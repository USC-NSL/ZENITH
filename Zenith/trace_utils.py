"""
Simple utility to work with traces generated with TLA+.
It accepts input files that contain TLA+ counterexamples. Right now,
it only works if they are clean (i.e. it is just the counterexample, 
and nothing more than that)
"""

import chardet
from typing import List, Tuple
from lark import Lark, Transformer, v_args, Discard

GRAMMAR = r"""
trace       : (step ("\n")+)+
step        : "State " INTEGER ": " action_name "\n" (conjunct)+
action_name : INITIAL_PREDICATE_NAME -> init
            | "<" CONNECTED_STRING " line " DONT_CARE_UNTIL_MORE_THAN_THEN_LINE_BREAK ">" -> transition1
            | "<" CONNECTED_STRING "(" DONT_CARE_UNTIL_CLOSE_PARENTHESES ")" " line " DONT_CARE_UNTIL_MORE_THAN_THEN_LINE_BREAK ">" -> transition2
conjunct    : CONJUNCT_LIST_ELEM var_name " = " var_value
var_name    : CONNECTED_STRING
var_value   : DONT_CARE_UNTIL_CONJUNCT_OR_DOUBLE_LINE_BREAK

CONNECTED_STRING: /[a-zA-Z0-9_!]+/
DONT_CARE_UNTIL_CLOSE_PARENTHESES: /.+?(?=\))/
DONT_CARE_UNTIL_MORE_THAN_THEN_LINE_BREAK: /.+?(?=(\>\n))/
DONT_CARE_UNTIL_CONJUNCT_OR_DOUBLE_LINE_BREAK: /(.|\s)+?(?=(\/\\|(\n\n)))/
INITIAL_PREDICATE_NAME: "<Initial predicate>"
INTEGER : /[0-9]+/
CONJUNCT_LIST_ELEM: "/\\ "
"""


class Step:
    INIT_ACTION = "Initial Assignment"

    def __init__(self, step_number: int, action_name: str, assignments: List[Tuple[str, str]]):
        self.step_number = step_number
        self.action_name = action_name
        self.is_init = action_name == Step.INIT_ACTION
        self.assignments = {variable: value.replace('\n', '') for (variable, value) in assignments}
    
    def __str__(self):
        return f"STEP {self.step_number} [[{self.action_name}]]\n\t" + \
            "\n\t".join([f"{key}: {value}" for key, value in self.assignments.items()])
    
    @property
    def without_pc(self):
        assignments = self.assignments.copy()
        assignments.pop('pc', None)
        return Step(self.step_number, self.action_name, assignments.items())


def get_step_diff(step: Step, previous_step: Step):
    assignments = step.assignments
    previous_assignments = previous_step.assignments

    return Step(
        step.step_number, step.action_name,
        [(k, v) for k, v in assignments.items() if v != previous_assignments[k]]
    )


class Trace:
    def __init__(self, steps: List[Step]):
        self.steps = steps
        
        # Get initial assignment
        init_step = steps[0]
        if init_step.is_init:
            self._variables = set(init_step.assignments.keys())
        else:
            self._variables = set()
    
    def __str__(self):
        return "\n\n".join(str(step) for step in self.steps)
    
    @property
    def variables(self):
        if len(self._variables) > 0:
            return self._variables
        raise ValueError("No initial state given. Cannot safely infer variables")

    @property
    def without_pc(self):
        return Trace([step.without_pc for step in self.steps])
    
    @property
    def without_init(self):
        if self.steps[0].is_init:
            return Trace(self.steps[1:])
        return self

    @property
    def diff(self):
        previous_step = self.steps[0]
        diffs = []
        for current_step in self.steps[1:]:
            diffs.append(get_step_diff(current_step, previous_step))
            previous_step = current_step
        
        return Trace([self.steps[0]] + diffs)
    
    def dump(self, path: str = "out.trace_out"):
        with open(path, 'w') as f:
            f.write(str(self))


class TreeToTrace(Transformer):
    @v_args(inline=True)
    def string(self, s):
        return s.replace('\\"', '"')

    @v_args(inline=True)
    def stripped_string(self, s):
        return s.replace('\\"', '"').strip()

    @v_args(inline=True)
    def number(self, n):
        return int(n)
    
    @v_args(inline=True)
    def transition1(self, action_name, description):
        return action_name
    
    @v_args(inline=True)
    def transition2(self, action_name, pid, description):
        return action_name
    
    def conjunct(self, s):
        assert len(s) == 2
        return (s[0], s[1])
    
    def step(self, items):
        assert isinstance(items[0], int)
        assert isinstance(items[1], str), str(items[1])
        assignments = [item for item in items[2:] if item != Discard]
        for item in assignments:
            assert isinstance(item, tuple), str(type(item))
            assert len(item) == 2
        return Step(items[0], items[1], assignments)
    
    trace = Trace
    var_name = string
    var_value = lambda self, s: s[0]
    init = lambda self, s: Step.INIT_ACTION
    INTEGER = number
    CONNECTED_STRING = string
    CONJUNCT_LIST_ELEM = lambda self, s: Discard
    DONT_CARE_UNTIL_CONJUNCT_OR_DOUBLE_LINE_BREAK = stripped_string
    DONT_CARE_UNTIL_MORE_THAN_THEN_LINE_BREAK = stripped_string


PARSER = Lark(GRAMMAR, parser='lalr', start='trace')
TRANSFORMER = TreeToTrace()


def load(path: str) -> Trace:
    # For windows, the encoding is often UTF-16-LE, so we should consider that
    det = chardet.universaldetector.UniversalDetector()
    with open(path, 'rb') as f:
        for line in f:
            det.feed(line)
            if det.done:
                break
    det.close()
    with open(path, 'r', encoding=det.result['encoding']) as f:
        trace_str = f.read() + "\n"
        ast = PARSER.parse(trace_str)
        return TRANSFORMER.transform(ast)
