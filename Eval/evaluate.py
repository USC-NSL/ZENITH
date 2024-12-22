import os
import sys
import shutil
import argparse
import platform
from typing import List

# We'll address everything relative to the directory of this script
THIS_DIR = os.path.dirname(os.path.realpath(__file__))

# Here are the directory for all the modules that we'll need
LIBS = [
    "Include",    # Evaluation constants, DAG definition, constants for switch/controller
    "Switch"      # The actual switch specification
]

# These are the commands we invoke ...
TLC_CMD = "java {java_opts} -XX:+UseParallelGC -cp {jar} tlc2.TLC {module} -workers auto -noGenerateSpecTE -cleanup -config {config}"
SANY_CMD = "java {java_opts} -cp {jar} tla2sany.SANY {module}"
PCAL_TRANS_CMD = "java {java_opts} -cp {jar} pcal.trans -nocfg -unixEOL {module}"


def get_cmd(args, java_opts) -> List[str]:
    action = args.action
    module_name = os.path.abspath(args.module)

    os_name = platform.system()
    jar = '%TLA_HOME%' if os_name == 'Windows' else '$TLA_HOME'
    
    if action == ACTIONS.CHECK:
        config = args.config
        if config is None:
            config_path = module_name.replace(".tla", ".cfg")
            assert os.path.exists(config_path), "Could not find default config for this spec, and no config file was provided"
            print(f"Using inferred config file at {config_path}")
            config = config_path
        assert config is not None, f"For checking the spec, a TLC configuration MUST be provided."
        if args.diff:
            return [TLC_CMD.format(module=module_name, java_opts=java_opts, jar=jar, config=os.path.abspath(config)) + ' -difftrace']
        else:
            return [TLC_CMD.format(module=module_name, java_opts=java_opts, jar=jar, config=os.path.abspath(config))]
    elif action == ACTIONS.PARSE:
        return [SANY_CMD.format(module=module_name, java_opts=java_opts, jar=jar)]
    elif action == ACTIONS.TRANSLATE:
        return [PCAL_TRANS_CMD.format(module=module_name, java_opts=java_opts, jar=jar)]
    elif action == ACTIONS.BUILD:
        return [
            PCAL_TRANS_CMD.format(module=module_name, java_opts=java_opts, jar=jar),
            SANY_CMD.format(module=module_name, java_opts=java_opts, jar=jar)
        ]

    raise ValueError(f"Unknown action \'{action}\'")


def get_libs(module_path, other_dirs: List[str]):
    os_name = platform.system()
    libraries = [
        os.path.join(THIS_DIR, lib) for lib in LIBS
    ] + [
        os.path.dirname(os.path.abspath(module_path))
    ] + [
        os.path.abspath(_dir) for _dir in other_dirs
    ]

    paths = [f'\"{lib}\"' for lib in libraries]

    if os_name == 'Windows':
        return f"-DTLA-Library={';'.join(paths)}"
    return f"-DTLA-Library={':'.join(paths)}"


def delete_states(module_path):
    module_dir = os.path.dirname(module_path)
    states_dir = os.path.join(module_dir, 'states')
    if os.path.exists(states_dir):
        shutil.rmtree(states_dir)


class ACTIONS:
    TRANSLATE = 'translate'  # Convert PlusCal to TLA+
    PARSE = 'parse'          # Run SANY and check the form of the spec
    BUILD = 'build'          # Combination of translation and parsing
    CHECK = 'check'          # Run TLC on the spec with a given configuration file


if __name__ == '__main__':
    parser = argparse.ArgumentParser('Run TLC on a specification')
    parser.add_argument('module', 
                        help="Path the TLA+ module to evaluate.")
    parser.add_argument('--action', choices=[ACTIONS.TRANSLATE, ACTIONS.PARSE, ACTIONS.BUILD, ACTIONS.CHECK], 
                        help="Do what?", default=ACTIONS.BUILD)
    parser.add_argument('--libs', nargs='+', type=str, 
                        help="List of library directories.")
    parser.add_argument('--config', 
                        help="Path to the TLC configuration file.")
    parser.add_argument('--cleanup', action='store_true',
                        help="Delete the `states` directory if it exists in the directory of the module")
    parser.add_argument('--diff', action='store_true',
                        help="Show only the DIFF between states when printing the trace")
    args = parser.parse_args()

    if not os.getenv('TLA_HOME'):
        print("No TLA_HOME environment variable set. Please set it to point to the TLA+ JAR file.")
        sys.exit(-1)

    opts = get_libs(args.module, args.libs if args.libs else [])
    cmds = get_cmd(args, opts)

    if args.cleanup:
        delete_states(args.module)

    for cmd in cmds:
        os.system(cmd)
