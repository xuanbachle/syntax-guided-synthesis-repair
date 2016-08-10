import sys
import os
import subprocess
from utils import cd
import logging
import json
from pprint import pprint
import tempfile
import shutil
from os.path import join
import time

logger = logging.getLogger(__name__)
#src/ distance.c oracle 1 2 3 --assert assert.json --verbose --initial-tests 1
#/home/dxble/workspace/repairtools/angelix/tests/distance

class Synthesizer:

    def __init__(self, config, extracted, angelic_forest_file):
        self.config = config
        self.extracted = extracted
        self.angelic_forest_file = angelic_forest_file

    def dump_angelic_forest(self, angelic_forest):
        '''
        Convert angelic forest to format more suitable for current synthesis engine
        '''
        def id(expr):
            return '{}-{}-{}-{}'.format(*expr)

        dumpable_angelic_forest = dict()
        for test, paths in angelic_forest.items():
            dumpable_paths = []
            for path in paths:
                dumpable_path = []

                for expr, values in path.items():
                    for instance, value in enumerate(values):
                        angelic, _, environment = value  # ignore original for now
                        context = []
                        for name, value in environment.items():
                            context.append({'name': name,
                                            'value': value})
                        dumpable_path.append({ 'context': context,
                                               'value': { 'name': 'angelic',
                                                          'value': angelic },
                                               'expression': id(expr),
                                               'instId': instance })
                dumpable_paths.append(dumpable_path)
            dumpable_angelic_forest[test] = dumpable_paths

        with open(self.angelic_forest_file, 'w') as file:
            json.dump(dumpable_angelic_forest, file, indent=2)

    def __call__(self, angelic_forest):

        if type(angelic_forest) == str:
            # angelic_forest is a file
            shutil.copyfile(angelic_forest, self.angelic_forest_file)
        else:
            # angelic_forest is a data structure
            self.dump_angelic_forest(angelic_forest)

        dirpath = tempfile.mkdtemp()
        patch_file = join(dirpath, 'patch')
        config_file = join(dirpath, 'config.json')

        for level in self.config['synthesis_levels']:

            logger.info('synthesizing patch with component level \'{}\''.format(level))

            config = {
                "encodingConfig": {
                    "componentsMultipleOccurrences": True,
                    # better if false, if not enough primitive components, synthesis can fail
                    "phantomComponents": True,
                    "repairBooleanConst": False,
                    "repairIntegerConst": False,
                    "level": "linear"
                },
                "simplification": self.config['synthesis_simplify'],
                "reuseStructure": not self.config['semfix'],
                "spaceReduction": self.config['space_reduction'],
                "componentLevel": level,
                "solverBound": 3,
                "solverTimeout": self.config['synthesis_timeout'],
            }

            with open(config_file, 'w') as file:
                json.dump(config, file)

            if self.config['synthesis_other_solver'] is None:
                jar = os.environ['SYNTHESIS_JAR']
            else:
                jar = os.environ['SYNTHESIS_OTHER_JAR']

            if self.config['verbose']:
                stderr = None
            else:
                stderr = subprocess.DEVNULL


            args = [self.angelic_forest_file, self.extracted, patch_file, config_file]
            if self.config['synthesis_other_solver'] is not None:
                solverName = self.config['synthesis_other_solver']
                args += [solverName]
                if solverName == "Enum":
                    args += [os.environ['ENUM_SOLVER_PATH']]
                elif solverName == "Symbolic":
                    args += [os.environ['SYMBOLIC_SOLVER_PATH']]
                elif solverName == "CVC4":
                    args += [os.environ['CVC4_SOLVER_PATH']]
                elif solverName == "Stoc":
                    args += [os.environ['STOC_SOLVER_PATH']]
                else:
                    raise NameError("Not supported solver: "+solverName)
                args += [os.environ["RESULT_BEAUTIFIER_PATH"]]

            logger.info(self.angelic_forest_file)
            logger.info(self.extracted)
            logger.info(patch_file)
            logger.info(config_file)
            try:
                start = time.time()
                result = subprocess.check_output(['java', '-jar', jar] + args, stderr=stderr)
                end = time.time()
                logger.info ("Synthesis time: {}".format(end - start))
            except subprocess.CalledProcessError:
                logger.warning("synthesis returned non-zero code")
                if self.config['term_when_syn_crashes']:
                    sys.exit()
                continue

            if str(result, 'UTF-8').strip() == 'TIMEOUT':
                logger.warning('timeout when synthesizing fix')
            elif str(result, 'UTF-8').strip() == 'FAIL':
                logger.info('synthesis failed')
            elif str(result, 'UTF-8').strip() == 'SUCCESS':
                with open(patch_file) as file:
                    content = file.readlines()
                patch = dict()
                while len(content) > 0:
                    line = content.pop(0)
                    if len(line) == 0:
                        continue
                    expr = tuple(map(int, line.strip().split('-')))
                    original = content.pop(0).strip()
                    fixed = content.pop(0).strip()
                    if self.config['semfix']:
                        logger.info('synthesized expression {}: {}'.format(expr, fixed))
                    else:
                        logger.info('fixing expression {}: {} ---> {}'.format(expr, original, fixed))
                    patch[expr] = fixed
                return patch
            else:
                raise Exception('result: ' + str(result, 'UTF-8'))

        shutil.rmtree(dirpath)

        return None
