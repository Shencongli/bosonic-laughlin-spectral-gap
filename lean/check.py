"""Build and audit the checked results; does not certify the gap target."""
from pathlib import Path
import argparse
import hashlib
import json
import re
import subprocess

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--packages', help='Optional Lake package overrides for offline sources')
args = parser.parse_args()
root = Path(__file__).resolve().parent
lake = ['lake'] + (['--packages=' + str(Path(args.packages).resolve())] if args.packages else [])
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
sources = sorted((root/'BosonicLaughlin').glob('*.lean'))
names = []
for source in sources:
    names += ['BosonicLaughlin.' + n for n in re.findall(
        r'^theorem\s+(\w+)', source.read_text(encoding='utf-8'), re.M)]
audit = (root/'Audit.lean').read_text(encoding='utf-8')
listed = re.findall(r'^#print axioms (\S+)', audit, re.M)
if sorted(names) != sorted(listed):
    raise SystemExit('Audit.lean must list every theorem exactly once.')

def run(command):
    result = subprocess.run(command, cwd=root, text=True, encoding='utf-8',
                            errors='replace', capture_output=True)
    if result.returncode:
        print(result.stdout)
        print(result.stderr)
        raise SystemExit(result.returncode)
    return result.stdout + result.stderr

version = run(lake + ['env', 'lean', '--version']).strip()
run(lake + ['build'])
output = run(lake + ['env', 'lean', 'Audit.lean'])
dependencies = {}
for name in names:
    match = re.search(re.escape("'"+name+"'") + r' depends on axioms:\s*\[([^\]]*)\]', output)
    if match:
        axioms = {x.strip() for x in match.group(1).split(',') if x.strip()}
    elif "'" + name + "' does not depend on any axioms" in output:
        axioms = set()
    else:
        raise SystemExit('Missing axiom report: ' + name)
    if axioms - allowed:
        raise SystemExit('Unapproved axiom dependency: ' + name + ': ' + str(axioms - allowed))
    dependencies[name] = sorted(axioms)

files = sources + [root/n for n in ['BosonicLaughlin.lean', 'Audit.lean',
    'lakefile.lean', 'lake-manifest.json', 'lean-toolchain', 'check.py']]
record = {
    'lean_version': version,
    'build_passed': True,
    'package_overrides_used': bool(args.packages),
    'checked_theorem_count': len(names),
    'main_uniform_gap_theorem_proved': False,
    'axiom_dependencies': dependencies,
    'sha256': {p.relative_to(root).as_posix(): hashlib.sha256(p.read_bytes()).hexdigest() for p in files},
}
(root/'verification-local.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
print(f'{len(names)} theorem declarations checked; permitted axioms only.')
print('The full bosonic Laughlin uniform-gap target remains unproved.')
