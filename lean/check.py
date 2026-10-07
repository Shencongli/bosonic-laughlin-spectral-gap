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
        r'^(?:@\[[^\]\r\n]*\][ \t]*)*(?:theorem|lemma)\s+(\w+)',
        source.read_text(encoding='utf-8'), re.M)]
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
run(lake + ['env', 'lean', 'StatementChecks.lean'])
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

required = [
    'pairApply_idempotent', 'hamiltonian_hermitian', 'hamiltonian_isBosonic',
    'modeNumber_factorial_moment', 'modeOccupation_eq_annihilate_normSq',
    'coherent_pairOccupation_le_energy', 'coherent_occupation_bound',
    'coherent_occupation_pair_lift', 'coherent_annihilation_pair_lift',
    'pairAnnihilate_eq_annihilate_twice',
    'energy_eq_sum_v0PairAnnihilate_normSq',
    'projectionPairs_eq_pairAnnihilate_normSq', 'coherent_pairAnnihilation_bound',
    'hamiltonian_normal_order', 'normalFourBody_nonneg',
    'normalFourBody_eq_sum_v0PairAnnihilate_normSq',
    'normal_order_fock_quadratic_form', 'threeBodyMap_isBosonic',
    'threeBody_gram', 'threeBody_hamiltonian', 'threeBody_normal_coefficient',
    'recoupling_endpoint_coefficient',
    'threeBody_adjoint_inner', 'threeBodyDeficitOne_nonzero',
    'threeBodyDeficitOne_kernel', 'threeBodyDeficitOne_swap',
    'coherent_occupation_v0_sum_lift',
    'normalFourBody_eq_sum_v0PairAnnihilate_energy_all_sectors',
]
for name in required:
    if 'BosonicLaughlin.' + name not in dependencies:
        raise SystemExit('Missing required theorem: ' + name)

files = sources + [root/n for n in ['BosonicLaughlin.lean', 'Audit.lean',
    'StatementChecks.lean', 'lakefile.lean', 'lake-manifest.json', 'lean-toolchain', 'check.py']]
record = {
    'lean_version': version,
    'build_passed': True,
    'package_overrides_used': bool(args.packages),
    'checked_theorem_count': len(names),
    'main_uniform_gap_theorem_proved': False,
    'coherent_occupation_and_pair_lift_proved_sectorwise': True,
    'normal_order_and_four_body_fock_form_proved_sectorwise': True,
    'three_particle_gram_and_normal_coefficient_proved': True,
    'complete_three_body_recoupling_spectrum_proved': False,
    'three_body_coefficient_lift_to_arbitrary_particle_number_proved': False,
    'physical_statement_contracts_checked': True,
    'physical_statement_contract_count': len(re.findall(
        r'^example\b', (root/'StatementChecks.lean').read_text(encoding='utf-8'), re.M)),
    'required_theorems': required,
    'axiom_dependencies': dependencies,
    'sha256': {p.relative_to(root).as_posix(): hashlib.sha256(p.read_bytes()).hexdigest() for p in files},
}
(root/'verification-local.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
print(f'{len(names)} theorem declarations checked; permitted axioms only.')
print('The full bosonic Laughlin uniform-gap target remains unproved.')
