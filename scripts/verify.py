"""Build the 127 proof modules and root aggregator, then audit the main theorems."""
import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parent.parent
PERMITTED = {'propext', 'Classical.choice', 'Quot.sound'}
REQUIRED = {
    'ChvatalErdos.main_quantitative',
    'ChvatalErdos.main_asymptotic',
    'ChvatalErdos.main_epsilon',
    'ChvatalErdos.main_linear_lower',
    'ChvatalErdos.main_pancyclic_construction',
    'ChvatalErdos.main_pancyclic_obstruction',
}

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--lake', default='lake', help='Lake executable, found in PATH by default')
    parser.add_argument('--lake-arg', action='append', default=[], help='Additional Lake options')
    parser.add_argument('--source-only', action='store_true', help='Check source integrity only; does not verify proofs')
    parser.add_argument('--skip-build', action='store_true', help='Audit an already completed local build')
    args = parser.parse_args()
    sources = sorted((ROOT / 'ChvatalErdos').glob('*.lean'))
    hashes = {p.relative_to(ROOT).as_posix(): digest(p) for p in sources}
    aggregator = ROOT / 'ChvatalErdos.lean'
    aggregator_hash = digest(aggregator) if aggregator.is_file() else None
    if not sources or not (ROOT / 'ChvatalErdos/Main.lean').is_file():
        raise RuntimeError('The local proof source tree is missing')
    if aggregator_hash is None:
        raise RuntimeError('The root library entry point is missing')
    for path in [*sources, aggregator]:
        if re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b|implemented_by|\[extern', path.read_text(encoding='utf-8-sig')):
            raise RuntimeError('Forbidden placeholder or bypass in ' + path.name)
    if args.source_only:
        archived = json.loads((ROOT / 'verification/verification-status.json').read_text())
        expected = {p['file']: p['sha256'] for p in archived['sources']}
        if hashes != expected:
            raise RuntimeError('Sources differ from the archived verified version')
        paper = ROOT / 'manuscript/paper.tex'
        if digest(paper) != archived['paper_sha256']:
            raise RuntimeError('The manuscript source differs from the archived version')
        print(f'SOURCE INTEGRITY PASSED: {len(sources)} original proof modules and the manuscript are unchanged. '
              'The additional root aggregator was scanned; no new Lean build was run.')
        return 0
    output_dir = ROOT / '.verification'
    output_dir.mkdir(exist_ok=True)
    status_path = output_dir / 'status.json'
    log_path = output_dir / 'verification.log'
    result = {'status': 'RUNNING', 'started_at_utc': datetime.now(timezone.utc).isoformat()}
    status_path.write_text(json.dumps(result, indent=2))
    lake = [args.lake, *args.lake_arg]
    try:
        with log_path.open('w', encoding='utf-8') as log:
            if not args.skip_build:
                targets = ['ChvatalErdos', *['ChvatalErdos.' + p.stem for p in sources]]
                build = subprocess.run([*lake, 'build', *targets], cwd=ROOT, stdout=log, stderr=subprocess.STDOUT)
                if build.returncode:
                    raise RuntimeError('Lake build failed; see .verification/verification.log')
            root_check = subprocess.run([*lake, 'env', 'lean', 'ChvatalErdos.lean'], cwd=ROOT,
                stdout=subprocess.PIPE, stderr=subprocess.STDOUT, encoding='utf-8', errors='replace')
            log.write(root_check.stdout)
            if root_check.returncode:
                raise RuntimeError('Lean rejected the root library entry point')
            check = subprocess.run([*lake, 'env', 'lean', 'ChvatalErdos/Main.lean'], cwd=ROOT,
                stdout=subprocess.PIPE, stderr=subprocess.STDOUT, encoding='utf-8', errors='replace')
            log.write(check.stdout)
            print(check.stdout, end='')
            if check.returncode:
                raise RuntimeError('Lean rejected the main entry point')
            if 'sorryAx' in check.stdout:
                raise RuntimeError('An unproved dependency was found')
            entries = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", check.stdout)
            audits = {name: {a.strip() for a in group.split(',') if a.strip()} for name, group in entries}
            if not REQUIRED <= audits.keys():
                raise RuntimeError('Some main theorem audit output is missing')
            observed = set()
            for name in REQUIRED:
                if not audits[name] <= PERMITTED:
                    raise RuntimeError('Unexpected dependency for ' + name)
                observed.update(audits[name])
            if any(digest(ROOT / name) != value for name, value in hashes.items()):
                raise RuntimeError('Proof sources changed during verification')
            if digest(aggregator) != aggregator_hash:
                raise RuntimeError('The root aggregator changed during verification')
        result.update(status='VERIFIED', proof_module_count=len(sources), root_aggregator_count=1,
            root_aggregator={'file': 'ChvatalErdos.lean', 'sha256': aggregator_hash},
            observed_axioms=sorted(observed),
            proved_main_theorems=sorted(REQUIRED), sources=hashes,
            build_mode='AUDIT_EXISTING_BUILD' if args.skip_build else 'LAKE_BUILD_ALL_LOCAL_MODULES',
            checked_at_utc=datetime.now(timezone.utc).isoformat())
        status_path.write_text(json.dumps(result, indent=2))
        print(f'VERIFIED: {len(sources)} proof modules plus one root aggregator; '
              'all required main theorem audits passed. Build mode: ' + result['build_mode'])
        return 0
    except Exception as exc:
        result.update(status='FAILED', error=str(exc))
        status_path.write_text(json.dumps(result, indent=2))
        print(str(exc), file=sys.stderr)
        return 1

if __name__ == '__main__':
    sys.exit(main())
