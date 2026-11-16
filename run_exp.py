#!/usr/bin/env python3
"""Run all experiments; write results/*.tsv"""
import subprocess, os, sys, itertools
from concurrent.futures import ThreadPoolExecutor
os.makedirs('results', exist_ok=True)
def run(cmd):
    out = subprocess.run(cmd, capture_output=True, text=True)
    if out.returncode not in (0,):
        return cmd, 'FAIL ' + out.stderr.strip() + out.stdout.strip()
    return cmd, out.stdout.strip()
jobs = []
# 1. list labeling: algorithms x workloads x sizes x seeds
for alg in ['pma', 'hi', 'seesaw']:
    for wl in ['random', 'front', 'seq']:
        for lg in range(12, 23, 2):
            seeds = [1] if alg == 'pma' and wl != 'random' else [1, 2, 3]
            for sd in seeds:
                jobs.append(('ll', ['./ll', alg, str(lg), wl, str(sd)]))
# 2. see-saw parameter sweep at lg=18, front and random
for a, b in [(4, 2), (8, 4), (16, 8), (32, 8), (64, 16)]:
    for wl in ['random', 'front']:
        for sd in [1, 2, 3]:
            jobs.append(('ss', ['./ll', 'seesaw', '18', wl, str(sd), str(a), str(b)]))
# 3. order maintenance: algorithms x workloads x sizes
for alg in ['ds87', 'bcdfz', 'twolevel']:
    for wl in ['random', 'front', 'seq']:
        for lg in range(12, 23, 2):
            jobs.append(('om', ['./om', alg, str(1 << lg), wl, '0', '1']))
for lg in range(10, 17, 1):
    jobs.append(('om', ['./om', 'naive', str(1 << lg), 'front', '62', '1']))
# 4. bcdfz threshold sweep, 32-bit tags, front inserts
for T in ['1.1', '1.2', '1.3', '1.4', '1.5', '1.6', '1.7']:
    for lg in range(10, 21, 1):
        jobs.append(('bcT', ['./om', 'bcdfz', str(1 << lg), 'front', T, '1', '32']))
results = {}
with ThreadPoolExecutor(max_workers=2) as ex:
    for (tag, cmd), (c, out) in zip(jobs, ex.map(lambda j: run(j[1]), jobs)):
        results.setdefault(tag, []).append(' '.join(cmd[1:]) + '\t' + out)
        print(tag, ' '.join(cmd[1:]), '->', out, flush=True)
for tag, lines in results.items():
    open(f'results/{tag}.tsv', 'w').write('\n'.join(lines) + '\n')
