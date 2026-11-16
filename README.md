# Order maintenance and list labeling: implementations and experiments

Companion code for the survey "The Order-Maintenance Problem and Online List
Labeling: A Survey with Implementations and Experiments" (L. M. S. Russo).

## Programs

* `om.c`: order maintenance on a doubly linked list (large label universes)
  * `naive`: midpoint labels, global relabel when a gap is exhausted
  * `ds87`: Dietz–Sleator list-range relabeling (smallest j with w(x,x_j) > j^2), labels in Z_M
  * `bcdfz`: Bender–Cole–Demaine–Farach-Colton–Zito tag-range relabeling with threshold T
  * `twolevel`: groups of <= G elements with local labels; groups labelled by `bcdfz` (O(1) amortized)
* `ll.c`: list labeling in an array of m = 2^k slots (linear regime)
  * `pma`: Itai–Konheim–Rodeh sparse table / packed-memory array
  * `hi`: randomized history-independent structure of Bender et al. (FOCS'22), simplified
  * `seesaw`: simplified See-Saw algorithm of Bender et al. (FOCS'24)

Both programs check their final output (labels increasing along the list,
array sorted) and print `ok 1` on success.

## Build and run

    gcc -O2 -o om om.c -lm
    gcc -O2 -o ll ll.c -lm
    ./om ALG N WORKLOAD [param] [seed] [bits]   # ALG: naive ds87 bcdfz twolevel; WORKLOAD: random front seq hot
    ./ll ALG LOGM WORKLOAD [seed] [p1] [p2]     # ALG: pma hi seesaw;  seesaw: p1=alpha p2=beta
    python3 run_exp.py                          # full experiment suite (about an hour on 2 cores)

`param` is the threshold T for `bcdfz`, the group size G for `twolevel`,
and the label bits for `naive`.  `results_log.txt` has the raw output of the
runs reported in the paper.  `figs.py` in the paper's repository turns it
into the PSTricks plots; it looks for this file at `../github/results_log.txt`
(or the path in the environment variable `OM_RESULTS`).

## Simplifications (see Section 8 of the paper)

* `hi` and `seesaw` support insertions only.
* `hi` omits the random-shift embedding and rebuilds globally when n drifts by eps*n0/4.
* `seesaw` uses fixed alpha and beta instead of Theta((log log n)^2), clamps skews so
  that no child exceeds density 0.8, and rebuilds the parent if a leaf overflows.

## Provenance

This code was written, and the experiments were run, by Claude (Anthropic),
a generative AI system, at the direction of the author.
