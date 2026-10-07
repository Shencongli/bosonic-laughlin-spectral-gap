# The Bosonic Laughlin Spectral Gap: A Candidate Proof

*An AI-generated research note — v0.1, 7 October 2026*

**Prepared and curated by Xin Shen**

**AI-generated candidate proof.** AI agents developed the core argument,
verification programs, threshold optimization, and manuscript under Xin
Shen's direction and curation. The recorded arithmetic checks passed;
independent mathematical review of the argument and its implementation
remains open. See the [AI contribution and verification statement](AI_CONTRIBUTIONS.md)
for tools, model information, human contributions, and outstanding review.

## Model and proposed bound

This research note concerns the **bosonic Laughlin** parent Hamiltonian at
**nu=1/2**: the **V0 Haldane pseudopotential** projected to the complete
**lowest Landau level** on the **sphere**. The integer $Q=N_\phi$ is the
magnetic flux, the one-particle space $U_Q$ is the spin-$Q/2$
representation, and the $N$-boson space is $\operatorname{Sym}^N U_Q$.
The Hamiltonian is the sum over unordered pairs of orthogonal projectors
onto relative angular momentum zero (pair spin $Q$), each with coefficient
one, with no rescaling by $N$ or $Q$. Zero energy is the kernel energy.

The candidate **uniform spectral gap** estimate is

$$
H_Q^2 \ge \frac13 H_Q, \qquad Q\ge3088,
$$

in every particle sector, with the threshold independent of $N$.
At Laughlin flux $Q=2(N-1)$, this would give a gap of at least $1/3$
above the unique Laughlin zero mode for $N\ge1545$. The threshold is a
sufficient bound from the proposed certificate; it is not claimed optimal.
The manuscript also gives a planar limit with particle number and
polynomial degree fixed. Its finite-size and limit conventions are stated
in the paper.

## Manuscript and release

- [Read the PDF](paper.pdf)
- [Download the v0.1 PDF](https://github.com/Shencongli/bosonic-laughlin-spectral-gap/releases/download/v0.1/paper.pdf)
- [LaTeX source](paper.tex)
- [v0.1 release](https://github.com/Shencongli/bosonic-laughlin-spectral-gap/releases/tag/v0.1)
- [AI contribution and verification statement](AI_CONTRIBUTIONS.md)

## Build the manuscript

From the repository root, with a LaTeX distribution providing `pdflatex`, run:

```sh
pdflatex -interaction=nonstopmode -halt-on-error paper.tex
pdflatex -interaction=nonstopmode -halt-on-error paper.tex
```

The manuscript is a standalone `.tex` file using `geometry`, `amsmath`,
`amssymb`, `amsthm`, `mathtools`, `booktabs`, and `hyperref`. References are
included with `thebibliography`; no external `.bib`, figure, or data file
is needed to compile it. The verification files support the arithmetic
checks and are not LaTeX build dependencies.

## Replay the arithmetic checks

```sh
python -S verification/verify_optimized_threshold.py
```

Only the Python standard library is needed. Run without `-O`, which
disables assertions used by the verifier. The command replays the
arithmetic checks and writes result files and logs beside the scripts.
It checks 26 exact planar blocks, rational negative-tail estimates,
coherent-comparison scalar budgets, and 156 interval block certificates
covering six flux ranges whose union is $[3088,\infty)$.
The decision arithmetic uses integers, exact fractions, and
outward-rounded dyadic intervals.

The analytic identities connecting these checks to the full Hamiltonian
are supplied in the manuscript and remain open to independent review.
The [Lean formalization](lean/README.md) proves the full-model coherent
occupation bound $n_\beta\le H_Q+I$ and its lift through the normalized pair
annihilator, for every flux and particle number in finite-dimensional sectors.
It also proves the exact normal-order identity $H_Q^2=H_Q+S_3+S_4$,
identifies the positive four-body term with the double-pair-annihilator
square sum, and verifies the three-particle Gram and Hamiltonian identities.
The complete three-body recoupling spectrum remains to be formalized.
**The uniform spectral-gap
theorem remains unproved in Lean.** The package documents its remaining
proof obligations and reproducible build. The v0.1 manuscript is unchanged.

## Verification materials

- `verification/exact_shifted_certificate_rows.json`: frozen comparison rows.
- `verification/optimized_threshold_verification.json`: recorded full replay.
- `verification/optimized_joint_head_Q*_results.json`: interval matrices,
  rational frames, shifts, and pivot bounds.
- `verification/audit_reports/`: internal AI cross-checks. “Independent” in
  historical filenames means a separate internal calculation, not external
  human review.
- `verification/historical_checks/`: the earlier conservative estimates
  retained in Appendix A.
- `verification/manifest.json`: verification-file hashes and replay metadata.
- `SHA256SUMS`: hashes of the current repository files, excluding this checksum file.

## Sources and attribution

The manuscript's Introduction and references credit the foundational
Laughlin and pseudopotential literature, algebraic zero-mode methods,
and related rigorous gap results. Rougerie's
[*On the Laughlin function and its perturbations*](https://arxiv.org/abs/1906.11656)
discusses the spectral-gap conjecture in Appendix A.

The immediate methodological source is OpenAI's
[*A Fock-space inequality and the Laughlin spectral gap*](https://github.com/openai/math/blob/main/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf)
(24 September 2026). This note adapts its Fock-space comparison strategy
to the bosonic $V_0$ model and supplies bosonic coefficients and explicit
finite-flux certificates. The source preprint is cited as an AI-authored
work; it is not included in this repository.

Topics: `laughlin`, `bosonic`, `spectral-gap`, `fractional-quantum-hall`,
`mathematical-physics`.
