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
The actual compressed exchange on the pair-spin and spectator space now has
a complete spectral decomposition in Lean, with eigenvalues
$\lambda_z=(-1)^z(Q)_z/(2Q)_z$ and projector ranks $3Q-2z+1$ for $0\le z\le Q$;
$(Q)_z$ denotes the falling factorial. The three-particle coefficient is now
connected to the actual normal-ordered three-body term in every finite
particle sector. The lift preserves positive quadratic forms and is proved
to send $|w\rangle\langle w'|$ to the corresponding creation-annihilation
product, with the manuscript's normalization. The full $H_Q^2$ identity is
connected to these lifted recoupling blocks, each proved positive and Hermitian.
The physical Hamiltonian kernel is now identified with the common kernel
of its normalized pair annihilators. Exact total-orbital-deficit blocks
and their matrices are connected to the original operator. In polynomial
coordinates, their common pair kernel is transported between flux Q and
orbital cap d whenever Q≥d, where d is the total orbital deficit. The
nonunitary coordinate change and its induced metric are explicit.
The certificate row class is also proved to annihilate the physical kernel.
The 8 October 2026 extension constructs complete occupation and highest-weight
coordinates for these physical blocks. It includes the sector normalization
$\sqrt{Q^d/N!}$, derives the verifier's spherical diagonal metric and
integer pair-annihilation matrices, and proves the exact Hamiltonian form
with coefficients $\kappa_p^2/E_{p,Q}$. The integer center-of-mass derivative
matrix is connected to the actual angular-momentum raising operator, and
its kernel represents the full physical highest-weight space. Multisets
are also put in bijection with sorted orbital tuples.
Lean now checks the 26 retained rational highest-weight frames: three
particles at degrees 0–8 and four particles at degrees 0–16. Complete
enumeration and matrix-entry checks identify their columns with bases of
the actual physical highest-weight spaces for Q≥d>0; the two degree-zero
blocks are handled separately for every Q. These are generally
nonorthogonal bases. The [build record](verification/lean_retained_frames_build.json)
and [AI semantic audit](verification/audit_reports/lean_retained_frames_audit.txt)
record the exact frame and coordinate checks.
The next extension proves the metric-aware Hamiltonian square and the
three-particle target form $\mathsf H G^{-1}\mathsf H-\mathsf H$ in the
actual physical coordinates. It also checks exact integer Gram witnesses
for the 26 exported planar comparison arrays and 26 Hamiltonian arrays,
their complete common kernels, and positive definiteness on the selected
principal-column complements. The two empty blocks are included.
These array results do not yet identify the full comparison with its
physical operator formula. That identification, the finite-sphere interval
certificates, two-spectator and coherent estimates, sphere transfer, and
Schur averaging remain to be formalized. The
[new build record](verification/lean_planar_certificates_build.json) and
[AI self-review](verification/audit_reports/lean_planar_certificates_audit.txt)
record the checked scope.
The spherical-row extension now derives the physical pair-annihilation
coordinate map, the four-body target's double-pair Gram form, and the
normal ordering of certificate rows in the three- and four-particle input
sectors. It proves the vacuum-functional pullbacks and exact coefficient
cancellations used term by term in the direct K3 and K4 construction.
The [spherical-row build record](verification/lean_sphere_rows_build.json)
and [AI self-review](verification/audit_reports/lean_sphere_rows_audit.txt)
record these operator identities. Full frozen-array assembly, normalized
many-particle descendants, Schur averaging, and interval verification
remain to be connected.
**The uniform spectral-gap theorem remains unproved in Lean.** The package
documents its remaining proof obligations and reproducible build. The v0.1
manuscript is unchanged.

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

The Lean proof uses mathlib's Hermitian-matrix spectral theorem
([pinned source](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/Analysis/Matrix/Spectrum.lean),
credited there to Alexander Bentkamp). The [Lean sources section](lean/README.md#sources)
also records the formalization's other dependencies and methodological sources.

Topics: `laughlin`, `bosonic`, `spectral-gap`, `fractional-quantum-hall`,
`mathematical-physics`.
