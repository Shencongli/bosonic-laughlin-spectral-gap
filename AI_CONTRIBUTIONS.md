# AI contribution and verification statement

**Prepared and curated by Xin Shen**  
**AI-generated candidate proof — v0.1, 7 October 2026**

## Generation and contributions

This note was developed in OpenAI Codex on 7 October 2026. The assistant
was identified in the session as belonging to the GPT-6 family. The exact
deployed model identifier and any distinct sub-agent model identifiers
were not recorded in the publication materials and are not asserted here.
The workflow used AI agents, local Python computations, and LaTeX
compilation. The released verifier uses the Python standard library;
its decisions use exact fractions and outward-rounded integer intervals.

AI agents contributed to the core proof development: adapting the
Fock-space strategy, deriving the bosonic operator and comparison bounds,
constructing the finite certificates, writing the verification programs,
optimizing the stated threshold, and drafting and editing the manuscript.
AI agents also performed the internal mathematical and computational
cross-checks recorded in this repository. AI involvement was not limited
to language editing or routine computation.

Xin Shen supplied the research question and source paper, directed the
bosonic extension and subsequent checks and threshold optimization,
set the editorial and disclosure requirements, curated the output, and
authorized this candidate-proof release. No separate line-by-line human
verification of the proof is recorded or claimed in v0.1.

## Methodological source

The immediate source is OpenAI,
[*A Fock-space inequality and the Laughlin spectral gap*](https://github.com/openai/math/blob/main/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf),
dated 24 September 2026. Its full-Fock-space comparison strategy is
adapted here to a different particle statistics and pseudopotential.
The Introduction and in-text citations identify this dependence and
credit the relevant human-authored literature. The present note does
not report an independent audit of every claim in that source preprint.

## Recorded checks

The complete arithmetic replay passed in the preparation workflow:

1. Exact planar positivity and kernel checks in all 26 retained blocks.
2. Rational negative-tail bounds and the scalar coherent-comparison budgets.
3. The 26 retained blocks in each of six flux ranges, totaling 156
   interval block certificates, with exact combination of the final budgets.

The ranges are $[3088,3090]$, $[3090,3100]$, $[3100,3125]$,
$[3125,3300]$, $[3300,4000]$, and $[4000,\infty)$.
The scripts and recorded outputs are supplied for reproduction. Their
success flags certify the implemented arithmetic checks. The driver
does not automatically verify all analytic operator identities in the
manuscript or compare every release file against its manifest.

Internal AI cross-checks examined the finite kernels, four-body coherent
comparison, sphere transfer, and interval implementation. Records whose
filenames contain “independent” describe separately constructed checks
within this AI workflow, not external human peer review.

## Steps awaiting independent review

The candidate conclusion depends on the correspondence between the
physical Hamiltonian, the analytic reductions, and the coded matrices.
Independent review is still needed for the normalization and normal
ordering; the recoupling identities and common-kernel identification;
the finite-sphere transfer and Schur averages; the coherent comparison
inequalities and positive many-body lifting; and the correspondence
between those formulas and all inputs to the interval verifier.

The arithmetic replay is not a proof-assistant formalization. No external
peer review or independent human validation is recorded for v0.1. The
publication status is therefore **candidate proof**, with the proposed
bound and its assumptions stated in the manuscript. The threshold
$Q_0=3088$ is not claimed to be the smallest possible sufficient threshold.
