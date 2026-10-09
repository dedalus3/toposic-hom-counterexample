# Toposic Hom counterexample

Lean formalizations of two failures of fullness for relative étale-topos reconstruction:

1. Over **every finite field** `k`, a pinned relative self-equivalence of the small étale topos of `G_m/k` is outside the image of every endomorphism in the finite-type scheme localization at universal homeomorphisms.
2. For **every prime** `p`, the corresponding obstruction persists for `G_m/F_p` regarded as a scheme over `Spec Z`.

The underlying geometric morphism of each witness is the identity. The nontrivial data are in the structural comparison with the base topos. These are failures of fullness, including fullness on equivalences; they do not exhibit two nonisomorphic schemes with equivalent relative topoi.

## Start here

- [The two final theorems](EtaleCounterexample/Counterexamples.lean): `finiteField_counterexample` and `arithmetic_counterexample`.
- [Verification record](verification/CERTIFICATE.txt): toolchain, checks, and trust boundary.
- [Exact principal signatures and axioms](verification/recorded/final-theorems.log).
- [Detailed formalization report](REPORT.txt): constructions, proved bridges, and auxiliary results not claimed.
- [Provenance](PROVENANCE.txt): AI involvement and the repository maintainer's role.

The formal statements use actual schemes, small étale sheaf categories, geometric morphisms with left-exact inverse images and adjunctions, and actual Gabriel–Zisman localizations. The final relative-isomorphism quotient retains compatibility with the base comparison. The algebraic comparison respects identity, composition, and ordinary scheme-induced direct images. Its domain contains all localized endomorphisms, including arbitrary zigzags in the arithmetic case.

## Reproduce

The project pins **Lean 4.34.0** in `lean-toolchain` and mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435` in `lake-manifest.json`.

With that Lean toolchain available (for example through elan), from the repository root run:

```sh
python3 verify-source.py
lake exe cache get
sh verify.sh
```

The first command checks the recorded source snapshot. The second obtains the pinned mathlib dependencies/cache on a first setup and needs network access. The third runs:

```sh
lake build
lake env lean Audit.lean
lake env leanchecker -v EtaleCounterexample
```

`verify.sh` stops on failure. Its current-run logs go in `verification/`; the committed release evidence is preserved separately in `verification/recorded/`. Build and replay may take substantial time and memory. A clean checkout rebuilds the project; the recorded release build used an existing dependency cache and existing build artifacts, followed by a new kernel replay of the project declarations.

Both principal theorem axiom lists are:

```text
[propext, Classical.choice, Quot.sound]
```

Universe annotations appear in the full output. `leanchecker` replays serialized declarations with Lean's kernel against imported environments. It is not a second implementation of Lean, and the recorded run is not a `--fresh` replay of all mathlib dependencies. A successful log is evidence of a run; the source and reproduction commands are the checkable artifact. The certificate is an unsigned verification record, not an external endorsement.

## Scope of the formalization

The two counterexamples are unconditional Lean theorems. The implementation proves the specific comparison and descent statements they need. In particular, it constructs a single explicit nonintegral Frobenius twist, handles negative monomial exponents and characteristic two, proves roof independence, and establishes arithmetic point separation.

This repository does **not** claim formalization of the complete family of twists indexed by the profinite integers, the classification “algebraic if and only if integral,” the global scheme-perfection equivalence, or the historical identification and priority of a conjecture. See `REPORT.txt` for the precise boundaries. The main mathematical paper is being studied and revised separately and is not included in this repository.

## Attribution and review

The project initiator reports that the mathematical argument and Lean formalization were developed using **OpenAI GPT-6 Astra with Extra High reasoning**. AI assistance was also used for documentation and release preparation. The public repository is maintained by `dedalus3`; maintenance and publication do not assert sole human mathematical authorship. See `PROVENANCE.txt`.

Independent review is welcome, especially of the match between the formal definitions and the intended relative étale-topos reconstruction problem. No specialist endorsement or novelty claim is implied by the verification record.

## License status

No project-wide license has been selected for this initial review release. The pinned third-party dependencies are not vendored here and retain their respective licenses. Public availability should not be read as an additional license grant.
