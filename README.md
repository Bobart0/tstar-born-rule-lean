# tstar-born-rule-lean
Machine-verified derivation of the general Born rule theorem (Lean 4 / Mathlib)

This repository contains a Lean 4 formalisation, checked against the Mathlib library, of the central theorem of the "descriptive route" towards the Born rule developed in the companion articles below. The theorem is established for an **arbitrary perspective and an arbitrary cell**, not merely for a fixed basis or a special case.

## What is verified, and what is not

Every step in [`theorem1_general.lean`](./theorem1_general.lean) is checked by the Lean kernel, **except** for a single explicitly declared axiom: Gleason's theorem (1957), which is not available in formalised form in any major proof library at the time of writing. Running

```lean
#print axioms theorem1_general
```

at the end of the file should list exactly four items: `propext`, `Classical.choice`, `Quot.sound` (Lean's own foundational axioms, present in every Lean proof without exception) and `gleason` (the single substantial import of this development). No result in this file depends on any other unverified assumption.

In particular, **Lemma 4** (`lemma4_noncontextual`), the derivation of non-contextuality from grain-coherence alone, depends on no axiom beyond Lean's own three foundational ones, not even Gleason's theorem. This is arguably the most novel single result in the companion articles, and it is fully machine-checked with no external dependency at all.

## How to verify this, with no local installation

1. Open [live.lean-lang.org](https://live.lean-lang.org/) in a browser.
2. Paste the entire contents of `theorem1_general.lean` into the editor.
3. Wait for elaboration to finish (Mathlib is preloaded server-side; the first `import Mathlib` may take a minute or two).
4. Confirm there is no red error marker anywhere in the file.
5. Append, on a new line at the end, `#print axioms theorem1_general` and confirm the output matches the four axioms listed above.

To check a single result in isolation (for instance Lemma 4 alone), run the same `#print axioms` command with that theorem's name instead.

No local install of Lean, Mathlib, or any dependency is required for this verification.

## Structure of the file

The file is organised in ten sections, in dependency order: perspectives and their basic plumbing lemmas; the four agentive axioms on an estimation rule; Lemma 4 (non-contextuality derived from grain coherence); perspectives built from an orthonormal basis, global or relative to a single cell; refining an arbitrary perspective (the construction that lifts every result below from a fixed basis to an arbitrary perspective); Lemma 5; Gleason's theorem as an explicit axiom; the pinning lemma and theorem; the frame function linking the estimation rule to Gleason's axiom; and Theorem 1 itself, in full generality.

## Companion articles

- Technical companion article (Gleason route, English): *[]*
- Companion philosophical article: *[]*

## Provenance and verification process

This formalisation was produced iteratively against the online Lean checker, each correction motivated by an error or warning message actually returned by the checker rather than by an a priori guess of Mathlib's naming conventions. A detailed account of this process, including every bug encountered and how it was diagnosed and fixed, is kept in the companion formalisation dossier referenced in the technical article above, rather than in this repository.

## License

This code is released under the [Apache 2.0](./LICENSE).

## Citation

If you refer to this work, please cite it as described in [`CITATION.cff`](./CITATION.cff).
