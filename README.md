# cva

_Concurrent Valuation Algebras (CVAs) formalised in Isabelle/HOL_

@misc{evangelouoost2023trace,
      title={Trace models of concurrent valuation algebras},
      author={Naso Evangelou-Oost and Larissa Meinicke and Callum Bannister and Ian J. Hayes},
      year={2023},
      eprint={2305.18017},
      archivePrefix={arXiv},
      primaryClass={cs.LO},
      url={<https://arxiv.org/abs/2305.18017>}
}
(v3 on arXiv)

---

## Formalisation status

### Section 2 - Ordered valuation algebras

#### (Covariant) Grothendieck construction: Grothendieck.thy

- [x] Definition 1 (valid_gc)

#### Ordered valution algebras (OVAs): OVA.thy

- [x] Remark 2 (res_functorial_id, res_functorial_trans, stability)
- [x] Remark 3 (local_mono_eq_global)
- [x] Theorem 1 (res_ext_adjunction, ext_functorial_id, ext_functorial_trans)
- [x] Corollary 1 (strongly_neutral_covariance, strongly_neutral_monoid)
- [x] Corollary 2 (galois_insertion, galois_closure_extensive)
- [x] Corollary 3 (locally_complete_imp_complete)
- [x] Lemma 1 (local_mono_ext_comm_imp_assoc, local_mono_ext_comm_imp_mono)
- [x] Lemma 2 (local_weak_exchange_imp_weak_exchange)

### Section 3 - Concurrent valuation algebras

#### Concurrent valution algebras (CVAs): CVA.thy

- [x] Proposition 1 (epsilon_le_delta, delta_seq_delta_eq_delta, epsilon_par_epsilon_eq_epsilon)
- [x] Proposition 2 (comparitor)
- [x] Proposition 3 (hoare_concurrency_rule)

### Section 4 - Tuple systems

#### Tuple systems: Tuple.thy

- [x] Theorem 2 (rel_ova_valid, rel_ova_commutative, rel_ova_strongly_neutral, rel_ova_tuple_system)
- [x] Proposition 4 (rel_ext_preimage)
- [x] Proposition 5 (rel_comb_is_int_ext, rel_ova_is_complete, rel_comb_is_meet)
- [x] Lemma 3 (valid_lists, valid_ne_lists)

## To-do

- The assumptions of section 2.1 of the paper were weakened to rely on only a prealgebra with right-adjoints existing for its restriction maps instead of an OVA. We should update the formalisation to reflect this, and the 2.1 results can then be moved from OVA.thy to Prealgebra.thy .
- Sections 5, 6, 7 (trace models).
- Use infix syntax where appropriate; see [here!](https://isabelle.zulipchat.com/#narrow/stream/238552-Beginner-Questions/topic/local.20infix.20operator.20definition/near/377738757)
- Remove possible unnecessary assumptions from theorems/lemmas/etc. (e.g. `valid`/`valid_map`; see [Design principles](#design-principles)).
- Improve readability of proofs.
- Make names more consistent.
- Develop a custom simp set to facilitate automation.

## Design principles

- Mathematical structures (Functions, Posets, Prealgebras (poset-valued presheaves), and their maps, etc.) are implemented as record types.
- Each structure has a corresponding validity predicate (`valid` or `valid_map`) which is used to constrain the structure's parameters to ensure that the structure is well-defined. These predicate should be verified at the boundaries of the formalisation, i.e.
   1. As assumptions to theorems/lemmas/constructions/etc. (inputs)
   2. As conclusions of theorems/lemmas/constructions/etc. (outputs)
- In this way, all structures in the 'interior' of the formalisation can safely be assumed to be well-defined.
- A cleaner approach may be to use subtypes with `typedef`, but we got stuck with this: see the subdirectory [experiments/subtypes](experiments/subtypes) for details. If you can help with this please let us know!

## Setup

### Prerequisites

- [Isabelle2022](https://isabelle.in.tum.de/website-Isabelle2022/index.html)

### (Optional) Building an image and loading it in Isabelle/jEdit

```
isabelle build -v -b -d . CVA
isabelle jedit -d . -l CVA
```

## Acknowledgements

Many, many thanks to Brae Webb, Callum Bannister, Kait Lam, and Scott Heiner for their help with this project! :heart:
