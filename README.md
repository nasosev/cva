# cva

_Concurrent Valuation Algebras (CVAs) formalised in Isabelle/HOL_

@misc{evangelouoost2023trace,
      title={Trace models of concurrent valuation algebras},
      author={Nasos Evangelou-Oost and Callum Bannister and Larissa Meinicke and Ian J. Hayes},
      year={2023},
      eprint={2305.18017},
      archivePrefix={arXiv},
      primaryClass={cs.LO},
      url={<https://arxiv.org/abs/2305.18017>
}

---

## Formalisation status

### Section 2 - Concurrent valuation algebras

#### (Covariant) Grothendieck construction: Grothendieck.thy

- [x] Definition 1 (valid_gc)

#### Ordered valution algebras (OVAs): OVA.thy

- [x] Remark 2 (gprj_functorial)
- [x] Remark 3 (id_le_gprj, local_mono_eq_global, laxity)
- [x] Theorem 1 (prj_ext_adjunction, ext_functorial)
- [x] Corollary 1 (strongly_neutral_covariance, strongly_neutral_monoid)
- [x] Corollary 2 (galois_insertion, galois_closure_extensive, galois_closure_idempotent)
- [x] Corollary 3 (locally_complete_imp_complete)

#### Concurrent valution algebras (CVAs): CVA.thy

- [x] Proposition 1 (epsilon_le_delta, delta_seq_delta_eq_delta, epsilon_par_epsilon_eq_epsilon)
- [x] Proposition 2 (comparitor)
- [x] Proposition 3 (hoare_concurrency_rule)

## To-do

- Sections 3-6...

## Design principles

- Mathematical structures (Functions, Posets, Presheaves, and their maps, etc.) are implemented as record types.
- Each structure has a corresponding validity predicate (`valid` or `valid_map`) which is used to constrain the structure's parameters to ensure that the structure is well-defined. These predicate should be verified at the boundaries of the formalisation, i.e.
   1. As assumptions to theorems/lemmas/constructions/etc. (inputs)
   2. As conclusions of theorems/lemmas/constructions/etc. (outputs)
- In this way, all structures in the 'interior' of the formalisation can safely be assumed to be well-defined.

## Notes

- Documentation is generated using ChatGPT and has not been proofread! :sweat_smile:

## Acknowledgements

Many, many thanks to Callum Bannister, Kait Lam, and Scott Heiner for their help with this project! :heart:
