# cva

_Concurrent Valuation Algebras (CVAs) formalised in Isabelle/HOL_

@misc{evangelouoost2023trace,
      title={Trace models of concurrent valuation algebras},
      author={Nasos Evangelou-Oost and Callum Bannister and Larissa Meinicke and Ian J. Hayes},
      year={2023},
      eprint={2305.18017},
      archivePrefix={arXiv},
      primaryClass={cs.LO},
      url={<https://arxiv.org/abs/2305.18017}>
}

---

## Formalisation status

### Section 2 - Concurrent valuation algebras

#### Ordered valution algebras (OVAs): OVA.thy

- [x] Definition 1 (valid_gc)
- [x] Remark 2 (gprj_functorial)
- [x] Remark 3 (id_le_gprj, gle_eq_local_le, laxity)
- [x] Theorem 1 (prj_ext_adjunction, ext_functorial)
- [x] Corollary 1 (strongly_neutral_covariance, strongly_neutral_monoid)
- [x] Corollary 2 (galois_insertion, galois_closure_extensive, galois_closure_idempotent)
- [x] Corollary 3 (locally_complete_imp_complete)

#### Concurrent valution algebras (CVAs): CVA.thy

- [x] Proposition 1 (epsilon_le_delta, delta_seq_delta_eq_delta, epsilon_par_epsilon_eq_epsilon)
- [x] Proposition 2 (comparitor)
- [x] Proposition 3 (hoare_concurrency_rule)

## To-do

- Sections 3--6...

## Acknowledgements

Many, many thanks to Callum Bannister, Kait Lam, and Scott Heiner for their help with this project! :heart:
