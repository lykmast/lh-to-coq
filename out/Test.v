Inductive PNat:Set := Z : PNat | S: PNat -> PNat.
Ltac ple := simpl.
Ltac smt_trivial := simpl; first [ assumption | intuition discriminate | easy].
Ltac smt_app th := first [ rewrite th | ple; rewrite th | apply th | ple; apply th].
Ltac smt_solve th := solve [ now rewrite th | now ple; rewrite th | now apply th | now ple; apply th].
Fixpoint add ds_dvl n :=
  match ds_dvl as lq_anf7205759403792795553 with | Z  => n | S m => let lq_anf7205759403792795554 := add m n in S lq_anf7205759403792795554 end.

Theorem add_lid (ds_dvb: PNat): add ds_dvb Z = ds_dvb.
Proof.
induction ds_dvb as [| n add_lid ]. now smt_trivial. smt_solve add_lid.
Qed.