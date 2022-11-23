Inductive PNat:Set := Z : PNat | S: PNat -> PNat.
Ltac ple := simpl.
Ltac smt_trivial := try intuition discriminate.
Ltac smt_app th := first [ rewrite th | ple; rewrite th ].
Fixpoint add ds_dvl n :=
  match ds_dvl as lq_anf7205759403792795553 with | Z  => n | S m => let lq_anf7205759403792795554 := add m n in S lq_anf7205759403792795554 end.

Theorem add_lid (ds_dvb: PNat): add ds_dvb Z = ds_dvb.
Proof.
induction ds_dvb as [| n add_lid ]. smt_app add_lid. smt_trivial.
Qed.

