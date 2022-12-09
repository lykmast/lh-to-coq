

From Equations Require Import Equations.
Set Equations Transparent.
Import Peano Nat.
Require Import Lia.
Require Import ArithRing.

Require Import LibTactics.



Lemma minus_id : forall m,  (S m) - 1 = m. lia. Qed.
Lemma succ_plus : forall m,  S m = m + 1. lia. Qed.
Lemma plus_rewrite : forall m n,  m + S n = S m + n /\ m  + 0 = m. lia. Qed.
Lemma plus_minus : forall m n, m + n - n = m. lia. Qed.
Lemma gt_ge : forall m n, m > n -> m >= n + 1. lia. Qed.
Lemma ge_gt : forall m n, m >= n + 1 -> m > n.  lia. Qed.
Lemma gt_ge2 : forall m n, m > n -> m >=n. lia. Qed.
Lemma gt_ge_gt: forall m n p, m > n -> n >= p -> m > p. lia. Qed.
Lemma gt_gt_gt: forall m n p, m > n -> n > p -> m > p. lia. Qed.
Lemma ge_ge_ge: forall m n p, m >= n -> n >= p -> m >= p. lia. Qed.
Lemma gt_plus : forall m n p, m > n -> m + p > n + p. lia. Qed.

Ltac math_rewrites :=
  try rewrite plus_minus;
  try rewrite minus_id;
  try rewrite <- succ_plus.
Ltac other_math_rewrites :=
  try rewrite plus_minus;
  try rewrite minus_id;
  try rewrite succ_plus.
  
Ltac ple_old := simpl; math_rewrites.
Ltac smt_trivial_old := ple_old; solve [ assumption | ring_simplify; intuition | intuition | intuition discriminate | easy | lia | nia].
Tactic Notation "ple" ident(f) := repeat (math_rewrites; simp f).

Tactic Notation "smt_trivial" ident(f) := ple f; smt_trivial_old. (* first [ assumption | intuition discriminate | easy | lia | nia]. *)
Ltac smt_app th := first [ rewrite th | ple_old; rewrite th | apply th | ple_old; apply th | applys_eq th]; try smt_trivial_old.
Ltac smt_solve th := solve [ now rewrite th | now ple_old; rewrite th | now apply th | now ple_old; apply th].

(* Lemma trans_gt_ge:  *)
Ltac Zify.zify_post_hook ::=
  try rewrite succ_plus;
  try rewrite plus_minus.
Ltac termination_resolve := first [lia | left; lia | right; lia].

(* Equations ack (p: nat*nat) : nat by wf p (lexprod _ _ lt lt) :=

ack (0,n) => n + 1;
ack (S m,0) => ack ((m),1);
ack (S m,S n) => ack ((m), (ack (S m, (n)))).
Print ack. *)

Equations? ack (m n:nat) : nat by wf (m,n) (lexprod _ _ lt lt) :=
ack 0 n := S n;
ack m 0 := ack (m - 1) 1;
ack m n := ack (m - 1) (ack m (n-1)).
Proof. all: termination_resolve. Defined.

Theorem ack_gt_snd m n : ack m n > n.
Proof. revert m n. induction m as [| m' IHm].
- intro n. smt_trivial ack.
- induction n as [| n' IHn].
  + simp ack. pose (IHm 1). 
    (* rewrite minus_id. (* this makes lia unable to solve the goal. why? *) 
    *) lia.
  + simp ack. pose (IHm (ack (S m') n')) as H1.
  pose IHn as H2.
  applys_eq gt_ge_gt. (* this should be automatic *)
  smt_app H1. smt_app H2.
Qed.

Theorem ack_snd_plus_one m n : ack m (n+1) > ack m n.
Proof.
  revert m n. destruct m as [|m].
  + intro n. 
    (* why is the assertion needed *)
    assert (ack 0 n = n + 1) as ->; smt_trivial ack.
  + intro n. pose (ack_gt_snd m (ack (S m) n)) as H.
    smt_app H.
    (* everything after this should be trivial *)
    rewrite <- succ_plus. (* this should be automatic *) 
    ple ack.
    repeat rewrite minus_id. (* this should be automatic *)
    smt_trivial_old.
Qed.


Theorem ack_mon_snd m n p: n > p -> ack m n > ack m p.
Proof.
intro H.
induction H as [| n _ ack_mon_snd].
(* induction in H!!! 
   maybe try induction on (n - p). *)
+ smt_app (ack_snd_plus_one m p).
+ applys_eq gt_gt_gt.
  smt_app (ack_snd_plus_one m n).
  smt_app ack_mon_snd.
Qed.

Theorem ack_mon_eq_snd m n p: n>=p -> ack m n >= ack m p.
Proof.
  intros [|]. smt_trivial_old.
  applys_eq gt_ge2. (* this should be automatic *)
  smt_app ack_mon_snd.
Qed.

Theorem ack_plus_one_fst_snd  m n: ack (m+1) n >= ack m (n+1).
Proof.
  induction n as [| n ack_plus_one_fst_snd].
  + smt_trivial ack.
  + ple ack.
    pose (ack_mon_eq_snd m (ack (m+1) n) (ack m (S n))) as H1;
    applys_eq ge_ge_ge.
    - smt_app H1;
      smt_app ack_plus_one_fst_snd.
    - pose (ack_gt_snd m (S n)) as H2;
      pose (ack_mon_eq_snd m (ack m (S n)) (S n+1)) as H3;
      smt_app H3; smt_app H2.  
Qed.

Theorem ack_geq_sum m n: ack m n >= m + n + 1.
Proof.
  revert n. induction m as [| m ack_geq_sum].
  + intro n. smt_trivial ack. 
  + intro n. pose (ack_plus_one_fst_snd m n) as H1.
    applys_eq ge_ge_ge.
    smt_app H1.
    smt_app ack_geq_sum.
Qed.


Theorem ack_mon_fst m n p: m > p -> ack m n >= ack p n.
Proof.
  induction 1 as [| m _ ack_mon_fst].
  + applys_eq ge_ge_ge.
    smt_app (ack_plus_one_fst_snd p n).
    applys_eq gt_ge2.
    smt_app (ack_mon_snd p (n+1) n).
  + applys_eq ge_ge_ge.
    smt_app (ack_plus_one_fst_snd m n).
    applys_eq ge_ge_ge.
    applys_eq gt_ge2.
    smt_app (ack_mon_snd m (n+1) n).
    smt_app ack_mon_fst.
Qed.

Theorem ack_fst_plus_two m n: ack (m+2) n > ack m (2*n).
Proof.
  induction n as [| n ack_fst_plus_two].
  + applys_eq gt_gt_gt.
    smt_app (ack_gt_snd m (ack m 1));
    assert (m+2 = S (S m)) as ->; try lia.
    simp ack; simpl; simp ack; smt_trivial_old.
    smt_app (ack_mon_snd m 1 0).
  + applys_eq gt_ge_gt.
    smt_app (ack_mon_snd (m+1) (ack (m+2) n) (ack m (2*n))).
    assert (m+2 = S (S m)) as ->; try lia.
    simp ack; simpl; simp ack; smt_trivial_old.
    
    applys_eq ge_ge_ge.
    smt_app (ack_mon_eq_snd (m+1) (ack m (2*n)) (m+2*n + 1)).
    smt_app (ack_geq_sum m (2*n)).
   
    applys_eq ge_ge_ge.
    smt_app (ack_mon_eq_snd (m+1) (m + 2*n + 1) (2*n + 1)).
    smt_app (ack_plus_one_fst_snd m (2*n + 1)). smt_trivial ack.
Qed.
