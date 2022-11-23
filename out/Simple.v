Inductive day : Type :=
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.
  

Example test_next_weekday:
  tuesday = sunday.
Proof. simpl. reflexivity. Qed.
