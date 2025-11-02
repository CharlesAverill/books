Definition relation (X : Type) : Type := X -> X -> Prop.

Definition deterministic {X : Type} (R : relation X) : Prop :=
  forall x y1 y2, R x y1 -> R x y2 -> y1 = y2.

Definition sound {X : Type} (R1 R2 : relation X) : Prop :=
  forall x y, R2 x y -> R1 x y.

Definition complete {X : Type} (R1 R2 : relation X) : Prop :=
  forall x y, R1 x y -> R2 x y.

Definition equivalent {X : Type} (R1 R2 : relation X) : Prop :=
  sound R1 R2 /\ complete R1 R2.