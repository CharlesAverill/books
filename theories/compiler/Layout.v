From Books Require Import lang.Syntax.

Definition layout : Type := ident -> option N.

Definition layout_of_alist (l : list (ident * N)) : layout :=
  List.fold_left (fun a '(i, addr) => update ieqb a i (Some addr)) l (fun _ => None).