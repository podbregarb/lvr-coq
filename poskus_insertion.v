Require Import List.
Require Import Bool.
Require Import ZArith.
Require Import sort.
Require Import Recdef.

(*Poskusmo definirat Insertion sort*)
Fixpoint vstavi(x:Z)(l:list Z):=
  match l with
    |nil=>(x::l)
    |(y::l')=>
       if Z.ltb y x then y::vstavi x l'(*Z.ltb pomeni strogo manjši*)
       else (x::y::l')
end.

Fixpoint insertion (l:list Z):=
  match l with
    | nil => nil
    | x::l' =>
      let l'' := insertion l' in
        vstavi x l''
end.



Eval compute in (insertion (3 :: 2 :: 1 :: 4 :: 8 :: 6 :: 7 :: 9 :: 5 :: nil)%Z).


Theorem insertion_deluje_1 : forall l : list Z, urejen (insertion l).
Admitted. (* To bo naredil Tomaž. *)

Theorem insertion_deluje_2 : forall l : list Z, enak l (insertion l).
Admitted. (* To bo naredil Andrej. *)






