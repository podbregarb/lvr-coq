Require Import List.
Require Import Bool.
Require Import ZArith.
(*Require Import sort.
Require Import Recdef.*)

Local Open Scope list_scope.
Local Open Scope Z_scope.

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



(*Eval compute in (insertion (3 :: 2 :: 1 :: 4 :: 8 :: 6 :: 7 :: 9 :: 5 :: nil)%Z).*)

Fixpoint urejen (l : list Z) :=
  match l with
    | nil => True
    | _ :: nil => True
    | x :: ((y :: _) as l') => x <= y /\ urejen l'
  end.

(** Za permutacije potrebujemo funkcijo, ki prešteje, kolikokrat
    se dano število [k] pojavi v seznamu [l]. *)
Fixpoint pojavi (x : Z) (l : list Z) : nat :=
  match l with
    | nil => O
    | y :: l' =>
      if x =? y then S (pojavi x l') else pojavi x l'
  end.

(** Seznama [l1] in [l2] sta enaka, če imata isto število pojavitev
    za vsak [x]. *)
Definition permutiran (l1 l2 : list Z) :=
  forall x : Z, pojavi x l1 = pojavi x l2.

Lemma urejen_tail (x : Z) (l : list Z) :
  urejen (x :: l) -> urejen l.
Proof.
  induction l ; firstorder.
Qed.



(* Če vstavimo v urejen seznam, dobimo urejen seznam.*)
Lemma vstavi_urejen (x : Z) (l : list Z):
  urejen l -> urejen (vstavi x l).
Proof.
intro.
induction l.
- firstorder.
- simpl.
  case_eq (a <? x).
  * intro.
    simpl.
    destruct l.
    + simpl.
      SearchAbout (?a <? ?x).
      apply Z.ltb_lt in H0.
      SearchAbout(?a < ?x -> ?a <= ?x).
      firstorder.
    + simpl.
      case_eq(z<?x).
      proof.
        intro.
        replace (z::vstavi x l) with (vstavi x(z::l)).
        proof.
           firstorder.
        end proof.
        apply (urejen_tail) in H.
        simpl.
        replace(z<?x) with true.
        auto.
      end proof.
      intro.
      firstorder.
      proof.
        apply Z.ltb_lt in H0.
        firstorder.
      end proof.
      SearchAbout(?z<? ?x).
      apply Z.ltb_ge in H1.
      firstorder.
   *intro.
    firstorder. 
    apply Z.ltb_ge in H0.
    firstorder.
Qed.

 

Theorem insertion_deluje_1 : forall l : list Z, urejen (insertion l).
Proof.
intro.
induction l.
- firstorder.
- simpl.
  apply vstavi_urejen.
  auto.
Qed.

(* Hocemo dokazat   S(pojavi x l)=pojavi(vstavi x l) *)
Lemma enakost (x:Z) (l : list Z): 
S(pojavi x l)=pojavi x (vstavi x l).
Proof.
induction l.
-simpl.
 SearchAbout(?x=? ?x).
 rewrite Z.eqb_refl.
 auto.
-simpl.
 case_eq(x=?a).
 *intro.
  SearchAbout(?x =? ?a).
  apply Z.eqb_eq in H.
  rewrite H.
  SearchAbout (?a <? ?a).
  rewrite Z.ltb_irrefl.
  simpl.
  SearchAbout (?a =? ?a).
  rewrite Z.eqb_refl.
  auto.
 *intro.
  SearchAbout(?x =? ?a).
  apply Z.eqb_neq in H.
  case_eq(a<?x).
  +intro.
   SearchAbout (?a <? ?x).
   apply Z.ltb_lt in H0.
   simpl.
   SearchAbout (?x =? ?a).
   apply Z.eqb_neq in H.
   rewrite H.
   auto.
  +intro.
   simpl.
   rewrite Z.eqb_refl.
   apply Z.eqb_neq in H.
   rewrite H.
   auto.
Qed.

Lemma enakost2 (x:Z) (a:Z) (l : list Z): 
x<>a -> pojavi x l=pojavi x (vstavi a l).
Proof.
intro.
induction l.
-simpl.
 apply Z.eqb_neq in H.
 rewrite H.
 auto.
-simpl.
 case_eq(x=?a0).
 *intro. 
  case_eq(a0<?a).
  +intro.
   simpl.
   rewrite H0.
   f_equal.
   apply IHl.
  +intro.
   simpl.
   apply Z.eqb_neq in H.
   rewrite H.
   rewrite H0.
   auto.
 *intro.
  case_eq(a0<?a).
  +intro.
   simpl.
   rewrite H0.
   apply IHl.
  +intro.
   simpl.
   apply Z.eqb_neq in H.
   rewrite H.
   rewrite H0.
   auto.
Qed.

 


Theorem insertion_deluje_2 : forall l : list Z, permutiran l (insertion l).
Proof.
intro.
induction l.
-firstorder.
-simpl.
 intro.
 simpl.
 case_eq(x=?a).
 *intro.
  replace a with x.
  +unfold permutiran in IHl.
   rewrite (IHl x).
   apply enakost.
  +apply Z.eqb_eq in H.
   auto.
 *intro.
  rewrite (IHl x).
  apply enakost2.
  SearchAbout (?x =? ?a).
  apply Z.eqb_neq in H.
  auto.
Qed.
  
   
   
 







