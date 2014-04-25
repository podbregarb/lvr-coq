(* Osnovne vaje iz logike 1. reda. *)

(* Uporabimo knižnico, ki ima taktiko omega. Ta zna delati z naravnimi števili,
   če nastopajo samo linearne funkcije. *)
Require Import Omega.

(* Tip naravnih števil je nat. Ima element 0, operacijo naslednik S in običjane
   aritmetične operacije. *)

Theorem vaja_1:
  forall n : nat, exists m : nat, n < m.
Proof. (* nat so naravna stevila *)
  intro.
  exists (S n). (* S n - naslednik od n: lahko bi napisali tudi n+1 *)
  omega.
  (* admit. - "jaja it's ok" - to lahko napišemo vedno kadar se nam česa ne da dokazovati, lahko se na to stvar vrnemo kasneje.. *)
Qed.

(* tu je n podan kot parameter - ni ga treba dodati (napisati intro.) *)
Theorem vaja_2 (n : nat): exists m : nat, n < m.
Proof.
  exists (1+n). (* tu je za program boljše če napišemo 1+n *)
  (* v naslednji vrstici lahko napišemo kar omega. ali auto. *)
  omega.
Qed.

Theorem vaja_4 (n m : nat): 2 * n + m + 1 = m + n + 1 + n.
Proof.
  omega. (* auto. ne dela, simpl. tut ne *)
Qed.

Theorem vaja_5 (n : nat): (exists m : nat, n = 2 * m) \/ (exists m : nat, n = 1 + 2 * m).
Proof.
  (* omega. tega ne zna :) *)
  induction n. (* zgenerira dva primera: osnovni in indukcijski korak *)
  - left.
    exists 0 ; auto. (* da nimamo bv dveh korakov, naredi v enem *) (* dela tudi reflexivity *)
  - destruct IHn. (* lahko tudi destruct IHn as [[k G]|[k' G']] - naredi vse do naslednjega destruct *)
    + right.
      destruct H as [k G].
      exists k.
      omega.
    + left.
      destruct H as [k G]. (* ce tu namesto k napišemo m, bo Coq sam spremenil drug m v m0; imamo dve lokalni spr. *)
      (* zdej bomo uporabili pravilo za eksistenčni operator *)
      exists (k+1).
      omega.
Qed.

Theorem vaja_6: forall n, exists m, n = 3 * m \/ n = 3 * m + 1 \/ n = 3 * m + 2.
Proof.
  induction n.
  - exists 0.
auto.
  -destruct IHn.
   destruct H.
   +exists x.
    omega.
   +destruct H.
    *exists x;omega.
    *exists(x+1);omega.
Qed.

(* Predpostavimo, da imamo množici A in B. *)
Parameter A B : Set. 

(* Predpostavimo, da imamo predikat P na A in  Q na B. *)
Parameter P : A -> Prop.
Parameter Q : B -> Prop.

Theorem vaja_7:
  forall y : B, (forall x : A , P x /\ Q y) -> (forall z : A, P z).
Proof.
  (* ta dokaz je Coq-u očiten z firstorder. *)
  intros y H z.
  apply H. (* tu Coq v hipotezo namesto x vstavi z *)
Qed.

(* Predpostavimo relacijo R med A in B. *)
Parameter R : A -> B -> Prop.

Theorem vaja_8:
  (exists x : A, forall y : B, R x y) -> (forall y : B, exists x : A, R x y).
Proof.
  intro H.
  intro k.
  destruct H.
  exists x.
  apply H.
Qed.

Theorem vaja_9:
  ~ (exists x : A, P x) <-> forall x : A, ~ P x.
Proof.
  (* naredimo na vajah *)
  (* namigi: to je ekvivalnca, dokazati jo je treba v obe smeri, uporabi split. *)
  split.
  -intro. 
   intro.
   intro.
   destruct H.
   exists x.
   assumption.
  -intros.
   intro.
   destruct H0.
   apply (H (x)).
   assumption.
  
   
Qed.

(* Zakon o izključeni tretji možnosti. 
   Tu smo ga samo definirali, nismo ga predpostavili! *)
Definition lem := forall P : Prop, P \/ ~ P.

(* Zakon o dvojni negaciji. *)
Definition dn := forall P : Prop, ~ ~ P -> P.

Lemma vaja_10: lem -> dn.
Proof.
  unfold dn, lem.
  intro H.
  intro.
  intro.
  destruct (H (P0)) as [H1|H2].
  -assumption.
  -destruct (H0).
   assumption.
   

Qed.

Lemma vaja_11: dn -> lem.
Proof.
  unfold dn, lem. (* poglededamo kaj sta definiciji dn in lem *)
  intros D Q. (* D je hipoteza da valja zakon o dvojni negaciji *)
  apply D.
  intro.
  absurd Q.
  - intro.
    (* H je implikacija: iz Q \/ ~Q sledi False *)
    apply H.
    left ; assumption.
  - apply D.
    intro.
    apply H.
    right ; assumption.
Qed.
  
Theorem vaja_12:
  (exists x : A, P x) -> ~ forall x : A, ~ P x.
Proof.
 intro.
 intro.
 destruct H.
 apply (H0 (x)).
 assumption.
 
Qed.

Theorem vaja_13:
  dn -> (~ forall x : A, ~ P x) -> exists x : A, P x.
Proof.
  intros D H.
  apply D.
  intro G.
  absurd (forall x:A, ~ P x).
  - assumption.
  - intros x K.
    absurd (exists z:A, P z).
    + assumption.
    + exists x.
      assumption.
Qed.
