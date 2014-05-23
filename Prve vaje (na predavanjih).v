Parameter A B C : Prop.

Theorem prvi_izrek: A/\B -> B/\A.

Proof.
  intro.
  split.
  - destruct H.
    assumption.
  - destruct H.
    assumption.
Qed.

Theorem drugi_izrek: A/\B -> B/\A.

Proof.
  tauto.
Qed.

Theorem vaja1: A-> (B->A).
Proof.
  intros.
  assumption.
Qed.

Theorem vaja3: A \/ A -> A.
Proof.
  intros G.
  destruct G.
  - assumption.
  - assumption.
Qed.

Theorem vaja3': A \/ A -> A.
Proof.
  intros [G1|G2]. (* kombiniran intro in destrut*)
  - assumption.
  - assumption.
Qed.

Theorem vaja3'': A \/ A -> A.
Proof.
  intros [?|?]. (* sam poimenuje hipoteze *)
  - assumption.
  - assumption.
Qed.

Theorem vaja4: (A \/ B -> C) -> (A -> C) /\ (B -> C).
Proof.
  intro.
  split.
  - intro.
    apply H.
    left.
    assumption.
  - intro.
    apply H.
    right.
    assumption.
Qed.

Theorem vaja5: (A -> C) /\ (B -> C) -> (A \/ B -> C).
Proof.
  intros [H1 H2] [G1|G2]. (* zdej razbijamo in zato ni | vmes, ta crta je samo za ali *)
  - apply H1.
    assumption.
  - apply H2.
    assumption.
Qed.

Theorem vaja8: ~(A \/ B) -> ~A /\ ~B.
Proof.
  intros.
  split.
  - intro.
    absurd (A \/ B).
    + assumption.
    + left.
      assumption.
 - intro.
    absurd (A \/ B).
    + assumption.
    + right.
      assumption.
Qed.

Theorem vaja7: A -> ~ ~ A.
Proof.
  intros H G. (* ne naredi sam 2x intro, treba prisilit :P *)
  apply G.
  assumption.
Qed.

Print vaja4.

Theorem vaja6: ~(A /\ ~A).
Proof.
  intros [H1 H2].
  absurd A.
  - assumption.
  - assumption.
Qed.
  
  

  
