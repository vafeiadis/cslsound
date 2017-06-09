Require Import HahnBase ZArith List Basic Lang.
Set Implicit Arguments.
Unset Strict Implicit.

(** * Assertions and the meaning of CSL judgments *)

(** ** Separation logic assertions

  We represent separation logic assertions as the Coq [assn] (i.e., a
  deep embedding). Here is the syntax of assertions: *)

Inductive assn : Set := 
    Aemp
  | Apure (b: bexp)
  | Aconj (p1: assn) (p2: assn)
  | Adisj (p1: assn) (p2: assn)
  | Astar (p1: assn) (p2: assn)
  | Awand (p1 p2: assn)
  | Anot (p : assn)
  | Apointsto (e1 e2: exp)
  | Aex (pp: nat -> assn).

(** Separating conjunction of a finite list of assertions is just a
  derived assertion. *)

Fixpoint Aistar ps := 
  match ps with
    | nil => Aemp
    | p :: ps => Astar p (Aistar ps)
  end.

(** The semantics of assertions is given by the following function
  indicating whether a state [ss] satisfies an assertion [p]. *)

Fixpoint sat ss p := 
  match p with
    | Aemp            => snd ss = (fun x => None) 
    | Apure b         => bdenot b (fst ss)
    | Aconj p q       => sat ss p /\ sat ss q
    | Adisj p q       => sat ss p \/ sat ss q
    | Astar p q       => exists h1 h2, sat (fst ss, h1) p /\ sat (fst ss, h2) q 
                          /\ hdef h1 h2 /\ hplus h1 h2 = snd ss
    | Awand p q       => forall h (SAT: sat (fst ss, h) p) (HD: hdef (snd ss) h),
                          sat (fst ss, hplus (snd ss) h) q
    | Apointsto e1 e2 => snd ss = upd (fun x => None) (edenot e1 (fst ss)) 
                                                (Some (edenot e2 (fst ss)))
    | Anot p          => not (sat ss p)
    | Aex pp          => exists v, sat ss (pp v)
  end.

(** We can derive the following unfolding lemma for iterated
  separating conjunction. *)

Lemma sat_istar_map_expand :
  forall r l ss f (IN: In r l) (DL: disjoint_list l),
    sat ss (Aistar (map f l))
    <-> exists h1 h2, sat (fst ss, h1) (f r)
      /\ sat (fst ss, h2) (Aistar (map f (removeAll Z.eq_dec l r)))
      /\ hdef h1 h2 /\ hplus h1 h2 = snd ss.
Proof.
  destruct ss as [s h]; ins.
  revert h; induction l; ins; des; clarify.
    by destruct Z.eq_dec; clarify; rewrite removeAll_notin.
  destruct Z.eq_dec; simpls; clarify.
  split; intros; des; clarify; eauto.
    eapply IHl in H0; eauto; desf; rewrite hdef_hplus2 in *; desf.
    by do 3 eexists; eauto; repeat eexists; eauto; 
       (* try apply hdef_hplus; *) auto using hplusAC.
  rewrite hdef_hplus2 in *; desf.
  do 3 eexists; eauto; repeat eexists.
    by eapply IHl; eauto; repeat eexists; eauto.
  eapply hdef_hplus2; eauto. 
  eauto using hplusAC.
Qed. 

(** ** Precision 

  We say that a assertion is precise if for any given heap, there is
  at most one subheap that satisfies the formula. (The formal
  definition below says that if there are two such subheaps, they must
  be equal.) *)

Definition precise p := 
  forall h1 h2 h1' h2' s
    (SAT: sat (s, h1) p)
    (SAT': sat (s, h1') p)
    (EQ: hplus h1 h2 = hplus h1' h2')
    (D : hdef h1 h2)
    (D': hdef h1' h2'),
    h1 = h1'.

Ltac inss := ins; desf; unnw; intuition; desf.

(** The empty assertion, emp, is precise. *)

Lemma precise_emp: precise Aemp.
Proof. by red; ins; extensionality x; rewrite SAT, SAT'. Qed. 

(** Star conjunction of precise assertions is precise. *)

Lemma precise_star p q: precise p -> precise q -> precise (Astar p q).
Proof.
  unfold precise; ins; desf.
  rewrite ?hdef_hplus, ?hplusA in *; des.
  assert (h4 = h0) by eauto. 
  clarify; f_equal; rewrite (hplusAC h2), (hplusAC h2') in EQ; eauto.
Qed. 

Lemma precise_istar:
  forall l (P: forall x (IN: In x l), precise x), precise (Aistar l).
Proof. by induction l; ins; auto using precise_emp, precise_star. Qed.

(** ** Auxiliary definitions for resource invariants *)

Definition assn_lift po := match po with None => Aemp | Some p => p end.

Definition envs G (l l' : list rname) := 
  (Aistar (map (fun x => assn_lift (G x)) (list_minus Z.eq_dec l l'))).

Lemma sat_envs_expand:
  forall r l l' (IN: In r l) (NIN: ~ In r l')
    (LD: disjoint_list l) J ss,
    sat ss (envs J l l') 
    <-> exists h1 h2, sat (fst ss, h1) (assn_lift (J r)) 
              /\ sat (fst ss, h2) (envs J (removeAll Z.eq_dec l r) l')
              /\ snd ss = hplus h1 h2 /\ hdef h1 h2.
Proof.
  unfold envs; ins.
  rewrite (sat_istar_map_expand (r := r)), removeAll_list_minus; 
    auto using disjoint_list_list_minus. 
    by intuition; simpls; desf; eauto 10.
  by apply In_list_minus.
Qed.

Lemma envs_app1 :
  forall x z (D: disjoint x z) J y, envs J (x ++ z) (y ++ z) = envs J x y.
Proof.
  by unfold envs; ins; rewrite list_minus_appr.
Qed.

Lemma envs_app2 :
  forall x z (D: disjoint z x) J y, envs J (z ++ x) (z ++ y) = envs J x y.
Proof.
  by unfold envs; ins; rewrite list_minus_appl.
Qed.

Lemma envs_removeAll_irr: 
  forall r l (NIN: ~ In r l) J l', envs J l (removeAll Z.eq_dec l' r) = envs J l l'.
Proof.
  by unfold envs; ins; rewrite list_minus_removeAll_irr.
Qed.

Lemma envs_removeAll2:
  forall r l' (IN: In r l') J l, 
    envs J (removeAll Z.eq_dec l r) (removeAll Z.eq_dec l' r) = envs J l l'.
Proof.
  unfold envs; ins; rewrite list_minus_removeAll2.
  f_equal; f_equal; revert l; induction l'; ins; desf. 
    by rewrite removeAll_list_minus, removeAllK.
  by rewrite IHl'. 
Qed.

Lemma envs_cons2_irr: 
  forall r l (NIN: ~ In r l) J l', envs J (r :: l) (r :: l') = envs J l l'.
Proof.
  by unfold envs; ins; desf; rewrite removeAll_irr.
Qed.

Lemma envs_upd_irr : forall J r v l l', 
  ~ In r l \/ In r l' -> envs (upd J r v) l l' = envs J l l'.
Proof.
  unfold envs; ins; f_equal; apply Eq_in_map; unfold upd; ins; desf;
  eapply In_list_minus in IN; intuition.
Qed.

(** ** Meaning of CSL judgments *)

(** First, we define configuration safety (cf. Definitions 3 and 4 in paper).
Intuitively, any configuration is safe for zero steps. For n + 1 steps, it better 
(i) satisfy the postcondition if it is a terminal configuration, (ii) not abort, 
(iii) access memory only inside its footprint, and 
(iv) after any step it does, re-establish the resource invariant and be safe for 
another n steps.  *)

Fixpoint safe (n : nat) (c: cmd) (s: stack) (h: heap) (gamma : rname -> option assn) (q: assn) := 
  match n with O => True
    | S n =>
(* Condition (i) *)
          << END: c = Cskip -> sat (s, h) q >>
(* Condition (ii) *)
       /\ << NAB: forall hF (D: hdef h hF) (ABORT: aborts c (s, hplus h hF)), False >>
(* Condition (iii) *)
       /\ << AOK: forall a (ACC: In a (accesses c s)), h a <> None >>
(* Condition (iv) *)
       /\ << SOK: forall hJ hF c' ss'
             (STEP: red c (s, hplus h (hplus hJ hF)) c' ss')
             (SAT: sat (s, hJ) (envs gamma (locked c') (locked c)))
             (D1: hdef h hJ)
             (D2: hdef h hF)
             (D3: hdef hJ hF),
             exists h' hJ',
                     snd ss' = hplus h' (hplus hJ' hF) 
                  /\ hdef h' hJ'
                  /\ hdef h' hF
                  /\ hdef hJ' hF
                  /\ sat (fst ss', hJ') (envs gamma (locked c) (locked c'))
                  /\ safe n c' (fst ss') h' gamma q >>
  end.

(** Now, the meaning of triples (cf. Definitions 2 and 5 in paper) *)

Definition CSL gamma p c q :=
  << U: user_cmd c >> /\ << SF: forall n s h, sat (s, h) p -> safe n c s h gamma q >>.

(** ** Free variables and substitutions *)

(** The free variables of an assertion [p] are given as a predicate
[fvA p]. *)

Fixpoint fvA p := 
  match p with
    | Aemp            => (fun v => False)
    | Apure B         => (fun v => In v (fvB B))
    | Apointsto e1 e2 => (fun v => In v (fvE e1 ++ fvE e2))
    | Anot P          => fvA P
    | Astar P Q
    | Awand P Q
    | Aconj P Q
    | Adisj P Q       => (fun v => fvA P v \/ fvA Q v)
    | Aex P           => (fun v => exists x, fvA (P x) v)
  end.

Definition fvAs gamma v := exists x : rname, fvA (assn_lift (gamma x)) v.

(** Substitution of an expression for a free variable in an assertion: *)

Fixpoint subA x e p := 
  match p with
    | Aemp            => Aemp
    | Apure B         => Apure (subB x e B)
    | Apointsto e1 e2 => Apointsto (subE x e e1) (subE x e e2)
    | Anot P          => Anot (subA x e P)
    | Astar P Q       => Astar (subA x e P) (subA x e Q)
    | Awand P Q       => Awand (subA x e P) (subA x e Q)
    | Aconj P Q       => Aconj (subA x e P) (subA x e Q)
    | Adisj P Q       => Adisj (subA x e P) (subA x e Q)
    | Aex PP          => Aex (fun n => subA x e (PP n))
  end.

Lemma fvA_istar :
  forall Ps v, fvA (Aistar Ps) v <-> (exists P, fvA P v /\ In P Ps).
Proof.
  induction Ps; ins; try rewrite IHPs; intuition; desf; eauto.
Qed.

Lemma subA_assign:
  forall x e p s h, sat (s,h) (subA x e p) <-> sat (upd s x (edenot e s), h) p.
Proof.
  induction p; ins; repeat first 
    [done | apply ex_iff; intro|apply all_iff; intro 
      | rewrite subE_assign | rewrite subB_assign
      | match goal with H: _ |- _ => rewrite H; clear H end].
Qed.

(** * Soundness proof *)

(** ** Basic properties of the semantics *)

(** 1. Assertions depend only on the values of their free variables. *)

Lemma prop1_A: forall p s s' (A: forall v (FV: fvA p v), s v = s' v) h,
  sat (s, h) p <-> sat (s', h) p.
Proof.
  ins; revert h; induction p; ins; repeat first 
    [done | apply ex_iff; intro|apply all_iff; intro 
      | rewrite (prop1_B A) 
      | match goal with H: _ |- _ => rewrite H; clear H end]; eauto.
  by rewrite (prop1_E (agrees_app1 A)), (prop1_E (agrees_app2 A)).
Qed.

Lemma prop1_As : 
  forall J s s' (A: forall v (FV: fvAs J v), s v = s' v) h l1 l2, 
    sat (s, h) (envs J l1 l2) <-> sat (s', h) (envs J l1 l2).
Proof.
  unfold envs; ins; apply prop1_A; ins.
  eapply A; eapply fvA_istar in FV; des; clarify.
  eapply in_map_iff in FV0; des; vauto.
Qed.

Corollary prop1_AsE :
  forall s h J l1 l2 s' 
    (SAT: sat (s, h) (envs J l1 l2)) 
    (A: forall v (FV: fvAs J v), s v = s' v),
  sat (s',h) (envs J l1 l2).
Proof.
  intros; eapply prop1_As, SAT; symmetry; eauto.
Qed. 

Corollary prop1_A2 : 
  forall x P (NIN: ~ fvA P x) s v h, sat (upd s x v, h) P <-> sat (s, h) P.
Proof. ins; apply prop1_A; unfold upd; ins; desf. Qed. 

Corollary prop1_As2 :
  forall x J (NIN: ~ fvAs J x) s v h l l', 
  sat (upd s x v, h) (envs J l l') <-> sat (s, h) (envs J l l').
Proof. ins; apply prop1_As; unfold upd; ins; desf. Qed. 

(** 2. Safety is monotone with respect to the step number (Proposition 3 in paper). *)

Lemma safe_mon :
  forall n C s h J Q (OK: safe n C s h J Q) m (LEQ: m <= n),
    safe m C s h J Q.
Proof.
  intros until m; revert C s n h OK; induction m; ins; unnw.
  destruct n; [exfalso; omega|apply le_S_n in LEQ].
  clarify; simpls; des; repeat split; ins. 
  exploit SOK; eauto; ins; des; eauto 10. 
Qed. 

(** 3. Safety depends only on the values of the free variables of the program, the
postcondition and the resource invariants (Proposition 4 in the paper). To establish
this property, we need the following auxiliary lemmas.
*)

Lemma agrees_upd : 
  forall A s s' y (EQs: s y = s' y) x x' (EQx: x = x') v v' (EQv: v = v'),
    upd (A:=A) s x v' y = upd s' x' v' y.
Proof. unfold upd; ins; desf. Qed.

Lemma red_agrees : 
  forall c ss c' ss' (STEP: red c ss c' ss') 
    X s (A: forall x, X x -> fst ss x = s x) 
        (S_FV: forall x, In x (fvC c) -> X x), 
    exists s' h', red c (s, snd ss) c' (s', h') 
      /\ (forall x, X x -> fst ss' x = s' x) /\ snd ss' = h'.
Proof.
  induction 1; ins; clarify; simpls; eauto using red;
  try (rewrite (prop1_B (s' := s)) in B; try by red; eauto using in_or_app);
  eauto 8 using red;
  try (by exploit IHSTEP; eauto; intro; des; clarify; eauto 8 using red, in_or_app).

  - do 3 eexists; [|split]; eauto using red.
    intros; rewrite (prop1_E (s' := s0)); try red; eauto.
    unfold upd; desf; auto.
  
  - rewrite (prop1_E (s' := s0)) in RD; try red; eauto.
    eauto 12 using red, prop1_E, agrees_upd.
  
  - do 3 eexists; [|split]; eauto using red.
    f_equal; [|f_equal]; eapply prop1_E; red; eauto using in_or_app.
  
  - do 3 eexists; [|split];
      eauto using red, agrees_upd, prop1_E.
    f_equal; f_equal; eapply prop1_E; red; eauto. 

  - do 3 eexists; [|split];
      eauto using red, prop1_E.
    f_equal; eapply prop1_E; red; eauto.
Qed.

Lemma aborts_agrees : 
  forall c ss (ABORT: aborts c ss) 
    s' (A: agrees (fvC c) (fst ss) s') h' (EQ: snd ss = h'),
    aborts c (s', h').
Proof.
  induction 1; ins; clarify; eauto using aborts; fold stack in *; fold heap in *;
  try erewrite prop1_E in *; eauto using aborts, agrees_tl, agrees_app1, agrees_app2.
  by rewrite (accesses_agrees (agrees_app1 A)), (writes_agrees (agrees_app2 A)) in *; vauto.
  by rewrite (accesses_agrees (agrees_app2 A)), (writes_agrees (agrees_app1 A)) in *; vauto.
Qed.

(** With these lemmas, we can show Proposition 4. *)

Lemma safe_agrees : 
  forall n C s h J Q (OK: safe n C s h J Q) s'
    (A: forall v, In v (fvC C) \/ fvA Q v \/ fvAs J v -> s v = s' v),
    safe n C s' h J Q.
Proof.
  induction n; inss.
  by apply -> prop1_A; eauto.
  by eapply NAB, aborts_agrees; eauto; red; symmetry; eauto.
  by eapply AOK; eauto; erewrite accesses_agrees; unfold agrees; eauto.

  exploit prop2; eauto; intro M; des; simpls; clarify. 
  exploit red_agrees; try apply STEP; [symmetry; eapply A, X|by left|].
  clear STEP; intros (s'0 & _ & STEP & A' & <-). 
  exploit SOK; eauto; [by eapply prop1_As, SAT; ins; eauto| ins; des]. 
  clarify; repeat eexists; eauto.
  by eapply prop1_As; try eassumption; eauto.
  eapply IHn; eauto; symmetry; eapply A'; des; auto.
Qed.


(* -------------------------------------------------------------------------- *)
(** ** Soundness of the proof rules *)
(* -------------------------------------------------------------------------- *)

(** We now show the soundness of each proof rule of CSL separately. *)

Definition disjoint A (X Y: A -> Prop) := forall x, X x -> Y x -> False.

Definition pred_of_list A (l: list A) (x: A) := In x l.

Coercion pred_of_list : list >-> Funclass.

Lemma disjoint_conv : 
  forall A (l1 l2 : list A), disjoint l1 l2 -> Basic.disjoint l1 l2.
Proof.  
  done.
Qed.

(** *** Skip *)

Lemma safe_skip :
  forall n s h J Q, sat (s,h) Q -> safe n Cskip s h J Q.
Proof.
  by induction n; inss; [inv ABORT |inv STEP].
Qed.
Hint Resolve safe_skip.

Theorem rule_skip J P : CSL J P Cskip P.
Proof. by split; auto. Qed.

(** *** Parallel composition *)

Lemma safe_par:
 forall n C1 s h1 J Q1 (OK1: safe n C1 s h1 J Q1)
   C2 h2 Q2 (OK2: safe n C2 s h2 J Q2)
   (WF: wf_cmd (Cpar C1 C2))
   (HD: hdef h1 h2)
   (FV1: disjoint (fvC C1) (wrC C2)) 
   (FV2: disjoint (fvA Q1) (wrC C2)) 
   (FV3: disjoint (fvAs J) (wrC C2))
   (FV4: disjoint (fvC C2) (wrC C1)) 
   (FV5: disjoint (fvA Q2) (wrC C1))
   (FV6: disjoint (fvAs J) (wrC C1)),
  safe n (Cpar C1 C2) s (hplus h1 h2) J (Astar Q1 Q2).
Proof.
  induction n; inss.
  {  (* No aborts *)
   
    rewrite hdef_hplus, hplusA in *; des; inv ABORT; eauto.
    by rewrite hplusAC in A; [eapply NAB, A|]; eauto.
    (* No races *)
    by destruct ND; eapply disjoint_conv; unfold disjoint, pred_of_list;
       intro y; destruct (HD y); intros; eauto using writes_accesses.
    by destruct ND; eapply disjoint_conv; unfold disjoint, pred_of_list;
       intro y; destruct (HD y); intros; eauto using writes_accesses.
  }
  { (* accesses *)
    by eapply in_app_iff in ACC; unfold hplus in *; desf; eauto.
  }
  { (* Step *)
  rewrite hdef_hplus, hplusA in *; des.
  inv STEP; simpls.
  - (* C1 does a step *)
    rewrite envs_app1 in *; auto.
    rewrite (hplusAC hF) in R; auto.
    exploit SOK0; eauto; intro M; des.
    rewrite hdef_hplus2 in *; des.
    exists (hplus h' h2), hJ'; repeat eexists; eauto. 
      by rewrite M, hplusA; f_equal; rewrite hplusAC; auto.
    destruct (prop2 R) as (B1 & B2 & B3).
    eapply IHn; repeat split; eauto using red_wf_cmd;
      try (by unfold disjoint, pred_of_list in *; ins; eauto 3).
    apply safe_agrees with s; [by eapply safe_mon, le_n_Sn|].
    by symmetry; apply B3; unfold disjoint in *; des; eauto.
  - (* C2 does a step *)
    rewrite envs_app2 in *; auto.
    rewrite (hplusAC (hplus hJ hF)) in R; auto.
    rewrite (hplusAC hF) in R; auto.
    exploit SOK; eauto; intro M; des.
    rewrite hdef_hplus2 in *; des.
    exists (hplus h1 h'), hJ'; repeat eexists; eauto. 
      rewrite (@hplusC h' h1); auto.
      by rewrite M, hplusA; f_equal; rewrite hplusAC; auto.
    destruct (prop2 R) as (B1 & B2 & B3).
    eapply IHn; repeat split; eauto using red_wf_cmd;
      try (by unfold disjoint, pred_of_list in *; ins; eauto 3).
    apply safe_agrees with s; [by eapply safe_mon, le_n_Sn|]. 
    by symmetry; apply B3; unfold disjoint in *; des; eauto. 
  - (* Par skip skip *)
    exists (hplus h1 h2), hJ; rewrite hplusA; repeat split; eauto.
    eapply safe_skip; repeat eexists; eauto.
  }
Qed.

Theorem rule_par J P1 P2 C1 C2 Q1 Q2 :
  CSL J P1 C1 Q1 -> CSL J P2 C2 Q2 ->
  disjoint (fvC C1) (wrC C2) -> disjoint (fvA Q1) (wrC C2) -> disjoint (fvAs J) (wrC C2) ->
  disjoint (fvC C2) (wrC C1) -> disjoint (fvA Q2) (wrC C1) -> disjoint (fvAs J) (wrC C1) ->
  CSL J (Astar P1 P2) (Cpar C1 C2) (Astar Q1 Q2).
Proof. 
  unfold CSL; inss; eapply safe_par; simpl; auto.
  rewrite !user_cmd_locked; simpls; auto.
Qed.

(** *** Resource declaration *)

Lemma safe_resource:
 forall n C s h J r R Q (OK: safe n C s h (upd J r (Some R)) Q) (WF: wf_cmd C)
   (DISJ: disjoint (fvA R) (wrC C)),
     (forall hR (NIN: ~ In r (locked C)) (HD: hdef h hR)
       (SAT_R: sat (s,hR) R),
       safe n (Cresource r C) s (hplus h hR) J (Astar Q R))
   /\ (In r (locked C) -> safe n (Cresource r C) s h J (Astar Q R)).
Proof.
  induction n; inss; 
    try rewrite hdef_hplus in *; desf;
    try (by inv ABORT; desf; try rewrite hplusA in A; eauto);
    try (inv STEP).

  by unfold hplus in *; desf; eauto.

  { (* normal step *)
  rewrite removeAll_irr in *; simpls. 
  rewrite hplusA in *.
  assert (B := prop2 R0); desf.
  destruct (In_dec Z.eq_dec r (locked c'0)).

  - rewrite <- (hplusA hR) in R0; simpls.
    exploit SOK; eauto.
      rewrite sat_envs_expand; eauto.
      simpl; repeat eexists; eauto .
      by unfold upd; desf.
      rewrite envs_upd_irr; try rewrite In_removeAll; tauto.
      eby eapply disjoint_locked, red_wf_cmd.
    ins; desf.
    exploit IHn; eauto using red_wf_cmd; ins; desf.
      by unfold disjoint, pred_of_list in *; ins; eauto.
    rewrite envs_upd_irr in *; vauto. 
    by repeat eexists; eauto; rewrite envs_removeAll_irr; auto.

  - rewrite (hplusAC hF) in R0; auto.      
    rewrite removeAll_irr in *; simpls. 
    exploit SOK; eauto; [by rewrite envs_upd_irr; vauto |intro M; desf].
    exploit IHn; eauto using red_wf_cmd; ins; desf.
      by unfold disjoint, pred_of_list in *; ins; eauto.
    rewrite envs_upd_irr in *; vauto. 
    rewrite hdef_hplus2 in *; desf.
    rewrite (hplusAC hF), <- (hplusA h') in M; auto.
    rewrite (prop1_A (s':=fst ss')) in SAT_R.
    repeat eexists; eauto. 
    by symmetry; apply B2; unfold disjoint in *; des; eauto.
  }
  { (* exit *)
    by repeat eexists; eauto; eapply safe_skip; simpl; eauto 8.
  }
  { (* normal step *)
    assert (B := prop2 R0); desf.
    simpls; rewrite envs_removeAll2 in SAT; auto.
    forward eapply SOK as X; eauto; [by rewrite envs_upd_irr; auto|desf].
    forward eapply IHn as Y; eauto using red_wf_cmd.
      by unfold disjoint, pred_of_list in *; ins; eauto.
    ins; desf.
    
    destruct (In_dec Z.eq_dec r (locked c'0)).
      rewrite envs_upd_irr in *; auto.
      rewrite envs_removeAll2; auto.
      by repeat eexists; eauto.
    
    rewrite envs_removeAll_irr; try rewrite In_removeAll; intuition.
    rewrite sat_envs_expand in X3; try edone; ins; desf.
    rewrite envs_upd_irr in *; try rewrite In_removeAll; intuition. 
    unfold upd in X3; desf; simpls.
    rewrite hdef_hplus, hdef_hplus2 in *; desf.
    rewrite !hplusA in *.
    rewrite <- hplusA in X.
    repeat eexists; eauto.
    eby eapply disjoint_locked.
  }
Qed.

Theorem rule_resource J P R r C Q:
  CSL (upd J r (Some R)) P C Q ->
  disjoint (fvA R) (wrC C) ->
  CSL J (Astar P R) (Cresource r C) (Astar Q R).
Proof.
  unfold CSL; inss.
  edestruct safe_resource as (X & _); eauto.
  by apply X; try rewrite user_cmd_locked.
Qed.

(** *** Frame rule *)

Lemma safe_frame:
 forall n C s h J Q 
   (OK: safe n C s h J Q) hR
   (HD: hdef h hR) R
   (DISJ: disjoint (fvA R) (wrC C))
   (SAT_R: sat (s,hR) R),
 safe n C s (hplus h hR) J (Astar Q R).
Proof.
  induction n; inss;
  rewrite ?hdef_hplus, ?hplusA in *; desf; eauto 7.
    by unfold hplus in *; desf; eauto.
  rewrite (hplusAC hF) in STEP; auto.
  edestruct SOK as (h' & ?); eauto; desf.
  rewrite hdef_hplus2 in *; des.
  exists (hplus h' hR), hJ'.
  rewrite hplusA, (hplusAC hF); repeat split; eauto.
  destruct (prop2 STEP) as (B1 & B2 & B3 & B4).
  eapply IHn; repeat split; eauto;
    try (by unfold disjoint, pred_of_list in *; ins; eauto).
  eapply prop1_A with s; eauto.
Qed.

Theorem rule_frame J P C Q R:
  CSL J P C Q -> disjoint (fvA R) (wrC C) ->
  CSL J (Astar P R) C (Astar Q R).
Proof.
  unfold CSL; inss; eauto using safe_frame.
Qed.

(** *** Conditional critical regions *)

Lemma safe_inwith:
  forall n C s h J Q r 
    (OK : safe n C s h J (Astar Q (assn_lift (J r))))
    (WF: wf_cmd (Cinwith r C)),
  safe n (Cinwith r C) s h J Q.
Proof.
  induction n; inss; 
    [by inv ABORT; eauto|inv STEP; ins].
  - exploit SOK; try eapply R; eauto.
      by rewrite envs_cons2_irr in SAT.
    ins; desf.
    repeat eexists; eauto using red_wf_cmd.
    by rewrite envs_cons2_irr.
  - destruct END as (hQ & hJ' & ?); desf.
    rewrite hdef_hplus in *; desf.
    exists hQ, hJ'; rewrite !hplusA; repeat split; eauto 8 using hdefU2, hplusU2.
Qed.

Theorem rule_with J P r B C Q:
  CSL J (Aconj (Astar P (assn_lift (J r))) (Apure B)) C (Astar Q (assn_lift (J r))) ->
  CSL J P (Cwith r B C) Q.
Proof.
  unfold CSL; inss; destruct n; inss; [by inv ABORT | ].
  inv STEP; ins; desf; rewrite (user_cmd_locked U) in *; simpls.
  rewrite hdef_hplus, hdef_hplus2 in *; desf.
  exists (hplus h h1), (fun _ => None); rewrite !hplusA; repeat split; auto.
  eapply safe_inwith; simpl; eauto 10. 
  rewrite (user_cmd_locked); auto. 
Qed.

(** *** Sequential composition *)

Lemma safe_seq :
  forall n C s h J Q (OK : safe n C s h J Q) C2 (U: user_cmd C2) R
    (NEXT: forall m s' h', m <= n -> sat (s', h') Q -> safe m C2 s' h' J R),
  safe n (Cseq C C2) s h J R.
Proof.
  induction n; inss; [by inv ABORT; eauto|].
  inv STEP; ins.
    by repeat eexists; eauto; rewrite (user_cmd_locked U) in *.
  exploit SOK; eauto; ins; desf; repeat eexists; eauto.
Qed.

Theorem rule_seq J P C1 Q C2 R :
  CSL J P C1 Q -> CSL J Q C2 R -> CSL J P (Cseq C1 C2) R.
Proof.
  unfold CSL; intuition; simpl; eauto using safe_seq.
Qed.


(** *** Conditionals (if-then-else) *)

Theorem rule_if J P B C1 C2 Q:
  CSL J (Aconj P (Apure B)) C1 Q ->
  CSL J (Aconj P (Apure (Bnot B))) C2 Q ->
  CSL J P (Cif B C1 C2) Q.
Proof.
  unfold CSL; inss; destruct n; inss.
  by inv ABORT.
  inv STEP; repeat eexists; simpls; eauto;
     try by rewrite user_cmd_locked in *.
  eapply SF; clarify.
Qed.

(** *** While *)

Lemma safe_while:
  forall J P B C (OK: CSL J (Aconj P (Apure B)) C P) s h (SAT_P: sat (s, h) P) n,
    safe n (Cwhile B C) s h J (Aconj P (Apure (Bnot B))).
Proof.
  intros; revert s h SAT_P; generalize (le_refl n); generalize n at -2 as m.
  induction n; destruct m; ins; [inv H|apply le_S_n in H]. 
  unnw; intuition; desf; [by inv ABORT|].
  inv STEP; repeat eexists; eauto; simpl.
  destruct m; ins; desf; unnw; intuition; desf; [by inv ABORT|].
  inv STEP0; repeat eexists; eauto; simpls.
  - by rewrite (user_cmd_locked (proj1 OK)) in *.
  - by eapply safe_seq; [eapply OK|by apply OK|]; simpls; eauto using le_trans.
  - by apply safe_skip; simpls; clarify.
(*  eapply rule_if, SAT_P; [eapply rule_seq|apply rule_skip]; eauto. *)
Qed.

Theorem rule_while J P B C :
  CSL J (Aconj P (Apure B)) C P ->
  CSL J P (Cwhile B C) (Aconj P (Apure (Bnot B))).
Proof.
  unfold CSL; inss; eapply safe_while; unfold CSL; eauto.
Qed.

(** *** Basic commands (Assign, Read, Write, Alloc, Free) *)

Theorem rule_assign J x E Q:
  ~ fvAs J x -> CSL J (subA x E Q) (Cassign x E) Q.
Proof.
  unfold CSL; inss; destruct n; inss;
  [by inv ABORT | inv STEP; ins; desf].
  rewrite subA_assign in *; eauto 10.
Qed.

Theorem rule_read J x E E' :
  ~ In x (fvE E) -> 
  ~ In x (fvE E') -> 
  ~ fvAs J x ->
  CSL J (Apointsto E E') (Cread x E) (Aconj (Apointsto E E') (Apure (Beq (Evar x) E'))).
Proof.
  unfold CSL; inss; destruct n; ins; unnw; intuition; desf.
    by inv ABORT; ins; unfold hplus, upd in *; desf.
    by unfold upd in *; desf.
  inv STEP.
  repeat eexists; eauto; eapply safe_skip; ins. 
  rewrite !prop1_E2; try done.
  clear STEP; unfold hplus, upd in *; desf; rewrite H2 in *; desf.
Qed.

Lemma hdef_upd : 
  forall h h' x v, h x <> None -> hdef h h' ->
  hdef (upd h x v) h'.
Proof.
  unfold hdef, upd; ins; desf; firstorder.
Qed.

Lemma hdef_upds : 
  forall h h' x v v', hdef (upd h x (Some v)) h' ->
  hdef (upd h x (Some v')) h'.
Proof.
  unfold hdef, upd; ins; specialize (H x0); desf; vauto.
Qed.


Theorem rule_write J E E0 E':
  CSL J (Apointsto E E0) (Cwrite E E') (Apointsto E E').
Proof.
  unfold CSL; inss; destruct n; inss. 
    by inv ABORT; ins; unfold hplus, upd in *; desf.
    by unfold upd in *; desf.
  inv STEP; clear STEP; ins; clarify. 
  eexists (upd (fun _ => None) (edenot E s0) (Some (edenot E' s0))), (fun _ => None).
  repeat split; eauto using hdefU, hdefU, hdef_upds.
    by extensionality x; unfold upd, hplus; simpl; desf.
  by eapply safe_skip.
Qed.

Theorem rule_alloc J x E:
  ~ In x (fvE E) -> 
  ~ fvAs J x ->
  CSL J (Aemp) (Calloc x E) (Apointsto (Evar x) E).
Proof.
  unfold CSL; inss; destruct n; inss.
  by inv ABORT.
  inv STEP; ins; clarify.
  eexists (upd (fun _ => None) v (Some (edenot E s0))), (fun _ => None).
  rewrite ?hplusU in *; repeat split; auto using hdefU. 
    by extensionality y; unfold upd, hplus; simpl; desf.
  by unfold hdef, upd; ins; desf; vauto. 
  by apply safe_skip; ins; rewrite prop1_E2; unfold upd; desf.
Qed.

Theorem rule_free J E E':
  CSL J (Apointsto E E') (Cdispose E) (Aemp).
Proof.
  unfold CSL; inss; destruct n; inss.
    by inv ABORT; ins; unfold hplus, upd in *; desf.
    by unfold upd in *; desf.
  inv STEP; clear STEP; ins; clarify.
  eexists (fun _ => None), (fun _ => None); repeat split; auto using hdefU.
    by destruct (D2 (edenot E s0));
       extensionality y; unfold upd, hplus in *; desf.
  by eapply safe_skip; ins.
Qed.

(** *** Simple structural rules (Conseq, Disj, Ex) *)

Notation "P '|=' Q" := (forall x, sat x P -> sat x Q)  (at level 100).

Lemma safe_conseq:
  forall n C s h J Q (OK: safe n C s h J Q) Q' (IMP: Q |= Q'),
  safe n C s h J Q'.
Proof.
  induction n; inss. 
  exploit SOK; eauto; ins; desf; repeat eexists; eauto.
Qed.

Theorem rule_conseq J P C Q P' Q':
  CSL J P C Q -> 
  (P' |= P) -> 
  (Q |= Q') -> 
  CSL J P' C Q'.
Proof.
  unfold CSL; inss; eauto using safe_conseq.
Qed.

Theorem rule_disj J P1 P2 C Q1 Q2:
  CSL J P1 C Q1 -> 
  CSL J P2 C Q2 ->
  CSL J (Adisj P1 P2) C (Adisj Q1 Q2).
Proof.
  unfold CSL; inss; eapply safe_conseq; eauto; vauto.
Qed.

Theorem rule_ex J P C Q:
  (forall x, CSL J (P x) C (Q x)) -> 
  CSL J (Aex P) C (Aex Q).
Proof.
  unfold CSL; inss; [by destruct (H 0)|].
  eapply safe_conseq; [eby apply H|]; vauto.
Qed.

(** *** Conjunction rule *)

Lemma safe_conj:
  forall n C s h J Q1 (OK1: safe n C s h J Q1)
     Q2 (OK2: safe n C s h J Q2)
        (PREC: forall r, precise (assn_lift (J r))),
  safe n C s h J (Aconj Q1 Q2).
Proof.
  induction n; inss.
  forward eapply SOK as X; eauto; forward eapply SOK0 as Y; eauto; ins; desf.
  assert (P: precise (envs J (locked C) (locked c'))). 
    by apply precise_istar; ins; eapply in_map_iff in IN; desf. 
  assert (hJ' = hJ'0) 
    by (rewrite hplusAC in *; rewrite X in *; auto; eapply P; eauto); subst. 
  assert (h' = h'0); subst; eauto 10.
  by rewrite X in *; eapply hplusKr; eauto.
Qed.

Theorem rule_conj J P1 P2 C Q1 Q2:
  CSL J P1 C Q1 -> 
  CSL J P2 C Q2 -> 
  (forall r, precise (assn_lift (J r))) ->
  CSL J (Aconj P1 P2) C (Aconj Q1 Q2).
Proof.
  unfold CSL; inss; eauto using safe_conj.
Qed.

