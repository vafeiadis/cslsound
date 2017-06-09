Require Import HahnBase ZArith List Basic Lang CSLsound.
Require Import Classical.

Set Implicit Arguments.
Unset Strict Implicit.

(** * RGSep assertions

  We represent separation logic assertions as the Coq [assn] (i.e., a
  deep embedding). Here is the syntax of assertions: *)

Inductive rgsep_assn := 
    RGlocal (p : assn)
  | RGshared (r: rname) (p : assn)
  | RGconj (p q : rgsep_assn)
  | RGdisj (p q : rgsep_assn)
  | RGstar (p q : rgsep_assn)
  | RGex (A: Type) (pp: A -> rgsep_assn).

(** Separating conjunction of a finite list of assertions is just a
  derived assertion. *)

Fixpoint RGistar ps := 
  match ps with
    | nil => RGlocal Aemp
    | p :: ps => RGstar p (RGistar ps)
  end.

(** The semantics of assertions is given by the following function
  indicating whether a state [ss] satisfies an assertion [p]. *)

Fixpoint RGsat ss p := 
  match p with
    | RGlocal p      => sat (fst ss) p
    | RGshared r p   => (forall x, snd (fst ss) x = None) /\ sat (fst (fst ss), snd ss r) p
    | RGconj p q     => RGsat ss p /\ RGsat ss q
    | RGdisj p q     => RGsat ss p \/ RGsat ss q
    | RGstar p q     => exists h1 h2, RGsat (fst (fst ss), h1, snd ss) p
                          /\ RGsat (fst (fst ss), h2, snd ss) q 
                          /\ hdef h1 h2 /\ hplus h1 h2 = snd (fst ss)
    | RGex pp        => exists v, RGsat ss (pp v)
  end.

(** We can derive the following unfolding lemma for iterated
  separating conjunction. *)

Lemma sat_istar_map_expand :
  forall r l ss f (IN: In r l) (DL: disjoint_list l),
    RGsat ss (RGistar (map f l))
    <-> exists h1 h2, RGsat (fst (fst ss), h1, snd ss) (f r)
      /\ RGsat (fst (fst ss), h2, snd ss) (RGistar (map f (removeAll Z.eq_dec l r)))
      /\ hdef h1 h2 /\ hplus h1 h2 = snd (fst ss).
Proof.
  destruct ss as [[s h] ss]; ins.
  revert h; induction l; ins; des; clarify.
    by destruct Z.eq_dec; clarify; rewrite removeAll_notin.
  destruct Z.eq_dec; simpls; clarify.
  split; intros; des; clarify; eauto.
    eapply IHl in H0; eauto; desf; rewrite hdef_hplus2 in *; desf.
    by do 3 eexists; eauto; repeat eexists; eauto; 
       (* try apply hdef_hplus; *) auto using hdefC, hplusAC.
  rewrite hdef_hplus2 in *; desf.
  do 3 eexists; eauto; repeat eexists.
    by eapply IHl; eauto; repeat eexists; eauto.
  eapply hdef_hplus2; eauto.
  eauto using hplusAC.
Qed. 

(** ** Meaning of RGSep judgments *)

(** First, we define configuration safety (cf. Definitions 3 and 4 in paper).
Intuitively, any configuration is safe for zero steps. For n + 1 steps, it better 
(i) satisfy the postcondition if it is a terminal configuration, (ii) not abort, 
(iii) access memory only inside its footprint, and 
(iv) after any step it does, re-establish the resource invariant and be safe for 
another n steps.  *)

Fixpoint hplus_list l := 
  match l with 
    | nil      => (fun x => None)
    | x :: l   => hplus x (hplus_list l)
  end.

Definition RGdef (l: list rname) (hh : rname -> heap) :=
  forall r1 r2 (NEQ: r1 <> r2) (NIN1: In r1 l) (NIN2: In r2 l), 
    hdef (hh r1) (hh r2).

Fixpoint RGsafe (n : nat) (c: cmd) (s: stack) (h: heap) (hh: rname -> heap) 
  (rely guar : rname -> heap -> heap -> Prop) (q: rgsep_assn) := 
  match n with O => True
    | S n =>
(* Condition (i) *)
          (c = Cskip -> RGsat (s, h, hh) q)
(* Condition (ii) *)
       /\ (forall hF (D: hdef h hF) (ABORT: aborts c (s, hplus h hF)), False)
(* Condition (iii) *)
       /\ (forall a (ACC: In a (accesses c s)), h a <> None)
(* Condition (iv) *)
       /\ (forall hh'
             (RELY: forall r (NEQ: hh r <> hh' r), 
               ~ In r (locked c) /\ rely r (hh r) (hh' r) /\ hdef h (hh' r)),
             RGsafe n c s h hh' rely guar q)
(* Condition (v) *)
       /\ (forall hJ hF c' ss'
             (STEP: red c (s, hplus h (hplus hJ hF)) c' ss')
             (EQ: hJ = hplus_list (map hh (list_minus Z.eq_dec (locked c') (locked c))))
             (D1: hdef h hF)
             (RD: RGdef (list_minus Z.eq_dec (locked c') (locked c)) hh)
             (Dh: forall r (IN: In r (locked c')) (NIN: ~ In r (locked c)), 
                  hdef (hplus h hF) (hh r)),
             exists h' hh',
               snd ss' = 
                 hplus h' 
                   (hplus (hplus_list (map hh' (list_minus Z.eq_dec (locked c) (locked c')))) hF)
               /\ hdef h' hF
               /\ << RD' : RGdef (list_minus Z.eq_dec (locked c) (locked c')) hh' >>
               /\ << Dh' : forall r (IN: In r (locked c)) (NIN: ~ In r (locked c')), 
                           hdef (hplus h' hF) (hh' r) >>
               /\ << GUAR : forall r (IN: In r (locked c)) (NIN: ~ In r (locked c')), 
                            guar r (hh r) (hh' r) >>
               /\ << GOTH : forall r (OTH: ~ In r (locked c) \/ In r (locked c')), 
                            hh r = hh' r >>
               /\ RGsafe n c' (fst ss') h' hh' rely guar q)
  end.

(** Now, the meaning of triples (cf. Definitions 2 and 5 in paper) *)

Definition RGSep rely guar p c q :=
  user_cmd c /\ (forall n s h hh, RGsat (s, h, hh) p -> RGsafe n c s h hh rely guar q).

(** ** Free variables and substitutions *)

(** The free variables of an assertion [p] are given as a predicate [fvA p]. *)

Fixpoint fvAA p := 
  match p with
    | RGlocal P 
    | RGshared _ P    => fvA P
    | RGconj P Q 
    | RGstar P Q
    | RGdisj P Q      => (fun v => fvAA P v \/ fvAA Q v)
    | RGex   P        => (fun v => exists x, fvAA (P x) v)
  end.

(** The free region names in an assertion [p]. *)

Fixpoint frgnA p :=  
  match p with
    | RGlocal P       => (fun v => False)
    | RGshared r P    => (fun v => v = r)
    | RGstar P Q
    | RGconj P Q
    | RGdisj P Q      => (fun v => frgnA P v \/ frgnA Q v)
    | RGex   P        => (fun v => exists x, frgnA (P x) v)
  end.


(** * Soundness proof *)

(** ** Basic properties of the semantics *)

(** 1. Assertions depend only on the values of their free variables and regions. *)

Lemma prop1_AA: forall p s s' (A: forall v (FV: fvAA p v), s v = s' v) h hh,
  RGsat (s, h, hh) p <-> RGsat (s', h, hh) p.
Proof.
  ins; revert h; induction p; ins; repeat (first [apply ex_iff | apply all_iff]; intro); 
    try (by rewrite IHp1, IHp2; auto); eauto using prop1_A, and_iff_compat_l.
Qed.

Lemma prop1_AA_rgn: forall p s h hh hh' (A: forall v (FV: frgnA p v), hh v = hh' v),
  RGsat (s, h, hh) p <-> RGsat (s, h, hh') p.
Proof.
  ins; revert h; induction p; ins; repeat (first [apply ex_iff | apply all_iff]; intro); 
    try (by rewrite IHp1, IHp2; auto); eauto.
  by rewrite A.
Qed.

(** 2. Safety is monotone with respect to the step number
(cf. Proposition 3 in paper). *)

Lemma RGsafe_mon :
  forall n C s h hh R G Q (OK: RGsafe n C s h hh R G Q) m (LEQ: m <= n),
    RGsafe m C s h hh R G Q.
Proof.
  intros until m; revert C s n h hh OK; induction m; ins.
  destruct n; [inv LEQ|apply le_S_n in LEQ]. 
  clarify; simpls; des; repeat split; ins. 
  exploit OK2; eauto; ins; des; eauto 10. 
  exploit OK3; eauto; ins; des; eauto 12.
Qed. 

(** 3. Safety depends only on the values of the free variables of the
program, the postcondition and the resource invariants
(cf. Proposition 4 in the paper). To establish this property, we need
the following auxiliary lemmas.
*)

Lemma RGsafe_agrees : 
  forall n C s h hh R G Q (OK: RGsafe n C s h hh R G Q) s'
    (A: forall v, In v (fvC C) \/ fvAA Q v -> s v = s' v),
    RGsafe n C s' h hh R G Q.
Proof.
  induction n; ins; des; intuition; clarify.
  by apply -> prop1_AA; eauto.
  by eapply OK0, aborts_agrees; eauto; red; symmetry; eauto.
  by eapply OK1; eauto; erewrite accesses_agrees; unfold agrees; eauto.
  by eapply IHn; try eapply OK2; eauto.

  exploit prop2; eauto; intro M; des; simpls; clarify. 
  exploit red_agrees; try apply STEP; [symmetry; eapply A, X|by left|].
  clear STEP; intros (s'0 & _ & STEP & A' & <-). 
  exploit OK3; eauto; []; ins; des. 
  exists h', hh'; repeat eexists; eauto.
  eapply IHn; eauto; symmetry; eapply A'; des; auto.
Qed.


(* -------------------------------------------------------------------------- *)
(** ** Soundness of the proof rules *)
(* -------------------------------------------------------------------------- *)

(** We now show the soundness of each proof rule of CSL separately. *)

Definition stable P exn (rely : rname -> heap -> heap -> Prop) :=
  forall s h hh
    (SAT: RGsat (s,h,hh) P) hh' 
    (RELY: forall r (NIN: ~ In r exn), rely r (hh r) (hh' r) \/ hh r = hh' r) 
    (LOCKED: forall r (IN: In r exn), hh r = hh' r)
    (*Dr: RGdef nil hh' *)
    (Dh: forall r (NIN: ~ In r exn), hdef h (hh' r) \/ hh r = hh' r),
    RGsat (s,h,hh') P.

(** *** Skip *)

Lemma RGsafe_skip :
  forall n s h hh R G Q, 
    RGsat (s,h,hh) Q -> stable Q nil R -> 
    RGsafe n Cskip s h hh R G Q.
Proof.
  induction n; ins; intuition; [inv ABORT|eauto|inv STEP].
  apply IHn; auto.
  eapply H0; eauto; ins; specialize (RELY r); tauto.
Qed.
Hint Resolve RGsafe_skip.

Theorem rule_skip Rely Guar P : stable P nil Rely -> RGSep Rely Guar P Cskip P.
Proof. by split; auto. Qed.

(** *** Parallel composition *)

Notation "P '\3/' Q" := (fun r h h' => P r h h' \/ Q r h h') (at level 100).
Definition Id3 {A B} (r: A) (h h': B) := h = h'.

Lemma In_appAC : 
  forall A (r: A) a b c, In r (b ++ a ++ c) <-> In r (a ++ b ++ c).
Proof. 
  ins; rewrite !in_app_iff in *; intuition.
Qed.

Lemma disj_app A (a b c : list A) : 
  Basic.disjoint (a ++ b) c <->  
  Basic.disjoint a c /\ Basic.disjoint b c.
Proof.
  unfold Basic.disjoint; intuition eauto using in_or_app.
  by rewrite in_app_iff in *; desf; eauto.
Qed.

Lemma disj_app2 A (a b c : list A) : 
  Basic.disjoint c (a ++ b) <->  
  Basic.disjoint c a /\ Basic.disjoint c b.
Proof.
  unfold Basic.disjoint; intuition eauto using in_or_app.
  by rewrite in_app_iff in *; desf; eauto.
Qed.

Lemma disjC A (a b : list A) : 
  Basic.disjoint b a -> Basic.disjoint a b.
Proof.
  unfold Basic.disjoint; eauto.
Qed.
Hint Immediate disjC.


Lemma hdef_hplus_list A h hh (l: list A) : 
  hdef h (hplus_list (map hh l)) <-> (forall r (IN: In r l), hdef h (hh r)).
Proof.
  induction l; [|destruct l]; split; ins; rewrite ?hdef_hplus2 in *; 
    desf; eauto 8; vauto.
Qed.

Notation "P '|==' Q" := (forall x, RGsat x P -> RGsat x Q)  (at level 100).

Definition Afalse := Apure (Bnot (Beq (Enum 0) (Enum 0))).

Lemma hdef_hplusD1 a b c: hdef (hplus a b) c -> hdef a c.
Proof. rewrite hdef_hplus; tauto. Qed.

Lemma hdef_hplusD2 a b c: hdef (hplus a b) c -> hdef b c.
Proof. rewrite hdef_hplus; tauto. Qed.

Lemma hdef_hplusD3 a b c: hdef a (hplus b c) -> hdef a b.
Proof. rewrite hdef_hplus2; tauto. Qed.

Lemma hdef_hplusD4 a b c: hdef a (hplus b c) -> hdef a c.
Proof. rewrite hdef_hplus2; tauto. Qed.

Hint Resolve hdef_hplusD1 hdef_hplusD2 hdef_hplusD3 hdef_hplusD4 : hdef_search.


Lemma RGsafe_par:
 forall Rely Guar1 Guar2 n s hh 
   C1 h1 Q1 (LOK: RGsafe n C1 s h1 hh (Rely \3/ Guar2) Guar1 Q1)
   C2 h2 Q2 (ROK: RGsafe n C2 s h2 hh (Rely \3/ Guar1) Guar2 Q2)
   (WF: wf_cmd (Cpar C1 C2))
   (HD: hdef h1 h2)
   (FV1: disjoint (fvC C1) (wrC C2)) 
   (FV2: disjoint (fvAA Q1) (wrC C2)) 
   (FV4: disjoint (fvC C2) (wrC C1)) 
   (FV5: disjoint (fvAA Q2) (wrC C1)),
  RGsafe n (Cpar C1 C2) s (hplus h1 h2) hh Rely (Guar1 \3/ Guar2) (RGstar Q1 Q2).
Proof.
  induction n; ins; des; intuition; clarify.
{ (* No aborts *)
  rewrite hdef_hplus, hplusA in *; des; inv ABORT; eauto.
  by rewrite hplusAC in A; [eapply ROK0, A|]; eauto.
  (* No races *)
  by destruct ND; eapply disjoint_conv; unfold disjoint, pred_of_list;
     intro y; destruct (HD y); intros; eauto using writes_accesses.
  by destruct ND; eapply disjoint_conv; unfold disjoint, pred_of_list;
     intro y; destruct (HD y); intros; eauto using writes_accesses.
}
{ (* Accesses *)
  by eapply in_app_iff in ACC; unfold hplus in *; desf; eauto.
}
{ (* Rely *)
  eapply (IHn); eauto.
  - eapply LOK2; ins; specialize (RELY r NEQ); intuition; eauto with hdef_search. 
  - eapply ROK2; ins; specialize (RELY r NEQ); intuition; eauto with hdef_search. 
}
{ (* Step *)
  rewrite hdef_hplus, hplusA in *; des.
  inv STEP; simpls.
  { (* C1 does a step *)
    rewrite list_minus_appr in *; auto.
    
    assert (LL : forall r, In r (list_minus Z.eq_dec (locked c1') (locked C1)) -> 
                 hdef h2 (hh r)).
      by intros; rewrite In_list_minus in *;
         specialize (Dh r); rewrite !in_app_iff, !hdef_hplus in Dh; 
         apply Dh; ins; desf; eauto.
    
    rewrite (hplusAC hF) in R; [| by apply hdefC, hdef_hplus_list, LL]; clear LL.
    
    exploit LOK3; try rewrite disj_app in *; eauto.
      by ins; eapply Dh; rewrite in_app_iff in *; auto; ins; desf; eauto.
    intro M; des.
    rewrite hdef_hplus2 in *; des.
    
    assert (LL : forall r, In r (list_minus Z.eq_dec (locked C1) (locked c1')) -> 
                 hdef h2 (hh' r)).
      intros; rewrite In_list_minus in *.
      by specialize (Dh' r); rewrite !hdef_hplus in Dh'; tauto.
    
    exploit (ROK2 hh'); ins; rewrite ?In_app in *; desf; eauto.
       intros; destruct (In_dec Z.eq_dec r (list_minus Z.eq_dec (locked C1) (locked c1'))).
         by intuition; rewrite In_list_minus in *; desf; eauto.
       by rewrite In_list_minus in *; desf; destruct NEQ; apply GOTH; tauto.
    
    exists (hplus h' h2), hh'; repeat eexists; eauto.
      by rewrite M, hplusA; f_equal; rewrite hplusAC; auto; apply hdef_hplus_list, LL. 
      by rewrite hplusA; red; ins; rewrite in_app_iff in *; apply Dh'; tauto.
      by left; eapply GUAR; rewrite in_app_iff in *; tauto.
      by red; intros; eapply GOTH; rewrite !in_app_iff in *; desf; eauto.
    
    destruct (prop2 R) as (B1 & B2 & B3).
    eapply IHn; eauto using red_wf_cmd;
      try (by unfold disjoint, pred_of_list in *; ins; eauto 3).
    by apply RGsafe_agrees with s; try done;
       symmetry; apply B3; unfold disjoint in *; des; eauto.
  }
  { (* C2 does a step *)
    rewrite list_minus_appl in *; auto.
   
    assert (LL : forall r, In r (list_minus Z.eq_dec (locked c2') (locked C2)) ->
                 hdef h1 (hh r)).
      by intros; rewrite In_list_minus in *;
         specialize (Dh r); rewrite !in_app_iff, !hdef_hplus in Dh; 
         apply Dh; ins; desf; eauto.
   
    rewrite (hplusAC _ (hdefC HD)) in R. 
    rewrite (hplusAC hF) in R; [| by apply hdefC, hdef_hplus_list, LL]; clear LL.
   
    exploit ROK3; eauto.
      by ins; rewrite (hplusAC _ HD); eapply Dh; 
         rewrite in_app_iff in *; auto; ins; desf; eauto.
    intro M; des.
    rewrite hdef_hplus2 in *; des.
   
    assert (LL : forall r, In r (list_minus Z.eq_dec (locked C2) (locked c2')) -> 
                 hdef h1 (hh' r)).
      intros; rewrite In_list_minus in *.
      by specialize (Dh' r); rewrite !hdef_hplus in Dh'; tauto. 
   
    exploit (LOK2 hh'); ins; rewrite ?In_app in *; desf; eauto.
       intros; destruct (In_dec Z.eq_dec r (list_minus Z.eq_dec (locked C2) (locked c2'))).
         by intuition; rewrite In_list_minus in *; desf; eauto.
       by rewrite In_list_minus in *; desf; rewrite GOTH in *; vauto; tauto.
   
    exists (hplus h' h1), hh'; repeat eexists; eauto.
      by rewrite M, hplusA; f_equal; rewrite hplusAC; auto; apply hdef_hplus_list, LL. 
      by rewrite hplusA; red; ins; rewrite in_app_iff in *; apply Dh'; tauto.
      by right; eapply GUAR; rewrite in_app_iff in *; tauto.
      by red; intros; eapply GOTH; rewrite !in_app_iff in *; desf; eauto.
   
    destruct (prop2 R) as (B1 & B2 & B3).
    rewrite hplusC; auto.
    eapply IHn; eauto using red_wf_cmd;
      try (by unfold disjoint, pred_of_list in *; ins; eauto 3).
    by apply RGsafe_agrees with s; try done;
       symmetry; apply B3; unfold disjoint in *; des; eauto.
  }
  { (* Par skip skip *)
    exists (hplus h1 h2), hh; rewrite hplusA; repeat split; eauto; try done. 
   
    assert (A: RGsafe n Cskip s h1 hh (Rely \3/ Guar2) Guar1 Q1).
      by apply RGsafe_mon with (S n); auto.
    assert (B: RGsafe n Cskip s h2 hh (Rely \3/ Guar1) Guar2 Q2).
      by apply RGsafe_mon with (S n); auto.
    clear -A B HD.
    revert h1 h2 hh A B HD.
    induction n; ins; desf; intuition; first [by inv ABORT | by inv STEP | idtac].
      by repeat eexists; eauto.
    apply IHn; eauto.
      by apply A2; ins; specialize (RELY _ NEQ); rewrite hdef_hplus in *; desf; auto.
      by apply B2; ins; specialize (RELY _ NEQ); rewrite hdef_hplus in *; desf; auto.
  }
}
Qed.

Theorem rule_par Rely Guar1 Guar2 P1 P2 C1 C2 Q1 Q2 :
  RGSep (Rely \3/ Guar2) Guar1 P1 C1 Q1 ->
  RGSep (Rely \3/ Guar1) Guar2 P2 C2 Q2 ->
  disjoint (fvC C1) (wrC C2) -> disjoint (fvAA Q1) (wrC C2) ->
  disjoint (fvC C2) (wrC C1) -> disjoint (fvAA Q2) (wrC C1) ->
  RGSep Rely (Guar1 \3/ Guar2) (RGstar P1 P2) (Cpar C1 C2) (RGstar Q1 Q2).
Proof. 
  unfold RGSep; ins; intuition; desf; eapply RGsafe_par; simpl; auto.
  rewrite !user_cmd_locked; simpls; auto.
Qed.

(** *** Resource declaration *)


Lemma upds : forall A f x (y: A), upd f x y x = y.
Proof. unfold upd; ins; desf. Qed.

Lemma updr : forall A f x (y z: A), upd (upd f x y) x z = upd f x z.
Proof. unfold upd; ins; extensionality w; desf. Qed.

Lemma updr' : forall A (f: Z -> A) x, upd f x (f x) = f.
Proof. unfold upd; ins; extensionality w; desf. Qed.

Lemma map_upd_irr A r l hh (hK : A) :
  ~ In r l -> (map (upd hh r hK) l = map hh l).
Proof.
  induction l; unfold upd; ins; desf; [exfalso|f_equal]; eauto.
Qed.


Lemma RGdef_upd_irr r l hh hK :
  ~ In r l -> (RGdef l (upd hh r hK) <-> RGdef l hh).
Proof.
  split; unfold upd, RGdef; ins; specialize (H0 r1 r2); desf; auto.
Qed.

Lemma RGdef_removeAll r l hh :
  RGdef (removeAll Z.eq_dec l r) hh ->
  (forall r', In r' (removeAll Z.eq_dec l r) -> hdef (hh r) (hh r')) ->
  RGdef l hh.
Proof.
  unfold RGdef; ins; specialize (H r1 r2); 
  generalize (H0 r1); intro; specialize (H0 r2);
  rewrite !In_removeAll in *; desf; auto.
  destruct (Z.eq_dec r r1); subst; auto.
  destruct (Z.eq_dec r r2); subst; intuition.
Qed.


Lemma hplus_list_expand hh r l : forall
  (DL: disjoint_list l)
  (IN: In r l)
  (HD: forall r1 (IN1: In r1 l) r2 (IN2: In r2 l) (NEQ: r1 <> r2), hdef (hh r1) (hh r2)),
  hplus_list (map hh l) =
  hplus (hh r) (hplus_list (map hh (removeAll Z.eq_dec l r))).
Proof.
  induction l; ins; desf; simpls. 
    by rewrite removeAll_irr.
  rewrite IHl, hplusAC; auto.
Qed.

Lemma RGsafe_resource:
 forall r Rely Rr Guar Gr Q q (NF: ~ frgnA Q r) n C s h hh
   (OK: RGsafe n C s h hh (upd Rely r Rr) (upd Guar r Gr) 
              (RGstar Q (RGshared r q))) 
   (WF: wf_cmd C),
     (forall hK (NIN: ~ In r (locked C)) (HD: hdef h (hh r)),
       RGsafe n (Cresource r C) s (hplus h (hh r)) 
                (upd hh r hK) Rely Guar (RGstar Q (RGlocal q)))
   /\ (forall hK (IN: In r (locked C)),
       RGsafe n (Cresource r C) s h (upd hh r hK) Rely Guar (RGstar Q (RGlocal q))).
Proof.
  induction n; ins; desf; intuition; desf;
    try rewrite hdef_hplus in *; desf;
    try (by inv ABORT; desf; try rewrite hplusA in A; eauto);
    try (inv STEP).

  by unfold hplus in *; desf; eauto.

  { (* rely *)
    rewrite removeAll_irr in *; simpls. 
    exploit OK2.
    instantiate (1 := upd hh' r (hh r)).
    unfold upd in *; ins; specialize (RELY r0); desf; try tauto.
    rewrite hdef_hplus in *; tauto.
    intros M.
   
    edestruct IHn as [X _]; eauto.
    specialize (X (hh' r)); rewrite upds, updr, updr' in X; tauto.
  }
  { (* normal step *)
  rewrite removeAll_irr in *; simpls. 
  rewrite hplusA in *.
  rewrite map_upd_irr in R; [|rewrite In_list_minus, In_removeAll; tauto].
  rewrite RGdef_upd_irr in RD; [|rewrite In_list_minus, In_removeAll; tauto].
  assert (B := prop2 R); desf; simpls.


  destruct (In_dec Z.eq_dec r (locked c'0)).
  - rewrite <- (hplusA (hh r)) in R; simpls.
   
    exploit OK3; eauto.
      rewrite <- removeAll_list_minus.
      symmetry; apply hplus_list_expand;
      eauto using disjoint_list_list_minus, disjoint_locked, red_wf_cmd.
        by rewrite In_list_minus.
      ins; generalize (Dh r1); intro; specialize (Dh r2); specialize (RD r1 r2 NEQ).
      by rewrite ?In_list_minus, ?In_removeAll, ?hdef_hplus in *; 
         unfold upd in *; desf; intuition.
   
      rewrite <- removeAll_list_minus in RD.
      eapply (RGdef_removeAll RD).
      ins; specialize (Dh r'); rewrite In_removeAll, In_list_minus, ?hdef_hplus in *;
        unfold upd in *; desf; tauto.
   
      ins; specialize (Dh r0); unfold upd in *; desf; eauto.
      rewrite In_removeAll, !hdef_hplus in Dh.
      by destruct (Z.eq_dec r0 r); [subst | ]; intuition; eauto.
    intro M; desf.
    rewrite M.
    exists h', (upd hh' r hK); repeat eexists; unfold NW; ins; 
      try rewrite In_removeAll in *; eauto. 
      by rewrite list_minus_removeAll_irr, map_upd_irr; try rewrite In_list_minus; tauto.
      by rewrite list_minus_removeAll_irr, RGdef_upd_irr; try rewrite In_list_minus; tauto.
      by specialize (Dh' r0); unfold upd in *; desf; intuition. 
      by specialize (GUAR r0); unfold upd in *; desf; tauto.
      by specialize (GOTH r0); unfold upd in *; desf; tauto.
    by edestruct IHn as [_ X]; eauto using red_wf_cmd.

  - rewrite removeAll_irr in *; simpls. 
    rewrite (hplusAC hF) in R; simpls;
     [| apply hdefC, hdef_hplus_list; ins; rewrite In_list_minus in *;
        specialize (Dh r0); rewrite !hdef_hplus in Dh; unfold upd in Dh; desf; tauto].
    
    exploit OK3; eauto.
      by ins; specialize (Dh r0); unfold upd in *; desf; eauto.
    intro M; desf; rewrite M.
    rewrite hdef_hplus2 in *; desf.
    exists (hplus h' (hh' r)), (upd hh' r hK); unfold NW;
      rewrite map_upd_irr, RGdef_upd_irr; try rewrite In_list_minus; try tauto;
      repeat eexists; ins; eauto.
    rewrite (hplusAC hF), hplusA, (GOTH r); vauto.
    eapply hdef_hplus_list; intros.
    by specialize (Dh' r0); rewrite !hdef_hplus in Dh'; rewrite In_list_minus in IN; tauto.
    
    by rewrite <- (GOTH r); eauto.
    by unfold upd; desf; rewrite hplusA, <- (GOTH r); eauto.
    
    by specialize (GUAR r0); unfold upd in *; desf; tauto.
    by specialize (GOTH r0); unfold upd in *; desf; tauto.
    edestruct IHn as [X _]; eauto using red_wf_cmd.
    by eapply X; eauto; rewrite <- GOTH; tauto.
  }
  { (* exit *)
    simpls; rewrite hplusU.
    repeat eexists; unfold NW; ins; eauto.
    assert (B: RGsafe n Cskip s h hh  (upd Rely r Rr) (upd Guar r Gr) 
                      (RGstar Q (RGshared r q))).
      by apply RGsafe_mon with (S n); auto.

    clear -B HD NF.
    revert hh hK B HD; induction n; ins; desf; repeat split; ins;
      try solve [inv ABORT | inv STEP]; [ | clear B ]; intuition; desf.
      assert (h2 = fun x => None) by (extensionality x; done); subst.
      rewrite hplusU2 in *; repeat eexists; eauto.
      by eapply prop1_AA_rgn; [|edone]; intros; unfold upd; desf.
   
    exploit (B2 (upd hh' r (hh r))).
      ins; specialize (RELY r0); unfold upd in *; rewrite hdef_hplus in *; desf; tauto.
    intro M; specialize (IHn _ (hh' r) M); rewrite upds, updr, updr' in IHn; tauto. 
  }
  { (* rely *)
    exploit OK2.
      instantiate (1 := upd hh' r (hh r)).
      unfold upd in *; ins; specialize (RELY r0); desf; try tauto.
      rewrite In_removeAll in RELY; tauto.
    intros M.
    edestruct IHn as [_ X]; eauto.
    specialize (X (hh' r)); rewrite updr, updr' in X; tauto.
  }
  { (* normal step *)
    simpls.
    rewrite map_upd_irr in R; [|rewrite In_list_minus, In_removeAll; tauto].
    rewrite RGdef_upd_irr in RD; [|rewrite In_list_minus, In_removeAll; tauto].
    rewrite list_minus_removeAll2 in *.
    rewrite removeAll_irr in RD; [| rewrite In_list_minus; tauto].
   
    assert (B := prop2 R); desf; simpls.
   
    exploit OK3; eauto.
      by rewrite removeAll_irr; try rewrite In_list_minus; tauto.
      by ins; specialize (Dh r0); unfold upd in Dh; 
         rewrite !In_removeAll in Dh; desf; tauto.
    intro M; desf; rewrite M; unfold NW.
    edestruct IHn as [X1 X2]; eauto using red_wf_cmd; [].
   
    destruct (In_dec Z.eq_dec r (locked c'0)).
      rewrite removeAll_irr; [| rewrite In_list_minus; tauto].
      eexists h', (upd hh' r hK); 
        rewrite map_upd_irr, RGdef_upd_irr; try (rewrite In_list_minus; tauto);
        repeat eexists; ins; auto; unfold upd; rewrite !In_removeAll in *; desf; eauto. 
      by specialize (GUAR r0); unfold upd in *; desf; tauto.
   
    exists (hplus h' (hh' r)), (upd hh' r hK). 
    rewrite map_upd_irr, RGdef_upd_irr; try (rewrite In_removeAll; tauto).
    rewrite hplusA; repeat eexists; ins; eauto; instantiate; repeat rewrite In_removeAll in *.
   
    rewrite (hplus_list_expand (r:=r)), hplusA; try done.
      by eauto using disjoint_list_list_minus, disjoint_locked, red_wf_cmd.
      by rewrite In_list_minus.
      ins; generalize (Dh' r1); intro; specialize (Dh' r2); specialize (RD' r1 r2 NEQ).
      by rewrite ?In_list_minus, ?In_removeAll, ?hdef_hplus in *; 
         unfold upd in *; desf; intuition.
   
    by specialize (Dh' r); rewrite hdef_hplus in Dh'; intuition.
    by red; intros; rewrite In_removeAll in *; apply RD'; tauto.
    by unfold upd; desf; eauto;
       specialize (Dh' r0); rewrite !hdef_hplus in *; intuition;
       eapply RD'; try rewrite In_list_minus; eauto. 
    specialize (GUAR r0); unfold upd in *; desf; tauto.
    specialize (GOTH r0); unfold upd in *; desf; tauto.
    apply X1; auto; eauto with hdef_search.
  }
Qed.

Theorem rule_resource Rely R Guar G P p r C Q q:
  RGSep (upd Rely r R) (upd Guar r G) (RGstar P (RGshared r p)) C (RGstar Q (RGshared r q)) ->
  ~ frgnA P r ->
  ~ frgnA Q r ->
  RGSep Rely Guar (RGstar P (RGlocal p)) (Cresource r C) (RGstar Q (RGlocal q)).
Proof.
  unfold RGSep; ins; intuition; desf. 
  assert (M: RGsat (s, h1, upd hh r h2) P)
    by (eapply prop1_AA_rgn, H; ins; unfold upd; desf).
  clear H.
  edestruct RGsafe_resource as (X & _); 
    try eapply H3; repeat eexists; eauto using hdefU2; [by rewrite upds|].
  specialize (X (hh r)).
  rewrite hplusU2, upds, updr, updr', user_cmd_locked in X; eauto.
Qed.

(** *** Frame rule *)

Lemma RGsafe_frame:
 forall n C s h hh Rely Guar Q 
   (OK: RGsafe n C s h hh Rely Guar Q) hR
   (HD: hdef h hR) R
   (DISJ: disjoint (fvAA R) (wrC C))
   (STAB: stable R nil (Rely \3/ Guar))
   (SAT_R: RGsat (s,hR,hh) R),
 RGsafe n C s (hplus h hR) hh Rely Guar (RGstar Q R).
Proof.
  intros until 0; revert C s h hh.
  induction n; ins; desf; intuition; rewrite ?hdef_hplus, ?hplusA in *; desf; eauto.
    by eauto 8.
    by unfold hplus in *; desf; eauto.
  { (* Rely *)
    eapply IHn; try eapply OK2; auto.
      by ins; specialize (RELY _ NEQ); desf; eauto with hdef_search.
    eapply STAB; eauto; ins; specialize (RELY r); rewrite hdef_hplus in *; tauto.
  }
  (* Step *)
  assert (LL : forall r, In r (list_minus Z.eq_dec (locked c') (locked C)) -> hdef hR (hh r)).
    by intros; rewrite In_list_minus in *; 
       specialize (Dh r); rewrite !hdef_hplus in Dh;
       apply Dh; ins; desf; eauto.

  rewrite (hplusAC hF) in STEP; [| by apply hdefC, hdef_hplus_list, LL]; clear LL.
  
  exploit (OK3); eauto. 
  intro M; des.
  rewrite hdef_hplus2 in *; des.

  assert (LL : forall r, In r (list_minus Z.eq_dec (locked C) (locked c')) -> 
    hdef hR (hh' r)).
    intros; rewrite In_list_minus in *.
    by specialize (Dh' r); rewrite !hdef_hplus in Dh'; tauto.

  exists (hplus h' hR), hh'; repeat eexists; eauto.
    by rewrite M, hplusA; f_equal; rewrite hplusAC; auto; apply hdef_hplus_list, LL. 
    by red; intros; rewrite hplusA; auto.

  destruct (prop2 STEP) as (B1 & B2 & B3 & B4).
  eapply IHn; eauto using red_wf_cmd;
    try (by unfold disjoint, pred_of_list in *; ins; eauto).
  eapply prop1_AA with s; eauto.
  eapply (STAB); try edone; ins;
    destruct (In_dec Z.eq_dec r (locked C)); eauto;
    destruct (In_dec Z.eq_dec r (locked c')); eauto.
  eauto with hdef_search.
Qed.

Theorem rule_frame Rely Guar P C Q R:
  RGSep Rely Guar P C Q ->
  disjoint (fvAA R) (wrC C) ->
  stable R nil (Rely \3/ Guar) ->  
  RGSep Rely Guar (RGstar P R) C (RGstar Q R).
Proof.
  unfold RGSep; intuition; ins; desf; eauto using RGsafe_frame.
Qed.

(** *** Conditional critical regions *)


Lemma RGsafe_inwith_rely_irr:
  forall n C s h hh Rely Guar Q r' 
    (OK : RGsafe n (Cinwith r' C) s h hh (upd Rely r' (fun h h' => False)) Guar Q)
    (STAB: stable Q nil Rely),
  RGsafe n (Cinwith r' C) s h hh Rely Guar Q.
Proof.
  induction n; ins; desf; intuition; desf.
    by apply IHn; try apply OK2; ins; specialize (RELY _ NEQ); unfold upd; desf; tauto. 
  exploit OK3; eauto; intro M; desf; rewrite M.
  repeat eexists; eauto; inv STEP; simpls; eauto.
  destruct n; [|eapply RGsafe_skip]; simpls; tauto. 
Qed.

Theorem rule_withR Rely Guar P r B C Q:
  RGSep (upd Rely r (fun h h' => False)) Guar P (Cwith r B C) Q ->
  stable P nil Rely ->
  stable Q nil Rely ->
  RGSep Rely Guar P (Cwith r B C) Q.
Proof.
  unfold RGSep; intros [U A] PS QS; intuition.
  revert hh H; induction n; ins; desf; intuition; desf. 
  - by inv ABORT.
  - eapply IHn; eauto.
    eapply PS; eauto; ins; specialize (RELY r0); tauto.  
  - inv STEP.
    exploit (A (S n)); eauto; intros (_ & _ & _ & _ & OK).
    exploit OK; eauto; clear -QS; intro M; desf; simpls.
    rewrite M; repeat eexists; eauto using RGsafe_inwith_rely_irr.
Qed.


Theorem rule_with Rely Guar P p r B C Q q:
  RGSep Rely Guar (RGstar P (RGlocal (Aconj p (Apure B)))) C (RGstar Q (RGlocal q))  ->
  ~ frgnA Q r ->
  Rely r = (fun h h' => False) ->
  (forall s h h', sat (s,h) p -> sat (s,h') q -> Guar r h h') ->
  disjoint (fvA p) (wrC C) ->
  stable P nil Rely ->
  stable Q nil Rely ->
  RGSep Rely Guar (RGstar P (RGshared r p)) (Cwith r B C) (RGstar Q (RGshared r q)).
Proof.
  intros [U A] FR REQ IN_GUAR DISJ PS QS; unfold RGSep; intuition. 
  simpls; desf.
  assert (h2 = (fun x => None)) by (extensionality x; done); clarify.
  rewrite hplusU2 in *; clear H1 H0.

  revert hh H H3; induction n; ins; intuition; desf.
    by inv ABORT.
  { (* rely *)
    eapply IHn; ins; desf; eauto.
    repeat eexists; eauto using hdefU2, hplusU2. 
      by eapply PS; eauto; ins; specialize (RELY r0); tauto.
    by replace (hh' r) with (hh r) by (specialize (RELY r); rewrite REQ in *; tauto).
  } 
  (* enter *)
  clear IHn.
  inv STEP; simpls.
  rewrite (user_cmd_locked U) in *; simpls.
  specialize (Dh r (or_introl eq_refl) (fun x => x)); rewrite hdef_hplus in *; desf.
  exists (hplus h1 (hh r)), hh; repeat eexists; ins; auto.
    by rewrite hplusU, hplusU2, hplusA.
  clear STEP.
  exploit (A n); [by repeat eexists; eauto|]; intro OK; revert OK.
  assert (WF: ~ In r (locked C)) by (rewrite (user_cmd_locked U); done).
  generalize (hplus h1 (hh r)) as h; clear - FR REQ QS WF DISJ IN_GUAR H3.
  rename H3 into SAT_P.
  revert C s hh WF DISJ SAT_P; induction n; ins; desf; intuition; desf.
    by inv ABORT; eauto.
    eapply IHn, OK2; ins.
      replace (hh' r) with (hh r) by (specialize (RELY r); tauto); auto.
    by specialize (RELY _ NEQ); tauto.
  inv STEP; simpls; desf.
  { (* internal step *)
    rewrite removeAll_irr in *; try done.
    exploit OK3; eauto; [by ins; eapply Dh; ins; desf; eauto|].
    intro M; desf.
    rewrite M; unfold NW; repeat eexists; ins; desf; eauto; try tauto.
    destruct (prop2 R) as (B1 & B2 & B3 & B4); simpls.
    apply IHn; auto.
      by unfold disjoint, pred_of_list in *; eauto. 
    replace (hh' r) with (hh r); auto.
    by eapply prop1_A, SAT_P; eauto.
  } 
  { (* exit *)
    specialize (OK eq_refl); clear OK0 OK1 OK2 OK3 IHn; desf.
    rewrite hdef_hplus in *; desf; rewrite hplusU; unfold NW.
    exists h1, (upd hh r h2); repeat eexists; ins; desf; 
      eauto; unfold upd, RGdef; ins; desf; eauto; try tauto.
      by rewrite hplusU2, hplusA.
    eapply RGsafe_skip.
      repeat eexists; simpls; desf; eauto using hdefU2, hplusU2.
      by eapply prop1_AA_rgn; eauto; ins; desf.
    clear - REQ QS; red; ins; desf.
    exists h1, h2; repeat eexists; eauto.
      by eapply QS; eauto; ins; specialize (Dh r0); rewrite hdef_hplus in *; tauto.
    by destruct (RELY r); try rewrite REQ in *; try congruence.
  }
Qed.

(** *** Sequential composition *)

Lemma RGsafe_seq :
  forall n C s h hh Rely Guar Q 
    (OK : RGsafe n C s h hh Rely Guar Q) C2 
    (U: user_cmd C2) R
    (NEXT: forall m s' h' hh', m <= n -> RGsat (s', h', hh') Q -> 
           RGsafe m C2 s' h' hh' Rely Guar R),
  RGsafe n (Cseq C C2) s h hh Rely Guar R.
Proof.
  induction n; ins; desf; intuition; desf; [by inv ABORT; eauto| |].
    by eapply IHn; try eapply OK2; eauto.
  inv STEP; ins.
    by repeat eexists; eauto; rewrite (user_cmd_locked U) in *.
  exploit OK3; eauto.
  intro; desf; exists h', hh'; repeat eexists; eauto.
Qed.

Theorem rule_seq Rely Guar P C1 Q C2 R :
  RGSep Rely Guar P C1 Q ->
  RGSep Rely Guar Q C2 R ->
  RGSep Rely Guar P (Cseq C1 C2) R.
Proof.
  unfold RGSep; intuition; simpl; eauto using RGsafe_seq.
Qed.


(** *** Conditionals (if-then-else) *)

Lemma red_det_tau Rely Guar s s' C C' Q:
  forall 
    (RED    : forall h, red C (s, h) C' (s', h))
    (DETERM : forall h cn ss (STEP': red C (s, h) cn ss), cn = C' /\ ss = (s',h))
    (NABORT : forall h, ~ aborts C (s, h))
    (ACC    : accesses C s = nil)
    (LOCK   : locked C' = locked C) n h hh
    (OK     : RGsafe n C' s' h hh Rely Guar Q),
    RGsafe n C s h hh Rely Guar Q.
Proof.
  induction n; ins; desf; intuition; desf; eauto.
    by specialize (RED (fun _ => None)); inv RED.
    by rewrite ACC in *.
    by eapply IHn, OK2; rewrite LOCK in *; eauto.
  apply DETERM in STEP; desf; simpl; rewrite <- LOCK in *; repeat eexists; try edone.
  by apply (RGsafe_mon (n := S n)); auto.
Qed.

Theorem rule_if Rely Guar P B C1 C2 Q:
  RGSep Rely Guar (RGconj P (RGlocal (Apure B))) C1 Q ->
  RGSep Rely Guar (RGconj P (RGlocal (Apure (Bnot B)))) C2 Q ->
  RGSep Rely Guar P (Cif B C1 C2) Q.
Proof.
  unfold RGSep; simpl; intuition.
  destruct (bdenot B s) eqn: BEQ;
    eapply red_det_tau; ins; desf; vauto; eauto using user_cmd_locked;
     try (by inv STEP'; simpls; clarify); try (by intro X; inv X).
  eapply H3; clarify.
Qed.

(** *** While *)

Lemma stable_local p exn Rely : 
  stable (RGlocal p) exn Rely.
Proof.
  unfold stable; ins; intuition eauto.
Qed.

Lemma stable_conj P Q exn Rely : 
  stable P exn Rely -> 
  stable Q exn Rely ->
  stable (RGconj P Q) exn Rely.
Proof.
  unfold stable; ins; intuition eauto.
Qed.

Hint Resolve stable_conj stable_local.


Lemma RGsafe_while:
  forall Rely Guar P B C (OK: RGSep Rely Guar (RGconj P (RGlocal (Apure B))) C P) 
    s h hh (SAT_P: RGsat (s, h, hh) P) (STAB: stable P nil Rely) n,
    RGsafe n (Cwhile B C) s h hh Rely Guar (RGconj P (RGlocal (Apure (Bnot B)))).
Proof.
  intros; revert s h hh SAT_P; generalize (le_refl n); generalize n at -2 as m.
  induction n; destruct m; ins; [by inv H| apply le_S_n in H].
  intuition; desf; [by inv ABORT| |].
    by eapply IHn, STAB; eauto; ins; specialize (RELY r); tauto.
  inv STEP; repeat eexists; eauto; simpls. 
  clear STEP Dh.
    destruct (bdenot B s) eqn:?; 
      eapply red_det_tau; ins; desf; vauto; eauto using user_cmd_locked;
     try (by inv STEP'; simpls; clarify); try (by intro X; inv X); simpls.
   by apply user_cmd_locked; destruct OK.
   by eapply RGsafe_seq; try apply OK; ins; eauto using le_trans. 
  apply RGsafe_skip; simpls; clarify; auto.
Qed.

Theorem rule_while Rely Guar P B C :
  RGSep Rely Guar (RGconj P (RGlocal (Apure B))) C P ->
  stable P nil Rely ->
  RGSep Rely Guar P (Cwhile B C) (RGconj P (RGlocal (Apure (Bnot B)))).
Proof.
  unfold RGSep; ins; intuition; eapply RGsafe_while; unfold RGSep; eauto.
Qed.

(** *** SL embedding *)

Lemma sat_envs_noneD :
  forall s h l l',
    sat (s, h) (envs (fun _ : rname => None) l l') -> 
    h = (fun x => None).
Proof.
  intros until 0; unfold envs.
  generalize (list_minus Z.eq_dec l l'); clear l l'; intro l.
  revert h; induction l; ins; desf; extensionality x; try done.
  by rewrite (IHl _ H0), hplusU2.
Qed.

Lemma no_locks_locked C : locks C = nil -> locked C = nil.
Proof.
  intros; generalize (fun r => @locked_locks r C); rewrite H.
  destruct locked; ins; exfalso; eauto.
Qed.

Theorem rule_sl Rely Guar J p C q:
  locks C = nil ->
  CSL J p C q ->
  RGSep Rely Guar (RGlocal p) C (RGlocal q).
Proof.
  unfold CSL, RGSep; inss; desf.
  eapply (SF n) in H0; clear -H H0.
  revert C s h H H0 hh; induction n; ins; desf; intuition; desf. 
    by apply IHn, (safe_mon (n := S n)); auto.

  assert (NOL: locks c' = nil).
    by destruct (prop2 STEP) as (_ & _ & NOL & _);
       rewrite H in *; destruct (locks c'); simpls; exfalso; eauto.
  rewrite (no_locks_locked H), (no_locks_locked NOL) in *; simpls.

  exploit (SOK (fun _ => None)); vauto; eauto. 
    by rewrite (no_locks_locked NOL).
  intro M; desf.
  rewrite (no_locks_locked NOL) in *; simpls.
  exists h', hh; repeat eexists; eauto; vauto.
Qed.

(** *** Simple structural rules (Conseq, Disj, Ex) *)

Notation "R '<3=' G" := 
  (forall r h h', (R r h h' : Prop) -> (G r h h' : Prop))  (at level 100).

Lemma RGsafe_conseq:
  forall n C s h hh Rely Guar Q (OK: RGsafe n C s h hh Rely Guar Q) 
    Rely' (R_IMP: Rely' <3= Rely)
    Guar' (G_IMP: Guar <3= Guar')
    Q'    (Q_IMP: Q |== Q'),
  RGsafe n C s h hh Rely' Guar' Q'.
Proof.
  intros; revert C s h hh OK; induction n; ins; desf; intuition.
    by apply IHn, OK2; ins; specialize (RELY _ NEQ); desf; auto.
  exploit OK3; eauto; []; intro; desf; exists h', hh'; repeat eexists; eauto.
Qed.

Theorem rule_conseq Rely Guar P C Q Rely' Guar' P' Q':
  RGSep Rely Guar P C Q -> 
  (P' |== P) -> (Q |== Q') -> 
  (Rely' <3= Rely) -> (Guar <3= Guar') -> 
  RGSep Rely' Guar' P' C Q'.
Proof.
  unfold RGSep; intuition; eauto using RGsafe_conseq.
Qed.

Theorem rule_disj Rely Guar P1 P2 C Q1 Q2:
  RGSep Rely Guar P1 C Q1 -> 
  RGSep Rely Guar P2 C Q2 ->
  RGSep Rely Guar (RGdisj P1 P2) C (RGdisj Q1 Q2).
Proof.
  unfold RGSep; ins; intuition; eapply RGsafe_conseq; eauto; vauto.
Qed.

Theorem rule_ex A Rely Guar P C Q:
  inhabited A \/ user_cmd C ->
  (forall x : A, RGSep Rely Guar (P x) C (Q x)) -> 
  RGSep Rely Guar (RGex P) C (RGex Q).
Proof.
  unfold RGSep; ins; split; [|clear H]. 
    by destruct H as [[]|]; auto; apply H0.
  ins; desf; eapply RGsafe_conseq; try eapply H0; eauto; vauto.
Qed.

