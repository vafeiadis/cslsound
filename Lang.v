Require Import HahnBase ZArith List Basic.

Set Implicit Arguments.
Unset Strict Implicit.

(** This file contains a soundness proof for CSL (with multiple resources)
  as presented by O'Hearn and Brookes including the data-race freedom property
  of CSL.  For simplicity, there is a slight difference regarding variable
  side-conditions: we do not allow resource-owned variables. *)

(** * Language syntax and semantics *)

(** We define the syntax and the operational semantics of the programming 
language of O'Hearn and Brookes. *)

Definition var   := Z.
Definition rname := Z.
Definition stack := var -> Z.
Definition state := (stack * heap)%type.

Inductive exp := 
  | Evar  (x : var)
  | Enum  (n : Z)
  | Eplus (e1: exp) (e2: exp).

Inductive bexp :=
  | Beq  (e1: exp) (e2: exp)
  | Band (b1: bexp) (b2: bexp)
  | Bnot (b: bexp).

Inductive cmd :=
  | Cskip
  | Cassign (x: var) (e: exp)
  | Cread   (x: var) (e: exp)
  | Cwrite  (e1: exp) (e2: exp)
  | Calloc  (x: var) (e: exp)
  | Cdispose (e: exp)
  | Cseq   (c1: cmd) (c2: cmd)
  | Cpar   (c1: cmd) (c2: cmd)
  | Cif    (b: bexp) (c1: cmd) (c2: cmd)
  | Cwhile (b: bexp) (c: cmd)
  | Cresource (r: rname) (c: cmd)
  | Cwith     (r: rname) (b: bexp) (c: cmd)
  | Cinwith   (r: rname) (c: cmd).

(** Arithmetic expressions ([exp]) consist of variables, constants, and
arithmetic operations. Boolean expressions ([bexp]) consist of comparisons
between arithmetic expressions.  Commands ([cmd]) include the empty command,
variable assignments, memory reads, writes, allocations and deallocations,
sequential and parallel composition, conditionals, while loops, resource
declaration and conditional critical regions (CCRs).  The last command form
represents a partially executed CCR and does not appear in user programs. 
This restriction is captured by the following definition: *)

Fixpoint user_cmd c := 
  match c with
    | Cskip         => True
    | Cassign x E   => True
    | Cread x E     => True
    | Cwrite E E'   => True
    | Calloc x E    => True
    | Cdispose E    => True
    | Cseq C1 C2    => user_cmd C1 /\ user_cmd C2
    | Cpar C1 C2    => user_cmd C1 /\ user_cmd C2
    | Cif B C1 C2   => user_cmd C1 /\ user_cmd C2
    | Cwhile B C    => user_cmd C
    | Cresource r C => user_cmd C
    | Cwith r B C   => user_cmd C
    | Cinwith r C   => False
  end.

(** The following function returns a list of locks that a command is
currently holding in some arbitrary fixed order. *)

Fixpoint locked c := 
  match c with
    | Cskip         => nil
    | Cassign x e   => nil
    | Cread x e     => nil
    | Cwrite e e'   => nil
    | Calloc x e    => nil
    | Cdispose e    => nil
    | Cseq c1 c2    => locked c1
    | Cpar c1 c2    => locked c1 ++ locked c2
    | Cif b c1 c2   => nil
    | Cwhile b c    => nil
    | Cresource r c => removeAll Z.eq_dec (locked c) r
    | Cwith r b c   => nil
    | Cinwith r c   => r :: locked c
  end.

(** The following function returns a list of locks that a command has
access to (either has acquired or may acquire in the future). *)

Fixpoint locks c := 
  match c with
    | Cskip         => nil
    | Cassign x e   => nil
    | Cread x e     => nil
    | Cwrite e e'   => nil
    | Calloc x e    => nil
    | Cdispose e    => nil
    | Cseq c1 c2    => locks c1 ++ locks c2
    | Cpar c1 c2    => locks c1 ++ locks c2
    | Cif b c1 c2   => locks c1 ++ locks c2
    | Cwhile b c    => locks c
    | Cresource r c => removeAll Z.eq_dec (locks c) r
    | Cwith r b c   => r :: locks c 
    | Cinwith r c   => r :: locks c
  end.


(** ** Semantics of expressions *)

(** Denotational semantics for arithmetic and boolean expressions. *)

Fixpoint edenot e s :=
  match e with
    | Evar v      => s v
    | Enum n      => n
    | Eplus e1 e2 => (edenot e1 s + edenot e2 s)%Z
  end.

Fixpoint bdenot b s : bool := 
  match b with
    | Beq e1 e2  => if Z.eq_dec (edenot e1 s) (edenot e2 s) then true else false
    | Band b1 b2 => bdenot b1 s && bdenot b2 s
    | Bnot b     => negb (bdenot b s)
  end.

(** ** Semantics of commands *)

(** The semantics for [Cwrite e e'] is a bit odd in that if [e] is not
    allocated, then it can allocate it and do the assignment.  This is
    for illustration purposes only.  Requiring that [h (edenot e s) <>
    None] does not change the proof. *)

Inductive red: cmd -> state -> cmd -> state -> Prop := 
| red_Seq1: forall c ss, red (Cseq Cskip c) ss c ss
| red_Seq2: forall c1 ss c1' ss' c2 
  (R: red c1 ss c1' ss'), 
  red (Cseq c1 c2) ss (Cseq c1' c2) ss'
| red_If1: forall b c1 c2 ss 
  (B: bdenot b (fst ss) = true), 
  red (Cif b c1 c2) ss c1 ss
| red_If2: forall b c1 c2 ss
  (B: bdenot b (fst ss) = false),
  red (Cif b c1 c2) ss c2 ss
| red_Par1: forall c1 c2 ss c1' ss'
  (R: red c1 ss c1' ss') 
  (D: disjoint (locked c1') (locked c2)), 
  red (Cpar c1 c2) ss (Cpar c1' c2) ss'
| red_Par2: forall c1 c2 ss c2' ss'
  (R: red c2 ss c2' ss') 
  (D: disjoint (locked c1) (locked c2')), 
  red (Cpar c1 c2) ss (Cpar c1 c2') ss'
| red_Par3: forall ss, red (Cpar Cskip Cskip) ss Cskip ss
| red_Loop: forall b c ss, 
  red (Cwhile b c) ss (Cif b (Cseq c (Cwhile b c)) Cskip) ss
| red_Res1: forall r c ss c' ss'
  (R: red c ss c' ss'),
  red (Cresource r c) ss (Cresource r c') ss'
| red_Res2: forall r ss, red (Cresource r Cskip) ss Cskip ss
| red_With1: forall r b c ss 
  (B: bdenot b (fst ss)),
  red (Cwith r b c) ss (Cinwith r c) ss
| red_With2:  forall r c ss c' ss'
  (R: red c ss c' ss')
  (NIN: ~ In r (locked c')),
  red (Cinwith r c) ss (Cinwith r c') ss'
| red_With3: forall r ss, red (Cinwith r Cskip) ss Cskip ss
| red_Assign: forall x e ss ss' s h
   (EQ1: ss = (s, h))
   (EQ2: ss' = (upd s x (edenot e s), h)),
   red (Cassign x e) ss Cskip ss'
| red_Read: forall x e ss ss' s h v
   (EQ1: ss = (s, h))
   (RD: h (edenot e s) = Some v)
   (EQ2: ss' = (upd s x v, h)),
   red (Cread x e) ss Cskip ss'
| red_Write: forall e1 e2 ss ss' s h
   (EQ1: ss = (s, h))
   (EQ2: ss' = (s, upd h (edenot e1 s) (Some (edenot e2 s)))),
   red (Cwrite e1 e2) ss Cskip ss'
| red_Alloc: forall x e ss ss' s h v
   (EQ1: ss = (s, h))
   (NIN: h v = None)
   (EQ2: ss' = (upd s x v, upd h v (Some (edenot e s)))),
   red (Calloc x e) ss Cskip ss'
| red_Free: forall e ss ss' s h
   (EQ1: ss = (s, h))
   (EQ2: ss' = (s, upd h (edenot e s) None)),
   red (Cdispose e) ss Cskip ss'.

(** ** Abort semantics *)

(** Below, we define the sets of memory accesses and memory writes
  that a command performs in one step. These are used to define what a
  race condition is. Note that we do not count memory allocation as a
  memory access because the memory cell allocated is fresh. *)

Fixpoint accesses c s := 
  match c with
    | Cskip => nil
    | (Cassign x e)   => nil
    | (Cread x e)     => edenot e s :: nil
    | (Cwrite e e')   => edenot e s :: nil
    | (Calloc x e)    => nil
    | (Cdispose e)    => edenot e s :: nil
    | (Cseq c1 c2)    => accesses c1 s
    | (Cpar c1 c2)    => accesses c1 s ++ accesses c2 s
    | (Cif b c1 c2)   => nil
    | (Cwhile b c)    => nil
    | (Cresource r c) => accesses c s
    | (Cwith r b c)   => nil
    | (Cinwith r c)   => accesses c s
  end.

Fixpoint writes c s :=
  match c with
    | Cskip => nil
    | (Cassign x e)   => nil
    | (Cread x e)     => nil
    | (Cwrite e e')   => edenot e s :: nil
    | (Calloc x e)    => nil
    | (Cdispose e)    => edenot e s :: nil
    | (Cseq c1 c2)    => writes c1 s
    | (Cpar c1 c2)    => writes c1 s ++ writes c2 s
    | (Cif b c1 c2)   => nil
    | (Cwhile b c)    => nil
    | (Cresource r c) => writes c s
    | (Cwith r b c)   => nil
    | (Cinwith r c)   => writes c s
  end.

(** A command aborts in a given state whenever it can access
  unallocated memory or has a race condition in its first execution
  step. The soundness statement of the logic asserts that these
  transitions never occur. *)

Inductive aborts : cmd -> state -> Prop := 
| aborts_Seq : forall c1 c2 ss (A: aborts c1 ss), aborts (Cseq c1 c2) ss
| aborts_Par1: forall c1 c2 ss (A: aborts c1 ss), aborts (Cpar c1 c2) ss
| aborts_Par2: forall c1 c2 ss (A: aborts c2 ss), aborts (Cpar c1 c2) ss
| aborts_Race1: forall c1 c2 ss 
    (ND: ~ disjoint (accesses c1 (fst ss)) (writes c2 (fst ss))), 
    aborts (Cpar c1 c2) ss
| aborts_Race2: forall c1 c2 ss 
    (ND: ~ disjoint (writes c1 (fst ss)) (accesses c2 (fst ss))), 
    aborts (Cpar c1 c2) ss
| aborts_Res: forall r c ss (A: aborts c ss), aborts (Cresource r c) ss
| aborts_Atom: forall r c ss (A: aborts c ss), aborts (Cinwith r c) ss
| aborts_Read: forall x e ss
    (NIN: snd ss (edenot e (fst ss)) = None),
    aborts (Cread x e) ss
| aborts_Write: forall e1 e2 ss
    (NIN: snd ss (edenot e1 (fst ss)) = None),
    aborts (Cwrite e1 e2) ss
| aborts_Free: forall e ss
    (NIN: snd ss (edenot e (fst ss)) = None),
    aborts (Cdispose e) ss.

(** ** Well-formed commands *)

(** Well-formed commands are intuitively those that can arise from a user
command by a reduction sequence.  In particular, they can have partially
executed CCRs only at reduction positions and their partially executed CCRs
must satisfy mutual exclusion.  *)

Fixpoint wf_cmd c :=
  match c with
    | Cskip         => True
    | Cassign x e   => True
    | Cread x e     => True
    | Cwrite e e'   => True
    | Calloc x e    => True
    | Cdispose e    => True
    | Cseq c1 c2    => wf_cmd c1 /\ wf_cmd c2
    | Cpar c1 c2    => wf_cmd c1 /\ wf_cmd c2 /\ disjoint (locked c1) (locked c2)
    | Cif b c1 c2   => user_cmd c1 /\ user_cmd c2
    | Cwhile b c    => user_cmd c
    | Cresource r c => wf_cmd c
    | Cwith r b c   => user_cmd c
    | Cinwith r c   => wf_cmd c /\ ~ In r (locked c)
  end.

(** Some basic properties: all user commands are well formed;
  well-formedness is preserved under reduction; user commands cannot
  immediately release a lock (they must have acquired it first). *)

Lemma user_cmdD: forall c, user_cmd c -> wf_cmd c /\ locked c = nil.
Proof.
  by induction c; simpl; intuition;
     repeat match goal with H: _ = nil |- _ => rewrite H end.
Qed.

Lemma user_cmd_locked: forall c, user_cmd c -> locked c = nil.
Proof.
  by induction c; simpl; intuition;
     repeat match goal with H: _ = nil |- _ => rewrite H end.
Qed.
Hint Immediate user_cmd_locked.

Lemma user_cmd_wf: forall c, user_cmd c -> wf_cmd c.
Proof. pose proof user_cmdD; firstorder. Qed.
Hint Immediate user_cmd_wf.

Lemma locked_locks: forall r c, In r (locked c) -> In r (locks c).
Proof.
  induction c; simpl; rewrite ?in_app_iff, ?In_removeAll in *; intuition.
Qed.

Lemma red_wf_cmd:
  forall c ss c' ss'
    (R: red c ss c' ss')
    (WF: wf_cmd c),
    wf_cmd c'.
Proof.
  induction 1; simpl in *; intros; des; clarify; intuition.
  by rewrite (user_cmd_locked WF) in H; inv H. 
Qed.

Lemma disjoint_locked :
  forall C, wf_cmd C -> disjoint_list (locked C).
Proof.  
  induction C; ins; desf; auto using disjoint_list_removeAll, disjoint_list_app.
Qed.

(** ** Free variables, updated variables and substitutions *)

(** The free variables of expressions, boolean expressions, assertions, 
    commands and environments are defined as expected: *)

Fixpoint fvE e :=
  match e with
    | (Evar v)      => v :: nil
    | (Enum n)      => nil
    | (Eplus e1 e2) => fvE e1 ++ fvE e2
  end.

Fixpoint fvB b := 
  match b with
    | Beq e1 e2   => fvE e1 ++ fvE e2
    | Band b1 b2  => fvB b1 ++ fvB b2
    | Bnot b      => fvB b
  end.

Fixpoint fvC c :=
  match c with
    | Cskip           => nil
    | (Cassign x e)   => x :: fvE e
    | (Cread x e)     => x :: fvE e
    | (Cwrite e e')   => fvE e ++ fvE e'
    | (Calloc x e)    => x :: fvE e
    | (Cdispose e)    => fvE e
    | (Cseq c1 c2)    => fvC c1 ++ fvC c2
    | (Cpar c1 c2)    => fvC c1 ++ fvC c2
    | (Cif b c1 c2)   => fvB b ++ fvC c1 ++ fvC c2
    | (Cwhile b c)    => fvB b ++ fvC c
    | (Cresource r c) => fvC c
    | (Cwith r b c)   => fvB b ++ fvC c
    | (Cinwith r c)   => fvC c
  end.

(** Below, we define the set of syntactically updated variables 
  of a command. This set overapproximates the set of variables that
  are actually updated during the command's execution. *)

Fixpoint wrC c :=
  match c with
    | Cskip           => nil
    | (Cassign x e)   => x :: nil
    | (Cread x e)     => x :: nil
    | (Cwrite e e')   => nil
    | (Calloc x e)    => x :: nil
    | (Cdispose e)    => nil
    | (Cseq c1 c2)    => wrC c1 ++ wrC c2
    | (Cpar c1 c2)    => wrC c1 ++ wrC c2
    | (Cif b c1 c2)   => wrC c1 ++ wrC c2
    | (Cwhile b c)    => wrC c
    | (Cresource r c) => wrC c
    | (Cwith r b c)   => wrC c
    | (Cinwith r c)   => wrC c
  end.

(** We also define the operation of substituting an expression for
a variable in expressions and assertions. *)

Fixpoint subE x e e0 := 
  match e0 with 
    | Evar y      => (if Z.eq_dec x y then e else Evar y)
    | Enum n      => Enum n
    | Eplus e1 e2 => Eplus (subE x e e1) (subE x e e2)
  end.

Fixpoint subB x e b :=
  match b with
    | Beq e1 e2  => Beq (subE x e e1) (subE x e e2)
    | Band b1 b2 => Band (subB x e b1) (subB x e b2)
    | Bnot b     => Bnot (subB x e b)
  end.

Lemma subE_assign:
 forall x e e' s, edenot (subE x e e') s = edenot e' (upd s x (edenot e s)).
Proof.
unfold upd; induction e'; simpl in *; intros; clarify; desf; eauto.
by rewrite IHe'1, IHe'2.
Qed.

Lemma subB_assign:
  forall x e b s, bdenot (subB x e b) s = bdenot b (upd s x (edenot e s)).
Proof.
  induction b; simpl; intros; clarify; repeat rewrite subE_assign; try congruence.
Qed.

(** Definition of two stacks agreeing on a set of variables *)

Definition agrees (X : list rname) (s s' : stack) := forall x, In x X -> s x = s' x.

Lemma agrees_union: 
  forall X Y s s', agrees (X ++ Y) s s' <-> (agrees X s s' /\ agrees Y s s').
Proof.
  unfold agrees; intuition; eapply in_app_iff in H; intuition.
Qed.

Lemma agreesC: forall X x y, agrees X x y -> agrees X y x.
Proof. unfold agrees; intuition (symmetry; eauto). Qed.

Hint Immediate agreesC.

Lemma agrees_tl: forall X Y x y, agrees (X :: Y) x y -> agrees Y x y.
Proof. red; intros; eapply H; vauto. Qed.

Lemma agrees_app1: forall X Y x y, agrees (X ++ Y) x y -> agrees X x y.
Proof. red; intros; eapply H, in_app_iff; vauto. Qed.

Lemma agrees_app2: forall X Y x y, agrees (X ++ Y) x y -> agrees Y x y.
Proof. red; intros; eapply H, in_app_iff; vauto. Qed.

Hint Immediate agrees_app1 agrees_app2.

Lemma agrees_imp: forall X Y x y, agrees X x y -> (forall z, In z Y -> In z X) -> agrees Y x y.
Proof. red; intros; eapply H; eauto. Qed.

(** ** Basic properties of the semantics *)

(** The lemmas in this subsection are Propositions 1 and 2 in the paper. *)

Lemma prop1_E: forall e s s', agrees (fvE e) s s' -> edenot e s = edenot e s'.
Proof.
 induction e; simpl; intros; clarify.
 by apply H; vauto.
 by erewrite IHe1, IHe2; eauto. 
Qed.

Lemma prop1_B: forall b s s', agrees (fvB b) s s' -> bdenot b s = bdenot b s'.
Proof.
  induction b; simpl; intros; clarify; try rewrite agrees_union in *; f_equal; intuition.
  by rewrite (prop1_E H0), (prop1_E H1). 
Qed.

Corollary prop1_E2 :
  forall x E (NIN: ~ In x (fvE E)) s v, edenot E (upd s x v) = edenot E s.
Proof. ins; apply prop1_E; red; unfold upd; ins; desf. Qed. 

Corollary prop1_B2 :
  forall x B (NIN: ~ In x (fvB B)) s v, bdenot B (upd s x v) = bdenot B s.
Proof. ins; apply prop1_B; red; unfold upd; ins; desf. Qed. 

(** Properties of memory accesses: *)

Lemma writes_accesses: 
  forall C s a, In a (writes C s) -> In a (accesses C s).
Proof. induction C; ins; rewrite in_app_iff in *; intuition. Qed.

Lemma accesses_agrees: 
  forall C s s' (A: agrees (fvC C) s s'), accesses C s = accesses C s'.
Proof. 
  induction C; ins; eauto; f_equal; eauto; eapply prop1_E; eauto.
  by red; ins; eapply A; vauto.
Qed.

Lemma writes_agrees : 
  forall C s s' (A: agrees (fvC C) s s'), writes C s = writes C s'.
Proof. 
  induction C; ins; eauto; f_equal; eauto using prop1_E.
Qed.

(** Proposition 2 in the paper, describing how [fvC] and [wrC]
interact with execution steps. *)

Lemma prop2: 
 forall C ss C' ss' (STEP: red C ss C' ss'),
      (forall x, In x (fvC C') -> In x (fvC C))
   /\ (forall x, In x (wrC C') -> In x (wrC C))
   /\ (forall x, In x (locks C') -> In x (locks C))
   /\ (forall x, ~ In x (wrC C) -> fst ss' x = fst ss x).
Proof.
  induction 1; ins; intuition; repeat rewrite in_app_iff in *; intuition; clarify;
  unfold upd; simpl; rewrite ?In_removeAll in *; desf; eauto; exfalso; eauto.
Qed.

