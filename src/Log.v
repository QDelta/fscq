Require Import Arith.
Require Import Omega.
Require Import List.
Require Import Prog.
Require Import Pred.
Require Import Hoare.
Require Import SepAuto.
Require Import BasicProg.
Require Import FunctionalExtensionality.
Require Import ZArith.
Require Import Lia.

Set Implicit Arguments.


(** * A log-based transactions implementation *)
Open Scope Z_scope.

Record xparams := {
  (* The actual data region is everything that's not described here *)

  LogLength : addr; (* Store the length of the log here. *)
  LogCommit : addr; (* Store true to apply after crash. *)

   LogStart : addr; (* Start of log region on disk *)
     LogLen : Z;    (* Size of log region *)

   LogLenOK : 0 <= LogLen
}.

Lemma loglen_pos: forall xp, 0 <= LogLen xp.
Proof.
  destruct xp; auto.
Qed.
Hint Resolve loglen_pos.

Hint Extern 1 (okToUnify (diskIs _) (diskIs _)) => constructor : okToUnify.

Inductive logstate :=
| NoTransaction (cur : mem)
(* Don't touch the disk directly in this state. *)
| ActiveTxn (old : mem) (cur : mem)
(* A transaction is in progress.
 * It started from the first memory and has evolved into the second.
 * It has not committed yet. *)
| CommittedTxn (cur : mem)
(* A transaction has committed but the log has not been applied yet. *).

Module Log.
  Definition logentry := (addr * valu)%type.
  Definition log := list logentry.

  (* Actually replay a log to implement redo in a memory. *)
  Fixpoint replay (l : log) (m : mem) : mem :=
    match l with
    | nil => m
    | (a, v) :: rest =>
      replay rest (upd m a v)
    end.

  Theorem replay_app : forall l m m0 a v,
    (forall a', m a' = replay l m0 a')
    -> (forall a', upd m a v a' = replay (l ++ (a, v) :: nil) m0 a').
  Proof.
    induction l; simpl; intros.
    - unfold upd; destruct (addr_eq_dec a' a); auto.
    - destruct a. auto.
  Qed.

  (* Check that a log is well-formed in memory. *)
  Fixpoint valid_log m (l : log) : Prop :=
    match l with
    | nil => True
    | (a, _) :: rest =>
      indomain a m /\ valid_log m rest
    end.

  Theorem valid_log_app : forall m l1 l2,
    valid_log m l1
    -> valid_log m l2
    -> valid_log m (l1 ++ l2).
  Proof.
    induction l1; auto; intros.
    rewrite <- app_comm_cons.
    destruct a; simpl.
    destruct H.
    intuition.
  Qed.

  Theorem indomain_upd_1 : forall m a a' v,
    indomain a m
    -> indomain a' (upd m a v)
    -> indomain a' m.
  Proof.
    unfold indomain, upd; intros.
    destruct (addr_eq_dec a' a); subst; auto.
  Qed.

  Theorem indomain_upd_2 : forall m a a' v,
    indomain a m
    -> indomain a' m
    -> indomain a' (upd m a v).
  Proof.
    unfold indomain, upd; intros.
    destruct (addr_eq_dec a' a); auto.
    exists v; auto.
  Qed.

  Theorem valid_log_upd : forall m a v l,
    indomain a m
    -> valid_log m l
    -> valid_log (upd m a v) l.
  Proof.
    intros.
    induction l; [firstorder|].
    destruct a0; simpl in *; intuition.
    eapply indomain_upd_2; auto.
  Qed.

  Theorem indomain_replay : forall l m m0 a,
    valid_log m l
    -> m0 a = replay l m a
    -> indomain a m0
    -> indomain a m.
  Proof.
    induction l; simpl.
    - unfold indomain. intros. deex. exists x. congruence.
    - destruct a. intros. destruct_and.
      eapply indomain_upd_1; eauto.
      eapply IHl; eauto.
      apply valid_log_upd; auto.
  Qed.

  Definition logentry_ptsto xp (e : logentry) idx :=
    let (a, v) := e in
    ((LogStart xp + idx*2) |-> a  * (LogStart xp + idx*2 + 1) |-> v)%pred.

  Fixpoint logentry_ptsto_list xp l idx :=
    match l with
    | nil => emp
    | e :: rest =>
      logentry_ptsto xp e idx * logentry_ptsto_list xp rest (idx + 1)
    end%pred.

  Hint Extern 1 (okToUnify (logentry_ptsto_list _ _ _) (logentry_ptsto_list _ _ _)) =>
    unfold okToUnify; f_equal; omega : okToUnify.
  Hint Extern 1 (okToUnify (logentry_ptsto _ _ _) (logentry_ptsto _ _ _)) =>
    unfold okToUnify; f_equal; omega : okToUnify.

  (* If the log appears to have zero length, unify the log's list rep with nil *)
  Hint Extern 1 (okToUnify (LogLength ?a |-> 0) (LogLength ?a |-> @length ?T ?b)) =>
    unify b (@nil T); constructor : okToUnify.

  Definition data_rep old : pred :=
    diskIs old.

  Fixpoint avail_region start len: pred :=
    match len with
    | O => emp
    | S len' => start |->? * avail_region (start + 1) len'
    end%pred.

  Hint Extern 1 (okToUnify (avail_region _ _) (avail_region _ _)) =>
    unfold okToUnify; repeat ( progress f_equal ; try omega ) : okToUnify.

  Hint Rewrite Z.sub_0_r Z.add_0_r.
  Hint Rewrite Zlength_cons.
  Hint Rewrite Zlength_nil.

  Lemma zlength_pos': forall T (l:list T) acc, Zlength_aux acc T l >= acc.
  Proof.
    induction l.
    - simpl; intros; omega.
    - simpl; intros.
      eapply Zge_trans.
      apply IHl.
      omega.
  Qed.

  Lemma zlength_pos: forall T (l:list T), Zlength l >= 0.
  Proof.
    intros; apply zlength_pos'.
  Qed.

  Lemma avail_region_grow' : forall xp l idx, 0 <= idx
    -> Zlength l + idx <= LogLen xp
    -> logentry_ptsto_list xp l idx *
         avail_region (LogStart xp + idx * 2 + Zlength l * 2)
                      (Z.to_nat (((LogLen xp) - Zlength l - idx) * 2)) ==>
       avail_region (LogStart xp + idx * 2) (Z.to_nat ((LogLen xp - idx) * 2)).
  Proof.
    induction l; autorewrite with core; simpl.
    intros; cancel.
    intros.
    assert (Zlength l >= 0); [apply zlength_pos|].
    case_eq ((LogLen xp - idx) * 2); intros; try lia.
    simpl; destruct (Pos2Nat.is_succ p); rewrite H3; simpl.
    destruct x; try lia.
    simpl.
    destruct a; unfold logentry_ptsto.
    cancel.
    replace (LogStart xp + idx * 2 + 1 + 1) with (LogStart xp + (idx + 1) * 2) by omega.
    replace x with (Z.to_nat ((LogLen xp - (idx + 1)) * 2)).
    eapply pimpl_trans; [|apply pimpl_star_emp].
    eapply pimpl_trans; [|apply IHl].
    cancel.
    omega.
    omega.
    (* XXX *)
    admit.
  Qed.

  Lemma avail_region_grow_all : forall xp l,
    Zlength l <= LogLen xp ->
    logentry_ptsto_list xp l 0 *
      avail_region (LogStart xp + Zlength l * 2)
                   (Z.to_nat (((LogLen xp) - Zlength l) * 2)) ==>
    avail_region (LogStart xp) (Z.to_nat ((LogLen xp) * 2)).
  Proof.
    intros.
    replace (LogStart xp) with (LogStart xp + 0 * 2) by omega.
    replace (LogLen xp * 2) with ((LogLen xp - 0) * 2) by omega.
    replace ((LogLen xp - Zlength l) * 2) with (((LogLen xp) - Zlength l - 0) * 2) by omega.
    apply avail_region_grow'; omega.
  Qed.

  Definition log_rep xp m l : pred :=
     ((LogLength xp) |-> Zlength l
      * [[ Zlength l <= LogLen xp ]]
      * [[ valid_log m l ]]
      * logentry_ptsto_list xp l 0
      * avail_region (LogStart xp + Zlength l * 2)
                     (Z.to_nat ((LogLen xp - Zlength l) * 2)))%pred.

  Definition cur_rep (old : mem) (l : log) (cur : mem) : pred :=
    [[ forall a, cur a = replay l old a ]]%pred.

  Definition rep xp (st : logstate) :=
    match st with
      | NoTransaction m =>
        (LogCommit xp) |-> 0
      * data_rep m
      * log_rep xp m nil

      | ActiveTxn old cur =>
        (LogCommit xp) |-> 0
      * data_rep old
      * exists log, log_rep xp old log
      * cur_rep old log cur

      | CommittedTxn cur =>
        (LogCommit xp) |-> 1
      * exists old, data_rep old
      * exists log, log_rep xp old log
      * cur_rep old log cur
    end%pred.

  Ltac log_unfold := unfold rep, data_rep, cur_rep, log_rep.

  Definition init xp rx :=
    (LogLength xp) <-- 0 ;;
    (LogCommit xp) <-- 0 ;;
    rx tt.

  Theorem init_ok : forall xp rx rec,
    {{ exists old F, F
     * data_rep old
     * avail_region (LogStart xp) (Z.to_nat (LogLen xp * 2))
     * (LogCommit xp) |->?
     * (LogLength xp) |->?
     * [[ {{ rep xp (NoTransaction old) * F }} rx tt >> rec ]]
     * [[ {{ any }} rec >> rec ]]
    }} init xp rx >> rec.
  Proof.
    unfold init; log_unfold.
    hoare.
  Qed.

  Definition begin xp rx := (LogLength xp) <-- 0 ;; rx tt.

  Theorem begin_ok : forall xp rx rec,
    {{ exists m F, rep xp (NoTransaction m) * F
     * [[{{ rep xp (ActiveTxn m m) * F }} rx tt >> rec]]
     * [[{{ rep xp (NoTransaction m) * F }} rec >> rec]]
    }} begin xp rx >> rec.
  Proof.
    unfold begin; log_unfold.
    hoare.
  Qed.

  Hint Extern 1 (_ =!=> avail_region _ _) =>
    match goal with
    | [ H: norm_goal (?L ==> ?R) |- _ ] =>
      match L with
      | context[logentry_ptsto_list ?xp ?l _] =>
        eapply pimpl_trans;
        [ apply avail_region_grow_all with (xp:=xp) (l:=l); omega
        | apply eq_pimpl; f_equal; auto; omega ]
      end
    end : norm_hint_right.

  Definition abort xp rx := (LogLength xp) <-- 0 ;; rx tt.

  Theorem abort_ok : forall xp rx rec,
    {{ exists m1 m2 F, rep xp (ActiveTxn m1 m2) * F
     * [[ {{ rep xp (NoTransaction m1) * F }} rx tt >> rec ]]
     * [[ {{ rep xp (NoTransaction m1) * F
          \/ rep xp (ActiveTxn m1 m2) * F }} rec >> rec ]]
    }} abort xp rx >> rec.
  Proof.
    unfold abort; log_unfold.
    hoare.
  Qed.

  Theorem avail_region_shrink_one : forall start len,
    len > 0
    -> avail_region start (Z.to_nat len) ==>
       start |->? * avail_region (start + 1) (Z.to_nat (len - 1)).
  Proof.
    destruct len; intros; try lia.
    destruct (Pos2Nat.is_succ p).
    simpl avail_region at 1.
    rewrite H0.
    simpl avail_region at 1.
    assert (x = Z.to_nat (Z.pos p - 1)) by admit.
    cancel.
  Qed.

  Hint Extern 1 (avail_region _ _ =!=> _) =>
    apply avail_region_shrink_one; omega : norm_hint_left.

  Theorem avail_region_grow_two : forall start len a b,
    len > 1
    -> start |-> a * (start + 1) |-> b
       * avail_region (S (S start)) (Init.Nat.pred (Init.Nat.pred len))
       ==> avail_region start len.
  Proof.
    intros.
    destruct len; try omega.
    destruct len; try omega.
    cancel.
  Qed.

  Hint Extern 1 (_ =!=> avail_region _ ?len) =>
    match goal with
    | [ H: norm_goal (?L ==> ?R) |- _ ] =>
      match L with
      | context[avail_region (S (S ?lstart)) _] =>
        match L with
        | context[(lstart |-> _)%pred] =>
          match L with
          | context[((lstart + 1) |-> _)%pred] =>
            apply avail_region_grow_two with (start:=lstart); omega
          | context[(S lstart |-> _)%pred] =>
            apply avail_region_grow_two with (start:=lstart); omega
          end
        end
      end
    end : norm_hint_right.

  Theorem logentry_ptsto_append' : forall xp l idx a v,
    ((LogStart xp + (length l + idx) * 2) |-> a)
    * ((LogStart xp + (length l + idx) * 2 + 1) |-> v)
    * logentry_ptsto_list xp l idx
    ==> logentry_ptsto_list xp (l ++ (a, v) :: nil) idx.
  Proof.
    induction l; auto; simpl; intros.
    - eapply pimpl_trans; [|eapply pimpl_sep_star;[apply pimpl_refl|apply IHl] ].
      cancel.
  Qed.

  Theorem logentry_ptsto_append : forall xp l a v,
    logentry_ptsto_list xp l 0 * ((LogStart xp + length l * 2) |-> a)
    * ((LogStart xp + length l * 2 + 1) |-> v)
    ==> logentry_ptsto_list xp (l ++ (a, v) :: nil) 0.
  Proof.
    intros.
    eapply pimpl_trans; [|apply logentry_ptsto_append'].
    cancel.
  Qed.

  Hint Extern 1 (_ =!=> logentry_ptsto_list ?xp ?r _) =>
    match goal with
    | [ H: norm_goal (?L ==> ?R) |- _ ] =>
      match L with
      | context[logentry_ptsto_list xp ?l _] =>
        match L with
        | context[((LogStart xp + length l * 2) |-> _)%pred] =>
          match L with
          | context[((LogStart xp + length l * 2 + 1) |-> _)%pred] =>
            match L with
            | context[(LogLength xp |-> S (length l))%pred] =>
              match R with
              (* Make sure this hint does not apply multiple times.. *)
              | context[((LogStart xp + length r * 2) |-> _)%pred] => fail 1
              | context[((LogStart xp + (length l + 1) * 2) |-> _)%pred] => fail 1
              | _ => apply logentry_ptsto_append
              end
            end
          end
        end
      end
    end : norm_hint_right.

  Hint Extern 1 (_ =!=> ?R) =>
    match R with
    | context[length (_ ++ _ :: nil)] => rewrite app_length; apply pimpl_refl
    end : norm_hint_right.

  Definition write xp a v rx :=
    len <- !(LogLength xp);
    If (le_lt_dec (LogLen xp) len) {
      rx false
    } else {
      (LogStart xp + len*2) <-- a;;
      (LogStart xp + len*2 + 1) <-- v;;
      (LogLength xp) <-- (S len);;
      rx true
    }.

  Hint Resolve indomain_replay.
  Hint Resolve replay_app.

  Theorem write_ok : forall xp a v rx rec,
    {{ exists m1 m2 F, rep xp (ActiveTxn m1 m2) * F
     * [[ indomain a m2 ]]
     * [[ {{ rep xp (ActiveTxn m1 (upd m2 a v)) * F }} rx true >> rec ]]
     * [[ {{ rep xp (ActiveTxn m1 m2) * F }} rx false >> rec ]]
     * [[ {{ exists m', rep xp (ActiveTxn m1 m') * F }} rec >> rec ]]
    }} write xp a v rx >> rec.
  Proof.
    unfold write; log_unfold.
    hoare.

    rewrite app_length; simpl; omega.
    apply valid_log_app; simpl; intuition eauto.
    rewrite app_length; simpl; omega.
    apply valid_log_app; simpl; intuition eauto.
  Qed.

  Lemma logentry_ptsto_extract: forall xp pos l idx,
    pos < length l
    -> (logentry_ptsto_list xp l idx ==>
        logentry_ptsto_list xp (firstn pos l) idx *
        ((LogStart xp + (idx+pos) * 2) |-> fst (nth pos l (0, 0))) *
        ((LogStart xp + (idx+pos) * 2 + 1) |-> snd (nth pos l (0, 0))) *
        logentry_ptsto_list xp (skipn (pos+1) l) (idx+pos+1)).
  Proof.
    induction pos; intros.
    - destruct l; simpl in *; try omega.
      unfold logentry_ptsto; destruct l.
      cancel.
    - destruct l; simpl in *; try omega.
      cancel.
      eapply pimpl_trans; [eapply pimpl_trans; [| apply IHpos ]|].
      cancel.
      omega.
      cancel.
  Qed.

  Lemma logentry_ptsto_absorb: forall xp pos l idx,
    pos < length l
    -> (logentry_ptsto_list xp (firstn pos l) idx *
        ((LogStart xp + (idx+pos) * 2) |-> fst (nth pos l (0, 0))) *
        ((LogStart xp + (idx+pos) * 2 + 1) |-> snd (nth pos l (0, 0))) *
        logentry_ptsto_list xp (skipn (pos+1) l) (idx+pos+1) ==>
        logentry_ptsto_list xp l idx).
  Proof.
    induction pos; intros.
    - destruct l; simpl in *; try omega.
      unfold logentry_ptsto; destruct l.
      cancel.
    - destruct l; simpl in *; try omega.
      cancel.
      eapply pimpl_trans; [eapply pimpl_trans; [| apply IHpos]|].
      repeat cancel.
      omega.
      cancel.
  Qed.

  Hint Extern 1 (logentry_ptsto_list ?xp ?log 0 =!=> _) =>
    match goal with
    | [ H: norm_goal (?L ==> ?R) |- _ ] =>
      match R with
      | context[((LogStart xp + ?p * 2) |-> _)%pred] =>
        apply logentry_ptsto_extract with (pos:=p); omega
      end
    end : norm_hint_left.

  Hint Extern 1 (_ =!=> logentry_ptsto_list ?xp ?log 0) =>
    match goal with
    | [ H: norm_goal (?L ==> ?R) |- _ ] =>
      match L with
      | context[((LogStart xp + ?p * 2) |-> _)%pred] =>
        match L with
        | context[logentry_ptsto_list xp (firstn p ?log) 0] =>
          apply logentry_ptsto_absorb with (pos:=p) (l:=log); omega
        end
      end
    end : norm_hint_right.

  Lemma replay_last_eq': forall l i a m,
    i + 1 = length l
    -> fst (nth i l (0, 0)) = a
    -> Some (snd (nth i l (0, 0))) = replay l m a.
  Proof.
    induction l; simpl; intros.
    - omega.
    - destruct a; destruct i.
      + destruct l; simpl in *; try omega.
        rewrite upd_eq; auto.
      + erewrite <- IHl; eauto; omega.
  Qed.

  Lemma firstn_step: forall T (a:T) i l,
    firstn (S i) (a :: l) = a :: firstn i l.
  Proof.
    firstorder.
  Qed.

  Lemma nth_firstn: forall T i l (x:T),
    i < length l
    -> nth i (firstn (S i) l) x = nth i l x.
  Proof.
    induction i.
    - destruct l; simpl; intros; auto; omega.
    - destruct l; auto; intros.
      rewrite firstn_step.
      apply IHi.
      simpl in *; omega.
  Qed.

  Lemma replay_last_eq: forall l i a m,
    i < length l
    -> fst (nth i l (0, 0)) = a
    -> Some (snd (nth i l (0, 0))) = replay (firstn (S i) l) m a.
  Proof.
    intros.
    rewrite <- replay_last_eq' with (i := i).
    - rewrite nth_firstn; auto.
    - destruct l; simpl in *; try omega.
      rewrite firstn_length.
      rewrite Nat.min_l; omega.
    - rewrite nth_firstn; auto.
  Qed.

  Lemma replay_last_ne': forall (e:logentry) l a m,
    fst e <> a
    -> replay l m a = replay (l ++ (e :: nil)) m a.
  Proof.
    destruct e.
    induction l; simpl; intros.
    - rewrite upd_ne; auto.
    - destruct a0.
      apply IHl; auto.
  Qed.

  Lemma firstn_lastone: forall T i l (e:T),
    S i <= length l
    -> firstn (S i) l = firstn i l ++ (nth i l e :: nil).
  Proof.
    induction i.
    - destruct l; simpl; intros; auto; omega.
    - destruct l; intros; [simpl in *; omega | ].
      repeat rewrite firstn_step.
      rewrite <- app_comm_cons.
      f_equal.
      apply IHi.
      simpl in *; omega.
  Qed.

  Lemma replay_last_ne: forall i l m a v,
    i < length l
    -> fst (nth i l (0, 0)) <> a
    -> Some v = replay (firstn i l) m a
    -> Some v = replay (firstn (S i) l) m a.
  Proof.
    intros.
    erewrite firstn_lastone; try omega.
    rewrite <- replay_last_ne'; eauto.
  Qed.

  Lemma firstn_length: forall A (l:list A),
    firstn (length l) l = l.
  Proof.
    induction l; simpl; f_equal; auto.
  Qed.

  Definition read xp a rx :=
    len <- !(LogLength xp);
    v <- !@a;

    v <- For i < len
      Ghost log old cur
      Loopvar v <- v
      Continuation lrx
      Invariant
        (LogCommit xp) |-> 0
        * data_rep old
        * log_rep xp old log
        * cur_rep old log cur
        * [[ Some v = replay (firstn i log) old a ]]
      OnCrash
        rep xp (ActiveTxn old cur)
      Begin
      a' <- !(LogStart xp + i*2);
      If (eq_nat_dec a' a) {
        v <- !(LogStart xp + i*2 + 1);
        lrx v
      } else {
        lrx v
      }
    Rof;

    rx v.

  Theorem read_ok : forall xp a rx rec,
    {{ exists m1 m2 v F, rep xp (ActiveTxn m1 m2) * F
     * [[ m2 @ a |-> v ]]
     * [[ {{ rep xp (ActiveTxn m1 m2) * F }} rx v >> rec ]]
     * [[ {{ rep xp (ActiveTxn m1 m2) * F }} rec >> rec ]]
    }} read xp a rx >> rec.
  Proof.
    unfold read; log_unfold.
    Opaque firstn.

    step.

    eapply pimpl_ok.
    eauto with prog.
    assert (indomain a m) as Ham.
    eapply indomain_replay; eauto.
    unfold indomain; eauto.
    destruct Ham.
    cancel; eauto.

    eapply pimpl_ok.
    eauto with prog.
    norm.
    cancel'.
    intuition.
    (* XXX why is "intuition" unifying existential variables if it runs first?? *)

    hoare.
    hoare.
    rewrite <- plus_n_O in *.
    apply replay_last_eq; auto.
    rewrite <- plus_n_O in *.
    apply replay_last_ne; auto.

    hoare.
    rewrite <- plus_n_O in *.
    rewrite firstn_length in *.
    congruence.

    hoare.
    hoare.
  Qed.

  Definition apply xp rx :=
    len <- !(LogLength xp);
    For i < len
      Ghost log cur
      Loopvar _ <- tt
      Continuation lrx
      Invariant
        (LogCommit xp) |-> 1
        * exists old, data_rep old
        * log_rep xp old log
        * cur_rep old log cur
        * [[ forall a, cur a = replay (skipn i log) old a ]]
      OnCrash
        rep xp (NoTransaction cur) \/
        rep xp (CommittedTxn cur)
      Begin
        a <- !(LogStart xp + i*2);
        v <- !(LogStart xp + i*2 + 1);
        a <--@ v;;
        lrx tt
    Rof;;
    (LogLength xp) <-- 0;;
    (LogCommit xp) <-- 0;;
    rx tt.

  Lemma skipn_length: forall T (l:list T),
    skipn (length l) l = nil.
  Proof.
    induction l; auto.
  Qed.

  Lemma indomain_log_nth: forall l i m, i < length l
    -> valid_log m l
    -> indomain (fst (nth i l (0, 0))) m.
  Proof.
    induction l.
    - simpl; intros; omega.
    - destruct a; destruct i; intros m Hi Hvl; destruct Hvl; auto.
      apply IHl; auto; simpl in *; omega.
  Qed.

  Lemma replay_upd: forall l m0 m1 a v a', replay l m0 a' = replay l m1 a'
    -> replay l (upd m0 a v) a' = replay l (upd m1 a v) a'.
  Proof.
    induction l.
    - simpl; intros; case_eq (eq_nat_dec a a'); intros; subst.
      repeat rewrite upd_eq; auto.
      repeat rewrite upd_ne; auto.
    - destruct a; simpl; intros.
      case_eq (eq_nat_dec a0 a); intros; subst.
      repeat rewrite upd_repeat; auto.
      repeat rewrite upd_comm with (a0:=a0); auto.
  Qed.

  Lemma replay_logupd: forall l m a i, i < length l
    -> replay l (upd m (fst (nth i l (0, 0))) (snd (nth i l (0, 0)))) a = replay l m a.
  Proof.
    induction l.
    - destruct i; simpl; intros; omega.
    - destruct i; destruct a.
      + simpl; intros; f_equal.
        rewrite upd_repeat; auto.
      + simpl; intros.
        apply replay_upd.
        apply IHl.
        omega.
  Qed.

  Lemma skipn_S_cons: forall T (a:T) l i,
    skipn (S i) (a :: l) = skipn i l.
  Proof.
    induction i; auto.
  Qed.

  Lemma replay_skip_more: forall l m a i, i < length l
    -> replay (skipn (S i) l) (upd m (fst (nth i l (0, 0))) (snd (nth i l (0, 0)))) a =
       replay (skipn i l) m a.
  Proof.
    induction l.
    - destruct i; simpl; intros; omega.
    - destruct i; destruct a; simpl; intros; auto.
      destruct l; [simpl in *; omega| ].
      rewrite <- IHl; try omega.
      rewrite skipn_S_cons; auto.
  Qed.

  Hint Extern 1 (_ =!=> LogLength ?xp |-> @length ?T ?l) =>
    match goal with
    | [ H: norm_goal (?L ==> ?R) |- _ ] =>
      match L with
      | context[(LogLength xp |-> 0)%pred] =>
        unify l (@nil T); apply pimpl_refl
      end
    end : norm_hint_right.

  Theorem apply_ok : forall xp rx rec,
    {{ exists m F, rep xp (CommittedTxn m) * F
     * [[ {{ rep xp (NoTransaction m) * F }} rx tt >> rec ]]
     * [[ {{ rep xp (NoTransaction m) * F
          \/ rep xp (CommittedTxn m) * F }} rec >> rec ]]
    }} apply xp rx >> rec.
  Proof.
    unfold apply; log_unfold.
    Opaque skipn.
    step.
    step.

    apply stars_or_right; unfold stars; simpl.
    norm.
    cancel. (* XXX cancel before intuition, otherwise intuition unifies the wrong diskIs *)
    intuition.

    step.
    step.
    step.

    apply indomain_log_nth; auto; omega.

    eapply pimpl_ok.
    eauto with prog.
    norm.
    cancel.
    intuition.
    intuition.
    apply valid_log_upd; auto.
    apply indomain_log_nth; auto; omega.
    rewrite replay_logupd; auto; omega.
    rewrite replay_skip_more; auto; omega.

    step.
    apply stars_or_right; unfold stars; simpl.
    norm.
    cancel.
    intuition.
    intuition.
    congruence.

    apply stars_or_right; unfold stars; simpl.
    norm.
    cancel.
    intuition.
    intuition.
    apply valid_log_upd; auto.
    apply indomain_log_nth; auto.
    rewrite replay_logupd; congruence.

    step.
    apply stars_or_right; unfold stars; simpl.
    norm.
    cancel.
    intuition.
    intuition.
    congruence.

    step.
    apply stars_or_right; unfold stars; simpl.
    norm.
    cancel.
    intuition.
    intuition.
    congruence.

    step.

    rewrite <- plus_n_O in *; rewrite skipn_length in *.

    assert (m1 = m); subst.
    apply functional_extensionality; intros.
    simpl replay in *; congruence.

    step.
    step.
    step.

    rewrite <- plus_n_O in *; rewrite skipn_length in *.

    step.

    apply stars_or_right; unfold stars; simpl.
    norm.
    cancel.
    intuition.
    intuition.
    intuition ( simpl; try omega; try congruence ).

    apply stars_or_right; unfold stars; simpl.
    norm.
    cancel.
    intuition congruence.

    step.
  Qed.

  Hint Extern 1 ({{_}} progseq (apply _) _ >> _) => apply apply_ok : prog.

  Definition commit xp rx :=
    (LogCommit xp) <-- 1;;
    apply xp;;
    rx tt.

  Theorem commit_ok : forall xp rx rec,
    {{ exists m1 m2 F, rep xp (ActiveTxn m1 m2) * F
     * [[ {{ rep xp (NoTransaction m2) * F }} rx tt >> rec ]]
     * [[ {{ rep xp (NoTransaction m2) * F
          \/ rep xp (ActiveTxn m1 m2) * F
          \/ rep xp (CommittedTxn m2) * F }} rec >> rec ]]
    }} commit xp rx >> rec.
  Proof.
    unfold commit; log_unfold.
    step.
    step.
    log_unfold; cancel.
    step.
    log_unfold; cancel.
    log_unfold; cancel.
    apply stars_or_right.
    apply stars_or_right.
    unfold stars; simpl.
    norm.
    cancel.
    intuition.
    step.
  Qed.

  Definition recover xp rx :=
    com <- !(LogCommit xp);
    If (eq_nat_dec com 1) {
      apply xp;;
      rx tt
    } else {
      (LogLength xp) <-- 0;;
      rx tt
    }.

  Theorem recover_ok : forall xp rx rec,
    {{ (exists m F, rep xp (NoTransaction m) * F
        * [[ {{ rep xp (NoTransaction m) * F }} rx tt >> rec ]]
        * [[ {{ rep xp (NoTransaction m) * F }} rec >> rec ]])
    \/ (exists m m' F, rep xp (ActiveTxn m m') * F
        * [[ {{ rep xp (NoTransaction m) * F }} rx tt >> rec ]]
        * [[ {{ rep xp (ActiveTxn m m') * F
             \/ rep xp (NoTransaction m) * F }} rec >> rec ]])
    \/ (exists m F, rep xp (CommittedTxn m) * F
        * [[ {{ rep xp (NoTransaction m) * F }} rx tt >> rec ]]
        * [[ {{ rep xp (CommittedTxn m) * F
             \/ rep xp (NoTransaction m) * F }} rec >> rec ]])
    }} recover xp rx >> rec.
  Proof.
    unfold recover; log_unfold.
    step.

    step.
    step.

    step.
    step.

    step.
    step.
    step.
    step.
    step.

    log_unfold.
    cancel.

    step.
    log_unfold.
    cancel.

    log_unfold.
    apply stars_or_left; unfold stars; simpl.
    norm.
    cancel.
    intuition.

    step.
  Qed.

End Log.
