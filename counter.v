(* Monotone counter with client. Adapted from the course notes in the Iris repo:
   https://iris-project.org. Proofs by me.

   Two specs are given:
     - a simpler one using just the authoritative RA.
     - a more-detailed one using the authoritative RA + fractions
*)

(* In this file we explain how to do prove the counter specifications from
   Section 7.7 of the notes. This involves construction and manipulation of
   resource algebras, the explanation of which is the focus of this file. We
   assume the reader has experimented with coq-intro-example-1.v example, and
   thus we do not explain the features we have explained therein already. *)

From iris.program_logic Require Export weakestpre.
From iris.base_logic.lib Require Export invariants.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode.
From iris.heap_lang Require Import notation lang.

From iris.heap_lang.lib Require Import par.

(* The counter module definition. *)
Definition newCounter : val := λ: <>, ref #0.

Definition read : val := λ: "c", !"c".

Definition incr : val :=
  rec: "incr" "c" :=
    let: "n" := !"c" in
    let: "m" := #1 + "n" in
    if: CAS "c" "n" "m" then #() else "incr" "c".
            
(* In the preceding section we spent a lot of time defining our own resource
   algebra and proving it satisfies all the needed properties. The same patterns
   appear often in proof development, and thus the iris Coq library provides
   several building blocks for constructing resource algebras.

   In the following section we repeat the above specification, but with a
   resource algebra constructed using these building blocks. We will see that
   this will save us quite a bit of work.

   As we stated in an exercise in the counter modules section of the lecture
   notes, the resource algebra we constructed above is nothing but Auth(N_max).
   Auth and N_max are both part of the iris Coq library. They are called authR
   and mnatUR (standing for authoritative Resource algebra and max nat Unital
   Resource algebra). *)

(* Auth is defined in iris.algebra.auth. *)
From iris.algebra Require Import auth.

(* The following section is a generic update property of the authoritative construction.
   In the Iris Coq library there are several update lemmas, using the concept of local updates
   (notation x ~l~> y, and the definition is called local_update).
   
   The two updates in the following section are the same as stated in the exercise in the notes.
*)
Section auth_update.
  Context {U : ucmraT}.

  Lemma auth_update_add (x y z : U): ✓ (x ⋅ z) → ● x ⋅ ◯ y ~~> ● (x ⋅ z) ⋅ ◯ (y ⋅ z).
  Proof.
    intros ?.
    (* auth_update is the generic update rule for the auth RA. It reduces a
       frame preserving update to that of a local update. *)
    apply auth_update.
    intros ? mz ? Heq.
    split.
    - apply cmra_valid_validN; auto.
    - simpl in *.
      rewrite Heq.
      destruct mz; simpl; auto.
      rewrite -assoc (comm _ _ z) assoc //.
  Qed.
  
  Lemma auth_update_add' (x y z w : U): ✓ (x ⋅ z) → w ≼ z → ● x ⋅ ◯ y ~~> ● (x ⋅ z) ⋅ ◯ (y ⋅ w).
  Proof.
    (* The proof of this lemma uses the previous lemma, together with the fact
       that ~~> is transitive, and the fact that we always have the frame
       preserving update from a ⋅ b to a. This is proved in cmra_update_op_l in
       the Coq library.
    *)
    intros Hv [? He].
    etransitivity.
    apply (auth_update_add x y z Hv).
    rewrite {2}He assoc auth_frag_op assoc.
    apply cmra_update_op_l.
  Qed.
End auth_update.

Section monotone_counter'.
  (* We tell Coq that our Iris instantiation has the following resource
     algebras. Note that the only diffference from above is that we use authR
     mnatUR in place of the resource algebra mcounterRA we constructed above. *)
  Class mcounterG' Σ := MCounterG' { mcounter_inG' :> inG Σ (authR mnatUR)}.
  Definition mcounterΣ' : gFunctors := #[GFunctor (authR mnatUR)].

  Instance subG_mcounterΣ' {Σ} : subG mcounterΣ' Σ → mcounterG' Σ.
  Proof. solve_inG. Qed.

  (* We now prove the same three properties we claim were required from the resource
     algebra in Section 7.7.  *)
  Instance mcounterRA_frag_core' (n : mnatUR): CoreId (◯ n).
  Proof.
    apply _.
    (* CoreID is a typeclass, so typeclass search can automatically deduce what
       we want. Concretely, the proof follows by lemmas auth_frag_core_id and
       mnat_core_id proved in the Iris Coq library. *)
  Qed.

  Lemma mcounterRA_valid_auth_frag' (m n : mnatUR): ✓ (● m ⋅ ◯ n) ↔ (n ≤ m)%nat.
  Proof.
    (* Use a simplified definition of validity for when the underlying CMRA is discrete, i.e., an RA.
       The general definition also involves the use of step-indices, which is not needed in our case. *)
    rewrite auth_both_valid.
    split.
    - intros [? _]; by apply mnat_included.
    - intros ?%mnat_included; done.
  Qed.

  Lemma mcounterRA_update' (m n : mnatUR): ● m ⋅ ◯ n ~~> ● (S m : mnatUR) ⋅ ◯ (S n : mnatUR).
  Proof.
    replace (S m) with (m ⋅ (S m)); last auto with arith.
    replace (S n) with (n ⋅ (S n)); last auto with arith.
    apply cmra_update_valid0; intros ?%cmra_discrete_valid%mcounterRA_valid_auth_frag'.
    apply auth_update_add'; first reflexivity.
    exists (S m); symmetry; apply max_r; auto with arith.
  Qed.

  (* We can now verify the programs. *)
  (* We start off as in the previous example, with some boilerplate code. *)
  Context `{!heapG Σ, !mcounterG' Σ} (N : namespace).
  Notation iProp := (iProp Σ).

  Definition counter_inv (ℓ : loc) (γ : gname) : iProp :=
    (∃ (m : mnatUR), ℓ ↦ #m ∗ own γ (● m))%I.

  Definition isCounter (ℓ : loc) (n : mnatUR) (γ : gname) : iProp :=
    own γ (◯ n) ∗ inv N (counter_inv ℓ γ)%I.

  Global Instance isCounter_persistent ℓ n γ: Persistent (isCounter ℓ n γ).
  Proof.
    apply _.
  Qed.

  Lemma newCounter_spec: {{{ True }}} newCounter #() {{{ v, RET #v; ∃ γ, isCounter v 0%nat γ }}}.
  Proof.
    iIntros (Φ) "_ HCont".
    iApply wp_fupd.
    iPoseProof (own_alloc (● (0%nat : mnatUR) ⋅ ◯ (0%nat : mnatUR)))%I as "Halloc".
    - apply mcounterRA_valid_auth_frag'. lia.
    - iMod "Halloc" as (γ) "[Hauth Hpart]".  
      unfold newCounter. wp_pures. wp_alloc ℓ as "Hl".
      iApply "HCont".
      unfold isCounter. unfold counter_inv.
      iExists γ. iFrame.
      iMod (inv_alloc N _ (∃ m : mnatUR, ℓ ↦ #m ∗ own γ (● m)) with "[Hauth Hl]") as "Hinv".
                * iNext. iExists 0%nat. iFrame.
                * iModIntro. iFrame.
  Qed.                  

 Lemma read_spec ℓ n γ  : {{{ isCounter ℓ n γ }}} read #ℓ {{{ m, RET #m; ⌜n ≤ m⌝ }}}.
 Proof.
   iIntros (Φ) "Hcounter Hcont".
   unfold read. wp_lam.
   unfold isCounter. iDestruct "Hcounter" as "[Hown Hinv]".
   unfold counter_inv.
   iInv "Hinv" as (m) "> [Hl Hauth]" "Hclose".
   wp_load.
   iPoseProof (own_valid_2 with "Hauth Hown") as "%".
   pose proof (iffLR (mcounterRA_valid_auth_frag' m n) H).
   iMod ("Hclose" with "[Hl Hauth]") as "_".
   - iNext. iExists m. iFrame.
   - iModIntro. iApply "Hcont"; auto.
 Qed.

 Lemma incr_spec ℓ n γ : {{{ isCounter ℓ n γ }}} incr #ℓ {{{ RET #(); isCounter ℓ (n + 1)%nat γ }}}.
 Proof.
   iIntros (Φ) "Hcounter Hcont".
   unfold isCounter.
   iDestruct "Hcounter" as "[Hnon #Hinv]".
   (* We need Lob induction because this is a recursive function. *)
   iLöb as "IH".
   (* Before opening the invariant, we need to get to an atomic operation. *)
   rewrite /incr. wp_lam. wp_bind (! _)%E.
   iInv N as (m) "> [Hpt HAuth]" "Hclose".
   wp_load.
   (* We now need to combine the auth and non-auth resources, so we can link the 
      logical and physical states. *)
   iPoseProof (own_valid_2 with "HAuth Hnon") as "%".
   pose proof (iffLR (mcounterRA_valid_auth_frag' m n) H).
   (* Now we can close the invariant. *)
   iMod ("Hclose" with "[Hpt HAuth]") as "_".
   - iNext. rewrite /counter_inv. iExists m. iFrame.
   - iModIntro.
     wp_pures. wp_bind (CmpXchg _ _ _)%E.          
     iInv N as (m') "> [Hpt HAuth]" "Hclose".
     (* Can open the invariant and consider two cases: the new value is the same as the old read, or not. *)     
     destruct (decide ((m = m'))); subst.
     * wp_cmpxchg_suc.
       iMod (own_update γ (● m' ⋅ ◯ n) (● (S m' : mnatUR) ⋅ ◯ (S n : mnatUR)) with "[HAuth Hnon]") as "Hsucc".
       { apply mcounterRA_update'. }
       { rewrite own_op. iFrame. }
       rewrite own_op.
       iDestruct "Hsucc" as "[Hauth Hnon]".
       iAssert (counter_inv ℓ γ) with "[Hauth Hpt]" as "Hcounter". {
         unfold counter_inv. iExists (1 + m')%nat.
         rewrite Z.add_1_l. rewrite <- Nat2Z.inj_succ.
         iFrame.
       }
       iMod ("Hclose" with "Hcounter") as "_".
       iModIntro.
       wp_pures.
       iApply "Hcont".
       rewrite Nat.add_1_r; iFrame; auto.
     * wp_cmpxchg_fail.
       { 
         injection. intros Heq.
         apply n0. apply Nat2Z.inj. auto. }
       iMod ("Hclose" with "[HAuth Hpt]") as "_".
       { unfold counter_inv.
         iNext. iExists m'%nat. iFrame.
       }
       iModIntro.
       wp_proj. wp_if.
       iApply ("IH" with "Hnon Hcont" ).
 Qed.
 
  Definition client : val :=
   λ: <>,
     let: "c" := newCounter #() in
     ((incr "c") ||| (incr "c")) ;;
     read "c".                            

  Context `{!spawnG Σ}.

  Lemma client_spec : {{{ True }}} client #()  {{{n, RET #n ; ⌜n ≥ 1⌝ }}}.
  Proof.
    iIntros (ϕ) "_ Hcont".
    unfold client. wp_pures. wp_bind (newCounter _).
    wp_apply newCounter_spec; auto.
    iIntros (v) "#Hc". iDestruct "Hc" as (γ) "Hc"; 
    wp_apply (wp_par (λ _, isCounter v 1 γ)%I (λ _, isCounter v 1 γ)%I);
    try wp_apply (incr_spec with "Hc"); auto.
    iIntros (? ?) "[Hc1 Hc2]". iNext. wp_pures.
    wp_apply (read_spec v 1 with "Hc1").
    iApply "Hcont".
  Qed.
  
End monotone_counter'.

(* Counter with contributions. *)
(* As a final example in this example file we give the more precise specification to the counter. *) 
(* As explained in the lecture notes we need a different resource algebra: the
   authoritative resource algebra on the product of the RA of fractions and the
   RA of natural numbers, with an added unit.

   The combination of the RA of fractions and the authoritative RA in this way
   is fairly common, and so the Iris Coq library provides frac_authR (CM)RA. *)

From iris.algebra Require Import frac_auth.

Section ccounter.
  (* We start as we did before, telling Coq what we assume from the Iris instantiation. *)
  (* Note that now we use natR as the underlying resource algebra. This is the
     RA of natural numbers with addition as the operation. *)
  Class ccounterG Σ := CCounterG { ccounter_inG :> inG Σ (frac_authR natR) }.
  Definition ccounterΣ : gFunctors := #[GFunctor (frac_authR natR)].

  Instance subG_ccounterΣ {Σ} : subG ccounterΣ Σ → ccounterG Σ.
  Proof. solve_inG. Qed.

  (* The first thing we are going to prove are the properties of the resource
     algebra, specialized to our use case. These are listed in the exercise in
     the relevant section of the lecture notes. *)
  (* We are using some new notation. The frac_auth library defines the notation
     ◯F{q} n to mean ◯ (q, n) as we used in the lecture notes. Further, ●F m
     means ● (1, m) and ◯F n means ◯ (1, n). *)
  Lemma ccounterRA_valid (m n : natR) (q : frac): ✓ (●F m ⋅ ◯F{q} n) → (n ≤ m)%nat.
  Proof.
    intros ?.
      (* This property follows directly from the generic properties of the relevant RAs. *)

    by apply nat_included, (frac_auth_included_total q).
  Qed.

  Lemma ccounterRA_valid_full (m n : natR): ✓ (●F m ⋅ ◯F n) → (n = m)%nat.
  Proof.
    by intros ?%frac_auth_agree.
  Qed.

  Lemma ccounterRA_update (m n : natR) (q : frac): (●F m ⋅ ◯F{q} n) ~~> (●F (S m) ⋅ ◯F{q} (S n)).
  Proof.
    apply frac_auth_update, (nat_local_update _ _ (S _) (S _)).
    lia.
  Qed.

  (* We have all the properties of the RAs needed and thus we can proceed with
     the proof, which proceeds largely as before, modulo the changes in
     invariants.

     There is one important difference in the definition of is_ccounter. The
     ghost name γ is not hidden. This is because now is_ccounter is not
     persistent, and to share it we have the is_ccounter_op lemma, which would
     not hold if we were to existentially quantify γ as we did in the previous
     examples.
  *)
  Context `{!heapG Σ, !ccounterG Σ} (N : namespace).

  
  Program Definition ccounter_inv (γ : gname) (l : loc) : iProp Σ :=
    (∃ m : natR,  own γ (●F m) ∗ l ↦ #m)%I.
  
  Definition is_ccounter (γ : gname) (l : loc) (q : frac) (n : natR) : iProp Σ :=
    ((own γ (◯F{q} n)) ∗ inv N (ccounter_inv γ l))%I.

    (** The main proofs. *)

  (* As explained in the notes the is_ccounter predicate for this specificatin is not persistent.
     However it is still shareable in the following restricted way.
   *)
  Lemma is_ccounter_op γ ℓ q1 q2 (n1 n2 : nat) :
    is_ccounter γ ℓ (q1 + q2) (n1 + n2)%nat ⊣⊢ is_ccounter γ ℓ q1 n1 ∗ is_ccounter γ ℓ q2 n2.
  Proof.
    apply bi.equiv_spec; split; rewrite /is_ccounter frac_auth_frag_op own_op.
    - iIntros "[? #?]".
      iFrame "#". iFrame.
    - iIntros "[[? #?] [? _]]".
      iFrame "#". iFrame.
  Qed.

  Lemma newCounter_cc_spec :
    {{{ True }}}
      newCounter #()
    {{{ ℓ, RET #ℓ; ∃ γ, is_ccounter γ ℓ 1 0%nat }}}.
  Proof.
    iIntros (Φ) "_ Hϕ".
    iApply wp_fupd.
    rewrite /newCounter. wp_pures. wp_alloc l as "Hc".
    iApply "Hϕ".
    rewrite /is_ccounter. rewrite /ccounter_inv.
    iMod (own_alloc (●F 0%nat ⋅ ◯F 0%nat)) as (γ) "[Hauth Hnon]"; first by apply auth_both_valid. 
    iExists γ.
    iFrame.
    iPoseProof (inv_alloc N _ (ccounter_inv γ l)) as "Hinv".
    iAssert (ccounter_inv γ l) with "[Hc Hauth]" as "Hcounterinv". {
      rewrite /ccounter_inv.
      iExists 0.
      iFrame.
    }
    iApply "Hinv". iNext. done.
  Qed.

  Lemma incr_cc_spec γ ℓ p n :
    {{{ is_ccounter γ ℓ p n  }}}
      incr #ℓ
    {{{ RET #(); is_ccounter γ ℓ p (S n)  }}}.
  Proof.
    iIntros (Φ) "Hc Hϕ".
    iLöb as "IH".
    rewrite /incr. wp_pures.
    rewrite /is_ccounter. iDestruct "Hc" as "[Hnon Hinv]".
    wp_bind (! _)%E.
    iDestruct "Hinv" as "#Hinv".
    iInv N as (v) "[Hℓ Hauth]" "Hclose".
    wp_load.
    iMod ("Hclose" with "[Hauth Hℓ]") as "_".
    { iNext. rewrite /ccounter_inv. iExists v. iFrame. }
    iModIntro. wp_pures.
    wp_bind (CmpXchg _ _ _).
    iInv N as (v') "[Hauth Hℓ]" "Hclose".
    destruct (decide (v' = v)).
    - wp_cmpxchg_suc. rewrite e.
      iAssert (own γ ((◯F{p} n) ⋅ (●F v))) with "[Hnon Hauth]" as "Hown".
      { iApply own_op; iFrame. }
      (* iAssert (✓ (◯F{p} n ⋅ ●F v))%I with "[Hown]" as "%".
      { iApply own_valid. done. } *)
      (* pose proof (ccounterRA_valid _ _ _ H) as Rs. *)
      iPoseProof (own_update _ (◯F{p} n ⋅ ●F v) (◯F{p} (S n) ⋅ ●F (S v)) with "Hown") as "Hnext".
      { apply ccounterRA_update. }
      iMod "Hnext" as "[Hnon Hauth]".
      iAssert (ccounter_inv γ ℓ) with "[Hauth Hℓ]" as "Hinv_all".
      { rewrite /ccounter_inv.  iExists (1 + v)%nat.
        iFrame. rewrite Nat2Z.inj_succ Z.add_1_l. done. }
      iMod ("Hclose" with "Hinv_all") as "_".
      iModIntro.
      wp_pures.
      iApply "Hϕ". iFrame "#". iFrame.
    - wp_cmpxchg_fail.
      { intros Heq.
        inversion Heq.
        apply Nat2Z.inj in H0.
        auto. }              
      iMod ("Hclose" with "[Hℓ Hauth]").
      { iNext. rewrite /ccounter_inv.
        iExists v'. iFrame. }
      iModIntro. wp_proj. wp_if.
      fold incr.
      iApply ("IH" with "[Hnon] Hϕ" ).
      iFrame. iFrame "#".
  Qed.

  Lemma read_cc_spec γ ℓ p n :
    {{{ is_ccounter γ ℓ p n }}}
      read #ℓ
    {{{ v, RET #v; ⌜n ≤ v⌝%nat ∧ is_ccounter γ ℓ p n }}}.
  Proof.
    iIntros (ϕ) "Hpre Hϕ".
    rewrite /read. wp_pures.
    rewrite /is_ccounter.
    iDestruct "Hpre" as "[Hown #Hinv]".
    iInv N as (m) "[Hauth Hℓ]" "Hclose".
    wp_load.
    iPoseProof (own_valid_2 with "Hauth Hown") as "%".
    eapply ccounterRA_valid in H.
    iMod ("Hclose" with "[Hauth Hℓ]").
    { rewrite /ccounter_inv. iExists m. iFrame. }
    iApply "Hϕ". iModIntro. iSplit.
    - iPureIntro. assumption.
    - iFrame. iFrame "#".
  Qed.

   Lemma read_cc_spec2 γ ℓ n :
    {{{ is_ccounter γ ℓ 1 n }}}
      read #ℓ
    {{{ v, RET #v; ⌜n = v⌝%nat ∧ is_ccounter γ ℓ 1 n }}}.
   Proof.
    iIntros (ϕ) "Hpre Hϕ".
    rewrite /read. wp_pures.
    rewrite /is_ccounter.
    iDestruct "Hpre" as "[Hown #Hinv]".
    iInv N as (m) "[Hauth Hℓ]" "Hclose".
    wp_load.
    iPoseProof (own_valid_2 with "Hauth Hown") as "%".
    eapply ccounterRA_valid_full in H.
    iMod ("Hclose" with "[Hauth Hℓ]").
    { rewrite /ccounter_inv. iExists m. iFrame. }
    iApply "Hϕ". iModIntro. iSplit.
    - iPureIntro. assumption.
    - iFrame. iFrame "#".
  Qed.

  Context `{!spawnG Σ}.
   
  Lemma client_spec2 : {{{ True }}} client #()  {{{n, RET #n ; ⌜n ≥ 2⌝ }}}.
  Proof.
    iIntros (ϕ) "_ Hcont".
    unfold client. wp_pures. wp_bind (newCounter _).
    wp_apply newCounter_cc_spec; auto.
    iIntros (ℓ) "Hc". iDestruct "Hc" as (γ) "Hc".
    assert (1%Qp = (1 / 2 + 1 / 2)%Qp) as ->.  {
      rewrite Qp_half_half.
      reflexivity.
    }
    assert (0 = 0 + 0) as -> by auto.   
    rewrite is_ccounter_op.
    iDestruct "Hc" as "[Hc1 Hc2]".
    wp_apply (wp_par (λ _, is_ccounter γ ℓ (1 / 2)%Qp 1)%I (λ _, is_ccounter γ ℓ (1 / 2)%Qp 1)%I with "[Hc1] [Hc2]").
    - wp_apply (incr_cc_spec with "Hc1" ).
      iIntros "Hc". done.
    - wp_apply (incr_cc_spec with "Hc2" ).
      iIntros "Hc". done.
    - iIntros (v1 v2) "Hc".
      iNext. wp_pures.
      rewrite <- is_ccounter_op.
      assert (1 + 1 = 2) as -> by auto.
      assert ((1 / 2 + 1 / 2)%Qp = 1%Qp) as Heq by apply Qp_half_half.
      rewrite Heq.
      wp_apply (read_cc_spec2 with "Hc").
      iIntros (v) "[% Hc]".
      iApply "Hcont". iPureIntro.
      rewrite H. auto.
Qed.
                   
End ccounter.
