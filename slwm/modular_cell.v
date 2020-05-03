(* Modular Specifications for Concurrent Modules. *)

From iris.program_logic Require Export hoare weakestpre.
From iris.heap_lang Require Export lang proofmode notation.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import agree frac frac_auth.

From iris.bi.lib Require Import fractional.

From iris.heap_lang.lib Require Import par.

Definition cntCmra : cmraT := (prodR fracR (agreeR (leibnizO Z))).

Class cntG Σ := CntG { CntG_inG :> inG Σ cntCmra }.
Definition cntΣ : gFunctors := #[GFunctor cntCmra ].

Instance subG_cntΣ {Σ} : subG cntΣ Σ → cntG Σ.
Proof. solve_inG. Qed.

Section cell_impl.
  
  Definition new_cell : val := λ: "m", ref "m".
  
  Definition read : val := λ: "l", !"l".

  Definition write : val := λ: "l" "w", "l" <- "w". 
  
End cell_impl.



Section cell_model.
  Context `{!cntG Σ}.

  Definition makeElem (q : Qp) (m : Z) : cntCmra := (q, to_agree m).

  Notation "γ ⤇[ q ] m" := (own γ (makeElem q m))
    (at level 20, q at level 50, format "γ ⤇[ q ]  m") : bi_scope.
  Notation "γ ⤇½ m" := (own γ (makeElem (1/2) m))
    (at level 20, format "γ ⤇½  m") : bi_scope.

  Global Instance makeElem_fractional γ m: Fractional (λ q, γ ⤇[q] m)%I.
  Proof.
    intros p q. rewrite /makeElem.
    rewrite -own_op; f_equiv.
    split; first done.
    by rewrite /= agree_idemp.
  Qed.

  Global Instance makeElem_as_fractional γ m q:
    AsFractional (own γ (makeElem q m)) (λ q, γ ⤇[q] m)%I q.
  Proof.
    split. done. apply _.
  Qed.

  Global Instance makeElem_Exclusive m: Exclusive (makeElem 1 m).
  Proof.
    intros [y ?] [H _]. apply (exclusive_l _ _ H).
  Qed.

  Lemma makeElem_op p q n:
    makeElem p n ⋅ makeElem q n ≡ makeElem (p + q) n.
  Proof.
    rewrite /makeElem; split; first done.
    by rewrite /= agree_idemp.
  Qed.

  Lemma makeElem_split n:
    makeElem 1 n ≡ makeElem (1/2)%Qp n ⋅ makeElem (1/2)%Qp n.
  Proof.
    rewrite makeElem_op.
    rewrite /makeElem. split.
    - simpl. apply Qp_eq. rewrite Qp_div_2. reflexivity.                            
    - simpl. reflexivity.
  Qed.

  Lemma makeElem_eq γ p q (n m : Z):
    γ ⤇[p] n -∗ γ ⤇[q] m -∗ ⌜n = m⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %HValid.
    destruct HValid as [_ H2].
    iIntros "!%"; by apply agree_op_invL'.
  Qed.

  Lemma makeElem_entail γ p q (n m : Z):
    γ ⤇[p] n -∗ γ ⤇[q] m -∗ γ ⤇[p + q] n.
  Proof.
    iIntros "H1 H2".
    iDestruct (makeElem_eq with "H1 H2") as %->.
    rewrite -makeElem_op.
    rewrite own_op.
    iFrame.
  Qed.

  Lemma makeElem_update γ (n m k : Z):
    γ ⤇½ n -∗ γ ⤇½ m ==∗ γ ⤇[1] k.
  Proof.
    iIntros "H1 H2".
    iDestruct (makeElem_entail with "H1 H2") as "H".
    rewrite Qp_div_2.
    iApply (own_update with "H"); by apply cmra_update_exclusive.
  Qed.
End cell_model.

Notation "γ ⤇[ q ] m" := (own γ (makeElem q m))
  (at level 20, q at level 50, format "γ ⤇[ q ]  m") : bi_scope.
Notation "γ ⤇½ m" := (own γ (makeElem (1/2) m))
  (at level 20, format "γ ⤇½  m") : bi_scope.

Section cell_impl.
  Context `{!heapG Σ, !cntG Σ, spawnG Σ} (N : namespace).

  Definition cell_inv ℓ γ := (∃ (m : Z), ℓ ↦ #m ∗ γ ⤇½ m)%I.

  Definition Cell (ℓ : loc) (γ : gname) : iProp Σ :=
    inv (N .@ "internal") (cell_inv ℓ γ).

  
  Lemma Cell_alloc (E : coPset) (m : Z) (ℓ : loc):
    (ℓ ↦ #m) ={E}=∗ ∃ γ, Cell ℓ γ ∗ γ ⤇½ m.
  Proof.
    iIntros "Hpt".
    iMod (own_alloc (makeElem 1 m)) as (γ) "[Hown1 Hown2]"; first done.
    iMod (inv_alloc (N.@ "internal") _ (cell_inv ℓ γ)%I with "[Hpt Hown1]") as "#HInc".
    { iExists _; iFrame. }
    iModIntro; iExists _; iFrame "# Hown2".
  Qed.

  Theorem new_cell_spec (E : coPset) (m : Z):
    ↑(N .@ "internal") ⊆ E →
    {{{ True }}} new_cell #m @ E {{{ (ℓ : loc), RET #ℓ; ∃ γ, Cell ℓ γ ∗ γ ⤇½ m}}}.
  Proof.
    iIntros (Hsubset Φ) "_ HΦ".
    wp_apply wp_fupd.
    wp_lam.
    wp_alloc ℓ as "Hl".
    iApply "HΦ".
    by iApply Cell_alloc.
  Qed.

  Theorem read_spec (γ : gname) (E : coPset) (P : iProp Σ) (Q : Z → iProp Σ) (ℓ : loc):
    ↑(N .@ "internal") ⊆ E →
    (∀ m, (γ ⤇½ m ∗ P ={E ∖ ↑(N .@ "internal")}=> γ ⤇½ m ∗ Q m)) ⊢
    {{{ Cell ℓ γ ∗ P}}} read #ℓ @ E {{{ (m : Z), RET #m; Cell ℓ γ ∗ Q m }}}.
  Proof.
    iIntros (Hsubset) "#HVS".
    iIntros (Φ) "!# [#HInc HP] HCont".
    wp_rec.
    rewrite /Cell.
    iInv (N .@ "internal") as (m) "[>Hpt >Hown]" "HClose".
    iMod ("HVS" $! m with "[Hown HP]") as "[Hown HQ]"; first by iFrame.
    wp_load.
    iMod ("HClose" with "[Hpt Hown]") as "_".
    { iNext; iExists _; iFrame. }
    iApply "HCont".
    iModIntro.
    iFrame.
    done.
  Qed.

  Lemma seq_read_spec (γ : gname) (E : coPset) (l : loc) (n : Z) :
    ↑(N .@ "internal") ⊆ E →
    {{{ γ ⤇½ n ∗ Cell l γ }}} read #l @E {{{ (m : Z), RET #m; ⌜m = n⌝ ∗ γ ⤇½ n }}}.
  Proof.
    iIntros (Hsubset Φ) "[Hγ Hcell] Hcont".
    wp_apply (read_spec γ E (γ ⤇½ n) (λ res, (γ ⤇½ n ∗ ⌜res = n⌝)%I) l with "[] [Hγ Hcell] [Hcont]"); auto.
    - iIntros (m). iModIntro. iIntros "[Hγ1 Hγ2]".
      iModIntro. iDestruct (makeElem_eq with "Hγ1 Hγ2") as %->. iFrame.
      iPureIntro. reflexivity.
    - iAssert (▷(∀ m : Z, ⌜m = n⌝ ∗  γ⤇½ n  -∗ Φ #m) -∗  ▷(∀ m : Z, Cell l γ ∗ γ⤇½ n ∗ ⌜m = n⌝ -∗ Φ #m))%I as "Himpl". {
        iApply bi.later_mono.
        iIntros "Hcont" (m) "[Hcell [Hγ %]]". subst.
        iApply "Hcont". iFrame. iPureIntro. reflexivity.
      }
      iApply "Himpl". done.
  Qed.

  Lemma write_spec (γ : gname) (E : coPset) (P Q : iProp Σ) (l : loc) (w : Z) :
    ↑(N .@ "internal") ⊆ E ->
    (∀ m, (γ ⤇½ m ∗ P ={E ∖ ↑(N .@ "internal")}=> γ ⤇½ w ∗ Q)) ⊢
    {{{ Cell l γ ∗ P }}} write #l #w @E {{{ RET #(); Q }}}.
  Proof.
    iIntros (Hnamespace) "#Hvs". iModIntro. iIntros (Φ) "[Hcell HP] Hcont".
    rewrite /write. wp_pures. rewrite /Cell.
    iInv (N .@ "internal") as (m') "[>Hpt >Hown]" "Hclose".
    iMod ("Hvs" $! m' with "[Hown HP]") as "[Hown HQ]"; first by iFrame.
    wp_store.
    iMod ("Hclose" with "[Hown Hpt]") as "_". {
      iNext. rewrite /cell_inv. iExists w. iFrame.
    }
    iModIntro. iApply "Hcont". iFrame.
  Qed.

  Lemma seq_write_spec (γ : gname) (E : coPset) (l : loc) (n w : Z) :
    ↑(N .@ "internal") ⊆ E →
    {{{ γ ⤇½ n ∗ Cell l γ }}} write #l #w @E {{{RET #(); γ ⤇½ w }}}.
  Proof.
    iIntros (Hns Φ) "[Hγ #Hcell] Hcont".
    wp_apply (write_spec γ E (γ ⤇½ n) (γ ⤇½ w)%I l w with "[] [Hγ] [Hcont]"); auto.
    iIntros (m). iModIntro. iIntros "[Hm Hn]".
    iDestruct (makeElem_update γ m n w with "Hm Hn") as "Hw".
    iMod "Hw". iModIntro.
    rewrite makeElem_split.
    rewrite own_op. iFrame.
  Qed.
    
  (* Demonstrate logical atomicity *)
  Definition par_read : val :=
    λ: <>,
       let: "l" := new_cell #0 in
       read "l";;
            (read "l" ||| read "l").


  Definition N_read : namespace := N .@ "read".

  Lemma par_read_helper l γ :
    {{{ Cell l γ ∗ inv N_read (γ⤇½ 0) }}} read #l {{{ v, RET v; ▷ ⌜v = #0⌝ }}}.
  Proof.
    iIntros (Φ) "[#Hcell #Hinv] Hcont".
    wp_apply (read_spec γ ⊤ True (fun m => (▷ ⌜m = 0⌝)%I) l); auto.
       + iIntros (m). iModIntro.
        iIntros "[Hγ _]".
        iInv N_read as "Hinv2" "Hclose".
        iDestruct (makeElem_eq with "Hγ Hinv2") as "#Hm".        
        iFrame. iFrame "#".
        iApply "Hclose". iFrame.
      + iIntros (m) "[_ Hm]".
        iAssert ( ▷ ⌜m = 0⌝ -∗  ▷ ⌜#m = #0⌝)%I as "Hm0". {
          iApply bi.later_mono. iIntros "->". done.
        }
        iApply "Hcont".
        iApply "Hm0". done.
  Qed.
  
  Lemma par_read_spec :
    {{{ True }}} par_read #() {{{ RET (#0, #0); True }}}.
  Proof.
    iIntros (ϕ) "_ Hcont".
    rewrite /par_read. wp_pures.
    wp_apply new_cell_spec; auto.
    iIntros (l) "Hpre". iDestruct "Hpre" as (γ) "[#Hcell Hγ]".
    wp_pures.    
    (* Use the sequential spec *)
    wp_apply (seq_read_spec with "[Hcell Hγ] [Hcont]"); auto.
    iNext. iIntros (m) "[% Hγ]". subst.
    wp_pures.
    (* Put ghost state in inv *)
    iMod (inv_alloc N_read _ (γ⤇½ 0) with "Hγ") as "#Hinv".
    (* Use the general spec *)
    wp_apply (wp_par (λ v, ▷ ⌜v = #0⌝)%I (λ v, ▷ ⌜v = #0⌝)%I).
    (* TODO: clean-up both branches, since they're the same *)
    - wp_apply par_read_helper.
      + iFrame "#".
      + by iIntros (v) "Hv". 
    - wp_apply par_read_helper.
      + iFrame "#".
      + by iIntros (v) "Hv".         
    - iIntros (v1 v2) "[Hv1 Hv2]".
      (* TODO: clean-up below *)
      iDestruct (timeless with "Hv1") as "H1". unfold sbi_except_0. iDestruct "H1" as "[H1|->]"; auto. 
      iDestruct (timeless with "Hv2") as "H2". unfold sbi_except_0. iDestruct "H2" as "[H2|->]"; auto.
      iNext. iApply "Hcont". auto.
  Qed.

        
End cell_impl.

