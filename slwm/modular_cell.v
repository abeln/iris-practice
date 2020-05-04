(* Modular specification of the message passing example from the "Strong Logic for Weak
   Memory paper." *)

From iris.program_logic Require Export hoare weakestpre.
From iris.heap_lang Require Export lang proofmode notation.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import agree frac frac_auth.
From iris.bi.lib Require Import fractional.
From iris.algebra Require Import excl.
From iris.heap_lang.lib Require Import par.

Definition cntCmra : cmraT := (prodR fracR (agreeR (leibnizO Z))).

Class cntG Σ := CntG { CntG_inG :> inG Σ cntCmra }.
Definition cntΣ : gFunctors := #[GFunctor cntCmra ].

Instance subG_cntΣ {Σ} : subG cntΣ Σ → cntG Σ.
Proof. solve_inG. Qed.

Context `{!heapG Σ, !cntG Σ, spawnG Σ} (N : namespace).

Section cell_impl.
  
  Definition new_cell : val := λ: "m", ref "m".
  
  Definition read : val := λ: "l", !"l".

  Definition write : val := λ: "l" "w", "l" <- "w". 
  
End cell_impl.

(* Most of the model lemmas are copied from the modular counter exampke in the
   Iris lecture notes. *)
Section cell_model.

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
  Definition cell_inv ℓ γ := (∃ (m : Z), ℓ ↦ #m ∗ γ ⤇½ m)%I.

  Definition Cell (ℓ : loc) (γ : gname) : iProp Σ :=
    inv (N .@ "internal") (cell_inv ℓ γ).

  Lemma IsCell_Persistent l γ : Persistent (Cell l γ).
  Proof.
    apply _.
  Qed.
  
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
    {{{ Cell ℓ γ ∗ P}}} read #ℓ @ E {{{ (m : Z), RET #m; Q m }}}.
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
        
End cell_impl.

Record abs_cell := AbsCell
  {
    (* Operations *)
    ref_cell : val;
    read_cell : val;
    write_cell : val;

    (* Represeantation predicate *)
    is_cell (ℓ : loc) (γ : gname) : iProp Σ;
   
    is_cell_persistent l γ : Persistent (is_cell l γ);
   
    
    (* Specs *)
    wp_ref_cell (E : coPset) (m : Z) :
      ↑N.@"internal" ⊆ E →
      {{{ True }}} ref_cell #m @ E {{{ (ℓ : loc), RET #ℓ; ∃ γ : gname, is_cell ℓ γ ∗ γ⤇½ m }}};

    
    wp_read_cell (γ : gname) (E : coPset) (P : iProp Σ) (Q : Z → iProp Σ) (ℓ : loc) :
      ↑N.@"internal" ⊆ E →
      (∀ m : Z, (γ⤇½ m ∗ P ={E ∖ ↑N.@"internal"}=> γ⤇½ m ∗ Q m)%stdpp) -∗
      {{{ is_cell ℓ γ ∗ P }}} read_cell #ℓ @ E {{{ (m : Z), RET #m; Q m }}};

    
    wp_write_cell (γ : gname) (E : coPset) (P Q : iProp Σ) (l : loc) (w : Z):
      ↑N.@"internal" ⊆ E →
      (∀ m : Z, (γ⤇½ m ∗ P ={E ∖ ↑N.@"internal"}=> γ⤇½ w ∗ Q)%stdpp) -∗
       {{{ is_cell l γ ∗ P }}} write_cell #l #w @ E {{{ RET #(); Q }}};   
   
  }.

Existing Instances is_cell_persistent.

Definition CellImpl : abs_cell :=
  {|

    ref_cell := new_cell;
    read_cell := read;
    write_cell := write;

    is_cell := Cell;
    is_cell_persistent := IsCell_Persistent;

    wp_ref_cell := new_cell_spec;

    wp_read_cell := read_spec;

    wp_write_cell := write_spec;
    
  |}.

Variable C : abs_cell.

Definition ref_cell' := C.(ref_cell).
Definition read_cell' := C.(read_cell).
Definition write_cell' := C.(write_cell).
Definition is_cell' := C.(is_cell).
Definition is_cell_persistent' := C.(is_cell_persistent).
Definition wp_ref_cell' := C.(wp_ref_cell).
Definition wp_read_cell' := C.(wp_read_cell).
Definition wp_write_cell' := C.(wp_write_cell).

(* Derive sequential specs from abstract specs. *)
Section seq_specs.

  Lemma seq_read_spec (γ : gname) (E : coPset) (l : loc) (n : Z) :
    ↑(N .@ "internal") ⊆ E →
    {{{ γ ⤇½ n ∗ is_cell' l γ }}} read_cell' #l @E {{{ (m : Z), RET #m; ⌜m = n⌝ ∗ γ ⤇½ n }}}.
  Proof.
    iIntros (Hsubset Φ) "[Hγ #Hcell] Hcont".
    wp_apply (wp_read_cell' γ E (γ ⤇½ n) (λ res, (γ ⤇½ n ∗ ⌜res = n⌝)%I) l with "[] [Hγ] [Hcont]"); auto.
    - iIntros (m). iModIntro. iIntros "[Hγ1 Hγ2]".
      iModIntro. iDestruct (makeElem_eq with "Hγ1 Hγ2") as %->. iFrame.
      iPureIntro. reflexivity.
    - iAssert (▷(∀ m : Z, ⌜m = n⌝ ∗  γ⤇½ n  -∗ Φ #m) -∗  ▷(∀ m : Z, γ⤇½ n ∗ ⌜m = n⌝ -∗ Φ #m))%I as "Himpl". {
        iApply bi.later_mono.
        iIntros "Hcont" (m) "[Hγ %]". subst.
        iApply "Hcont". iFrame. iPureIntro. reflexivity.
      }
      iApply "Himpl". done.
  Qed.

  Lemma seq_write_spec (γ : gname) (E : coPset) (l : loc) (n w : Z) :
    ↑(N .@ "internal") ⊆ E →
    {{{ γ ⤇½ n ∗ is_cell' l γ }}} write_cell' #l #w @E {{{RET #(); γ ⤇½ w }}}.
  Proof.
    iIntros (Hns Φ) "[Hγ #Hcell] Hcont".
    wp_apply (wp_write_cell' γ E (γ ⤇½ n) (γ ⤇½ w)%I l w with "[] [Hγ] [Hcont]"); auto.
    iIntros (m). iModIntro. iIntros "[Hm Hn]".
    iDestruct (makeElem_update γ m n w with "Hm Hn") as "Hw".
    iMod "Hw". iModIntro.
    rewrite makeElem_split.
    rewrite own_op. iFrame.
  Qed.

End seq_specs.

Section examples.
  
  (* Demonstrate logical atomicity *)
  Definition par_read : val :=
    λ: <>,
       let: "l" := ref_cell' #0 in
       read_cell' "l";;
       (read_cell' "l" ||| read_cell' "l").


  Definition N_read : namespace := N .@ "read".

  Lemma par_read_helper l γ :
    {{{ is_cell' l γ ∗ inv N_read (γ⤇½ 0) }}} read_cell' #l {{{ v, RET v; ▷ ⌜v = #0⌝ }}}.
  Proof.
    iIntros (Φ) "[#Hcell #Hinv] Hcont".
    wp_apply (wp_read_cell' γ ⊤ True (fun m => (▷ ⌜m = 0⌝)%I) l); auto.
       + iIntros (m). iModIntro.
        iIntros "[Hγ _]".
        iInv N_read as "Hinv2" "Hclose".
        iDestruct (makeElem_eq with "Hγ Hinv2") as "#Hm".        
        iFrame. iFrame "#".
        iApply "Hclose". iFrame.
      + iIntros (m) "Hm".
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
    wp_apply wp_ref_cell'; auto.
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
  
End examples.

Section mp_code.

  (* First we have a function `repeat l`, which reads l until its value is non-zero,
     at which point it returns l's value. *)
  Definition repeat_prog : val :=
    rec: "repeat" "l" :=
      let: "vl" := read_cell' "l" in
      if: "vl" = #0 then ("repeat" "l") else "vl".

  (* Then we have the code for the example. *)
  Definition mp : val :=
    λ: <>,
       let: "x" := ref_cell' #0 in
       let: "y" := ref_cell' #0 in
       let: "res" := ((write_cell' "x" #37;; write_cell' "y" #1) ||| (repeat_prog "y";; read_cell' "x")) in
       Snd "res".

End mp_code.

Section mp_model.
  Definition invN (name : string) := N .@ "inv" .@ name.  
  
  Definition inv_in (γ_in γ : gname) : iProp Σ :=
    (γ_in ⤇½ 37 ∨ own γ (Excl ()))%I.
  
  Definition inv_out (γ_out γ_in γ : gname) : iProp Σ :=
    (γ_out ⤇½ 0 ∨ γ_out ⤇½ 1 ∗ inv (invN "inner") (inv_in γ_in γ))%I.
End mp_model.

Section mp_spec.
  
  Lemma mp_spec :
    {{{ True }}} mp #() {{{ v, RET #v ; ⌜v = 37⌝ }}}.
  Proof.
    iIntros (Φ) "_ HPost".
    rewrite /mp. wp_pures.
    wp_apply (wp_ref_cell'); auto. iIntros (l_x) "Hpre". iDestruct "Hpre" as (γ_x) "[#Hcellx Hx]". wp_pures.    
    wp_apply (wp_ref_cell'); auto. iIntros (l_y) "Hpre". iDestruct "Hpre" as (γ_y) "[#Hcelly Hy]". wp_pures.
    wp_bind (par _ _).
    iMod (own_alloc (Excl ())) as (γ) "Hown".
    { constructor. }    
    iMod (inv_alloc (invN "outer") _ (inv_out γ_y γ_x γ) with "[Hy]") as "#Hinv".
    { iNext. rewrite /inv_out. iLeft. iFrame. }
    wp_apply (wp_par (λ _, True)%I (λ vx, ⌜vx = #37⌝)%I with "[Hinv Hx] [Hinv Hown]").
    - wp_apply (seq_write_spec γ_x _ l_x 0 37 with "[Hx]"); auto. iIntros "Hx".
      iMod (inv_alloc (invN "inner") _ (inv_in γ_x γ) with "[Hx]") as "#Hinv_in".
      { iNext. iLeft. iFrame. }
      wp_apply (wp_write_cell' γ_y _ True True l_y 1); auto.
      iIntros (m). iModIntro.
      iInv (invN "outer") as "[> Hy0 | [> Hy1 _]]" "Hclose".
      (* TODO: clean-up the following two cases  *)
      * iIntros "[Hγ_m _]".
        iDestruct (makeElem_update γ_y 0 m 1 with "Hy0 Hγ_m") as "Hγ1".
        rewrite makeElem_split own_op.
        (* Why is the following step ok? *)
        iMod "Hγ1". iDestruct "Hγ1" as "[Hγ1 Hγ2]".
        iMod ("Hclose" with "[Hinv_in Hγ1]") as "_". 
        iNext; iRight; iFrame; iFrame "#".
        iModIntro. iFrame.
      * iIntros "[Hγ_m _]".
        iDestruct (makeElem_update γ_y 1 m 1 with "Hy1 Hγ_m") as "Hγ1".
        rewrite makeElem_split own_op.
        (* Why is the following step ok? *)
        iMod "Hγ1". iDestruct "Hγ1" as "[Hγ1 Hγ2]".
        iMod ("Hclose" with "[Hinv_in Hγ1]") as "_". 
        iNext; iRight; iFrame; iFrame "#".
        iModIntro. iFrame.
    - wp_bind (repeat_prog _).
      iLöb as "IH".
      rewrite /repeat_prog. wp_pures.
      wp_apply (wp_read_cell' γ_y _ True (λ w, (⌜w = 0⌝ ∨ (⌜w = 1⌝ ∗ ▷ inv (invN "inner") (inv_in γ_x γ)))%I) l_y); auto. {
        iIntros (m). iModIntro. iIntros "[Hγ _]".
        iInv (invN "outer") as "[> Hγ0 | [> Hγ1 #Hinvx]]" "Hclose".
        + iDestruct (makeElem_eq _ _ _ _ _ with "Hγ Hγ0") as %->.
          iMod ("Hclose" with "[Hγ]") as "_". {
            iNext. rewrite /inv_out. iLeft. iFrame.
          }
          iModIntro. iFrame. iLeft. done.
        + iDestruct (makeElem_eq _ _ _ _ _ with "Hγ Hγ1") as %->.
          iMod ("Hclose" with "[Hγ1 Hinvx]") as "_". {
            rewrite /inv_out. iRight. iFrame. iFrame "#".
          }
          iModIntro. iFrame. iRight. rewrite /inv_in.
          iSplitL ""; first by iPureIntro.
          iFrame "#".
      }
      iIntros (m) "[-> | [-> #Hinv_in]]".
      + wp_pure _. wp_pure _. wp_pure _. wp_if.
        iApply "IH". iFrame.
      + wp_pures.
        wp_apply (wp_read_cell' γ_x _ (own γ (Excl ())) (λ w, ⌜w = 37⌝%I) l_x with "[] [Hown] []"); auto.
        * iIntros (m). iModIntro.
          iIntros "[Hx Hown]".
          iInv (invN "inner") as "[> Hγ_in | > Hown2]" "Hclose".
          {
            iDestruct (makeElem_eq _ _ _ _ _ with "Hx Hγ_in") as %->.
            iMod ("Hclose" with "[Hown]") as "_".
            iNext. rewrite /inv_in.  iRight. iFrame.
            iModIntro. iFrame. by iPureIntro.
          }
          {
            iDestruct (own_valid_2 with "Hown Hown2") as %Hvalid.
            exfalso.
            eapply (exclusive_l (Excl ()) (Excl ())).
            assumption.
          }            
        * iNext. iIntros (m) "->"; auto.
    - iIntros (v1 v2) "[_ ->]".
      iNext. wp_pures. iApply "HPost". iPureIntro. reflexivity.
  Qed.
      
End mp_spec.

