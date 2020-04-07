(* Stack with Helping example from the course notes. *)

(* Contains definitions of the weakest precondition assertion, and its basic rules. *)
From iris.program_logic Require Export weakestpre.

(* Instantiation of Iris with the particular language. The notation file
   contains many shorthand notations for the programming language constructs, and
   the lang file contains the actual language syntax. *)
From iris.heap_lang Require Export notation lang.

(* Files related to the interactive proof mode. The first import includes the 
   general tactics of the proof mode. The second provides some more specialized 
   tactics particular to the instantiation of Iris to a particular programming 
   language. *)
From iris.proofmode Require Export tactics.
From iris.heap_lang Require Import proofmode.

(* Definition of invariants and their rules (expressed using the fancy update modality). *)
From iris.base_logic.lib Require Export invariants.

(* The exclusive resource algebra. *)
From iris.algebra Require Import excl.

Context `{!heapG Σ}.
Context `{inG Σ (exclR unitR)}.

Notation iProp := (iProp Σ).

Section offers.

  (*
    An offer is a pair (v, l), where l is a location indicating the status of the offer:
      - 0: this is the initial offer state, when it hasn't been accepted or revoked.
      - 1: this offer has already been accepted by another thread
      - 2: the offer has been revoked by the thread that issued it
   *)

  (* Returns an offer containing the given value *)
  Definition mk_offer : val := λ: "v", ("v", ref #0).

  (* Given an offer (v, _), returns either (Some v) if the offer could be revoked (which
     happens if the offer state is 0), or None otherwise. Sets the offer state to 2. *)
  Definition revoke_offer : val :=
    λ: "off",
      let: "v" := Fst "off" in
      let: "l" := Snd "off" in
      if: (CAS "l" #0 #2) then SOME "v" else NONE.

  (* Given an offer (v, _), return either (Some v) if the offer could be accepted, or None 
     otherwise. Mutates the offer state to 1. *)
  Definition accept_offer : val :=
    λ: "off",
      let: "v" := Fst "off" in
      let: "l" := Snd "off" in
      if: ("CAS" "l" #0 #1) then SOME "v" else NONE.

  (* Offer specification *)

  Variable Φ : val -> iProp. (* The predicate satisfied by the value in the offer. *)

  (* The key to revoking offer γ *)
  Definition offer_key γ := own γ (Excl ()).
  
  (* The following `stages` predicate describes the possible states of the lock
     (and will be later wrapped in an invariant). *)

  Definition stages (v : val) (l : loc) (γ : gname) : iProp :=
    (l ↦ #0 ∗ Φ v) ∨ (l ↦ #1) ∨ (l ↦ #2 ∗ offer_key γ).

  (* The representation predicate for offers. *)
  Definition is_offer (o : val) (γ : gname) : iProp :=
    (∃ (l : loc ) v, ⌜o = (v, #l)%V⌝ ∗ ∃ n, inv n (stages v l γ))%I.

  (* Method specifications *)
  Definition offer_inv : namespace := nroot .@ "offer_inv".

  Lemma wp_mk_offfer v :
    {{{ Φ v }}} mk_offer v {{{ o, RET o; ∃ γ, (offer_key γ) ∗ (is_offer o γ) }}}.
  Proof.
    iIntros (P) "Hpre Hpost".
    iMod (own_alloc (Excl ())) as (γ) "Hown". { constructor. }
    iApply wp_fupd. rewrite /mk_offer. wp_pures. wp_alloc l as "Hl". wp_pures. iApply "Hpost".
    rewrite /is_offer. iExists γ. iFrame. iExists l, v. iSplitL "".
    { by iPureIntro. }
    iExists offer_inv. iApply (inv_alloc offer_inv  _ (stages v l γ)).
    iNext. rewrite /stages. iLeft. iFrame.
  Qed.

  Lemma wp_revoke_offer o γ :
    {{{ is_offer o γ ∗ offer_key γ }}} revoke_offer o {{{ r, RET r; ∃ (v : val ), ⌜r = NONEV⌝ ∨ ⌜r = SOMEV v⌝ ∗ Φ v }}}.
  Proof.
    iIntros (P) "Hpre Hpost".
    iLöb as "#IH".
    rewrite /revoke_offer. wp_pures.
    iDestruct "Hpre" as "[Hpre Hkey]". iDestruct "Hpre" as (l v) "[-> Hpre]".
    iDestruct "Hpre" as (N) "Hpre".
    wp_pures. wp_bind (CmpXchg _ _ _).
    iInv N as "[[> Hl0 HΦ ] | [> Hl1 | [> Hl2 Hghost ]]]" "Hclose".
    - wp_cmpxchg_suc. iMod ("Hclose" with "[Hl0 Hkey]") as "_".
      { iNext. rewrite /stages. iRight. iRight. iFrame. }
      iModIntro. wp_pures.
      iApply "Hpost". iExists v. iRight. iFrame. by iPureIntro.
    - wp_cmpxchg_fail. iMod ("Hclose" with "[Hl1 Hkey]") as "_".
      { iNext. rewrite /stages. iRight. iLeft. iFrame. }
      iModIntro. wp_pures. iApply "Hpost". iExists #(). by iLeft.
    - wp_cmpxchg_fail. iMod ("Hclose" with "[Hl2 Hkey]") as "_".
      { iNext. rewrite /stages. iRight. iRight. iFrame. }
      iModIntro. wp_pures. iApply "Hpost". iExists #(). by iLeft.
  Qed.
        
  
End offers.
