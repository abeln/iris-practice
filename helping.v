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
      if: (CAS "l" #0 #1) then SOME "v" else NONE.

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

  (* When we create an offer, we get the offer and also the key to revoke it. *)
  Lemma wp_mk_offer v :
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

  (* To revoke an offer, we need its key. *)
  Lemma wp_revoke_offer o γ :
    {{{ is_offer o γ ∗ offer_key γ }}} revoke_offer o {{{ r, RET r; ∃ (v : val ), ⌜r = NONEV⌝ ∨ ⌜r = SOMEV v⌝ ∗ Φ v }}}.
  Proof.
    iIntros (P) "Hpre Hpost".
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

  Lemma wp_accept_offer o γ :
    {{{ is_offer o γ }}} accept_offer o {{{ r, RET r; ∃ v, ⌜r = NONEV⌝ ∨ ⌜r = SOMEV v⌝ ∗ Φ v }}}.
    iIntros (P) "Hpre Hpost".
    rewrite /accept_offer. wp_pures.
    iDestruct "Hpre" as (l v) "[-> Hpre]". iDestruct "Hpre" as (N) "Hpre".
    wp_pures. wp_bind (CmpXchg _ _ _).
    iInv N as "[[> Hl0 HΦ ] | [> Hl1 | [> Hl2 Hghost ]]]" "Hclose".
    - wp_cmpxchg_suc. iMod ("Hclose" with "[Hl0]") as "_".
      { iNext. rewrite /stages. iRight. iLeft. iFrame. }
      iModIntro. wp_pures.
      iApply "Hpost". iExists v. iRight. iFrame. by iPureIntro.
    - wp_cmpxchg_fail. iMod ("Hclose" with "[Hl1]") as "_".
      { iNext. rewrite /stages. iRight. iLeft. iFrame. }
      iModIntro. wp_pures. iApply "Hpost". iExists #(). by iLeft.
    - wp_cmpxchg_fail. iMod ("Hclose" with "[Hl2 Hghost]") as "_".
      { iNext. rewrite /stages. iRight. iRight. iFrame. }
      iModIntro. wp_pures. iApply "Hpost". iExists #(). by iLeft.
  Qed.
      
End offers.

Section mailbox.

  (* Returns a pair of two closures: the first component is for putting an offer in the mailbox
     The second is for getting an offer out of the mailbox. *)
  Definition mk_mailbox : val :=
    λ: <>,
       let: "r" := ref NONEV in

       (* Returns (Some v) if the element was not taken by someone else, or None if
          another thread accepted the offer. *)
       let: "put" :=
         (λ: "v",
           let: "o" := mk_offer "v" in
           "r" <- SOME "o";;
           revoke_offer "o")
       in

       (* Returns (Some v) if we were able to get an element from the mailbox, and
          None otherwise. *)
       let: "get" :=
         (λ: "v",
           match: !"r" with
             NONE => NONEV
           | SOME "o" => accept_offer "o"
           end)
       in
        
       
       ("put", "get").

  (* Specs *)

  Variable Φ : val -> iProp.

  (* Representation predicate for mailboxes *)
  Definition is_mailbox (m : loc) : iProp :=
    m ↦ NONEV ∨ (∃ (o : val) γ, m ↦ SOMEV o ∗ is_offer Φ o γ).

  Definition mailbox_inv : namespace := nroot .@ "mailbox_inv".
  
  (* Since mk_mailbox returns a pair of closures, its specification uses nested Hoare triples *)
  Lemma wp_mk_mailbox : 
    {{{ True }}} mk_mailbox #() {{{m, RET m; ∃ (put get : val),
                                   ⌜m = (put, get)%V⌝ ∗
                                   ∀ (v : val), {{{ Φ v }}} put v {{{ vr, RET vr; ⌜vr = NONEV⌝ ∨ ∃ vv : val, ⌜vr = SOMEV vv⌝ ∗ Φ vv }}} ∗
                                   {{{ True }}} get #()  {{{ r, RET r; ⌜r = NONEV⌝ ∨ ∃ (v : val), ⌜r = SOMEV v⌝ ∗ Φ v }}}
                             }}}.
  Proof.
    iIntros (P) "_ Hpost".
    rewrite /mk_mailbox. wp_pures. wp_alloc r as "Hr". wp_pure _.
    iMod (inv_alloc mailbox_inv _ (is_mailbox r) with "[Hr]") as "#Hinv".
    { iNext. rewrite /is_mailbox. by iLeft; iFrame. }    
    wp_pures.
    iApply "Hpost". iExists _, _. iSplitL "".
    { by iPureIntro. }
    iIntros (v).
    iSplitL "".
    - iModIntro. iIntros (Cont) "Hpre Hpost".
      wp_pures. wp_apply (wp_mk_offer Φ v with "Hpre").
      iIntros (o) "Ho". iDestruct "Ho" as (γ) "[Hkey #Ho]". wp_pures.
      wp_bind (_ <- _)%E. rewrite /is_mailbox.
      iInv mailbox_inv as "[> Hnone | Hsome]" "Hclose".
      * wp_store. iMod ("Hclose" with "[Ho Hnone]") as "_".
        { iNext. iRight. iExists o, γ. iFrame "#". iFrame. }
        iModIntro. wp_pures. wp_apply (wp_revoke_offer Φ o γ with "[Hkey]"); auto.
        iIntros (r0) "Hst". iApply "Hpost".
        iDestruct "Hst" as (v0) "[Hnone | Hsome]".
        { by iLeft. }
        { by iRight; iExists v0. }
      * iDestruct "Hsome" as (o0 γ0) "[Hr _]".
        wp_store. iMod ("Hclose" with "[Hr]") as "_".
        { iNext. by iRight; iExists o, γ; iFrame. }
        iModIntro. wp_pures. wp_apply (wp_revoke_offer Φ o γ with "[Hkey]").
        { iFrame; iFrame "#". }
        iIntros (r0) "Hpre". iDestruct "Hpre" as (v0) "Hpre".
        iApply "Hpost". iDestruct "Hpre" as "[Hnone | Hsome]".
        { by iLeft. }
        { by iRight; iExists v0. }
        
    - iModIntro. iIntros (P') "_ Hpost".
      wp_pures. wp_bind (! _)%E.
      iInv mailbox_inv as "[Hnone | Hsome]" "Hclose".
      * wp_load. iMod ("Hclose" with "[Hnone]") as "_".
        {  iNext. rewrite /is_mailbox. by iLeft. }
        iModIntro. wp_pures. iApply "Hpost". by iLeft.
      * iDestruct "Hsome" as (o γ) "[Hr #Ho]".
        wp_load. iMod ("Hclose" with "[Hr]") as "_".
        { iNext. iRight. iExists o, γ. iFrame. iFrame "#". }
        iModIntro. wp_pures. wp_apply (wp_accept_offer Φ o γ); auto.
        iIntros (r0) "H". iApply "Hpost". iDestruct "H" as (v0) "[Hnone | Hsome]".
        { by iLeft. }
        { by iRight; iExists v0. }
  Qed.
      
End mailbox.

Section stack.

  Definition mk_stack : val :=
    λ: <>,
       let: "mb" := mk_mailbox #() in
       let: "put" := Fst "mb" in
       let: "get" := Snd "mb" in

       (* The stack is a pointer p that points to either
          - NONEV, if the stack is empty
          - SOMEV l, if the stack is non-empty.
            l in turn points to a pair (h, t), where h is the top of the stack
            and `t` is the rest of the stack. *)

       (* TODO: explain how this differs from the course notes because of limitations
          on what can be compared with CAS. *)
       
       let: "stack" := ref NONEV in

       (* Push an element into the stack. Returns unit. *)
       let: "push" :=
          rec: "push" "v" :=
            match: ("put" "v") with
              NONE => #()
            | SOME "v" =>
              let: "curr" := !"stack" in
              let: "nstack" := SOME (ref ("v", "curr")) in
              if: (CAS "stack" "curr" "nstack") then #() else ("push" "v")
            end
       in

       (* Pop an element from the stack. If the stack is empty, return None,
          otherwise return Some head. *)
       let: "pop" :=
        rec: "pop" <> :=
          match: ("get" #()) with
            SOME "v" => SOME "v"
          | NONE =>
            match: !"stack" with
              NONE => NONEV
            | SOME "l" =>
              let: "p" := !"l" in
              let: "head" := Fst "p" in
              let: "tail" := Snd "p" in
              if: (CAS "stack" (SOME "l") "tail") then SOME "head" else ("pop" #())
            end
          end
          
       in

       ("push", "pop").

  (* Bag specification for mk_stack *)

  Variable Φ : val -> iProp.

  Definition oloc_to_val (o : option loc) : val :=
    match o with
      None => NONEV
    | Some l => SOMEV #l
    end.

  (* The representation predicate for stacks. The version in the notes uses guarded
     recursion, but let's see if we can get by with a simpler version. *)
  Fixpoint is_stack (o : option loc) (ls : list val) : iProp :=
    match ls with
      nil => ⌜o = None⌝
    | x :: xs => ∃ (l : loc) (o' : option loc),
      ⌜o = Some l⌝ ∗ l ↦ (x, oloc_to_val o') ∗ Φ x ∗ (is_stack o' xs)
  end.

  Definition stack_inv (l : loc) : iProp :=    
    ∃ (o : option loc) (ls : list val), l ↦ oloc_to_val o ∗ is_stack o ls.
  
  Definition inv_ns : namespace := nroot .@ "stack_inv".

  Lemma oloc_to_val_unboxed ol : val_is_unboxed (oloc_to_val ol).
  Proof.
    rewrite /val_is_unboxed. destruct ol; simpl; auto.
  Qed.
  
  Lemma wp_mk_stack :
    {{{ True }}} mk_stack #() {{{ s, RET s; ∃ (push pop : val),
                                 ⌜s = (push, pop)%V⌝ ∗
                                                 (∀ (v : val), {{{ Φ v }}} push v {{{ RET #(); True
                                                                                 }}}) ∗
                                                 ({{{ True }}} pop #() {{{ v, RET v; ⌜v = NONEV⌝ ∨ ∃ (w : val), ⌜v = SOMEV w⌝ ∗ Φ w }}})  }}}.
 Proof.
   iIntros (C) "Hpre Hpost".
   rewrite /mk_stack. wp_pures.
   wp_apply wp_mk_mailbox; try done.
   iIntros (m) "Hm". iDestruct "Hm" as (put get) "[-> #Hm]".
   wp_pures. wp_alloc s as "Hs".
   iMod (inv_alloc inv_ns _ (stack_inv s) with "[Hs]") as "#Hinv".
   { iNext. rewrite /stack_inv.
     iExists None, nil. iSimpl. iFrame. iPureIntro. reflexivity. }
   wp_pures. iApply "Hpost". iExists _, _.
   iSplitL "". auto.
   iSplitL "".

   (* push *)
   - iLöb as "Hind".
     iIntros (v). iModIntro.
     iIntros (C2) "Hpre Hpost".
     wp_pures. wp_bind (put _). iSpecialize ("Hm" $! v). iDestruct "Hm" as "[Hput _]". 
     wp_apply ("Hput" with "Hpre").                                                        
     iIntros (vr) "Hpre".                                                       
     iDestruct "Hpre" as "[-> | Hsome]".
     { wp_pures. by iApply "Hpost". }
     iDestruct "Hsome" as (vv) "[-> HΦ]".
     wp_pures. wp_bind (! _)%E.
     iInv inv_ns as (ol ls) "[Hs His]" "Hclose". wp_load.     
     iMod ("Hclose" with "[His Hs]") as "_".
     { iNext. rewrite /stack_inv. iExists ol, ls. iFrame. }
     iModIntro. wp_pures. wp_alloc l2 as "Hl2". wp_pures. wp_bind (CmpXchg _ _ _).
     iInv inv_ns as (ol2 ls2) "[Hs His]" "Hclose". 
     destruct (decide (ol = ol2)); subst.
     + wp_cmpxchg_suc. { left; apply oloc_to_val_unboxed. }
       iMod ("Hclose" with "[Hs His Hl2 HΦ]") as "_". {
         iNext. rewrite /stack_inv.
         iExists (Some l2), (vv :: ls2).
         iFrame. rewrite /is_stack. iExists l2, ol2.
         iFrame. iPureIntro. reflexivity.
       }
       iModIntro. wp_pures. by (iApply "Hpost").
     + wp_cmpxchg_fail.
       { destruct ol, ol2; auto.
         simpl. intros eq. apply n. inversion eq; subst. reflexivity. }
       { left; apply oloc_to_val_unboxed. }
       iMod ("Hclose" with "[Hs His]") as "_". {
         iNext. rewrite /stack_inv. iExists ol2, ls2. iFrame.
       }
       iModIntro. wp_pure _. wp_pure _. iApply ("Hind" with "[HΦ]"); iFrame.

   (* pop *)
   - iLöb as "Hind".
     iIntros (v). iModIntro.
     iIntros "Hpre Hpost".
     wp_pures. wp_bind (get _). iSpecialize ("Hm" $! #()). iDestruct "Hm" as "[_ Hget]".
     wp_apply "Hget"; try done.
     iIntros (r) "[-> | Hs]".
     + 
     + iDestruct "Hs" as (v0) "[-> HΦ]".
       wp_pures. iApply "Hpost". iRight. iExists v0; iFrame. iPureIntro; done.
   
     
     
End stack.
