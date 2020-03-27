(* This file contains the specification of the lock module implemented as a simple spin lock and discussed in 
   section 7.6 in the invariants and ghost state chapter of the Iris Lecture Notes.
*)

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

Section lock_model. 
(* In order to do the proof we need to assume certain things about the
   instantiation of Iris. The particular, even the heap is handled in an
   analogous way as other ghost state. This line states that we assume the Iris
   instantiation has sufficient structure to manipulate the heap, e.g., it
   allows us to use the points-to predicate, and that the ghost state includes
   the exclusive resource algebra over the singleton set (represented using the
   unitR type). *)  

  Context `{heapG Σ}.
  Context `{inG Σ (exclR unitR)}.
 
  (* We use a ghost name with a token to model whether the lock is locked or not.
     The the token is just exclusive ownerwhip of unit value. *)
  Definition locked γ := own γ (Excl ()).

  (* The name of a lock. *)
  Definition lockN (l : loc) := nroot .@ "lock" .@ l.

  (* The lock invariant *)
  Definition is_lock γ l P :=
    inv (lockN l) ((l ↦ (#false) ∗ P ∗ locked γ) ∨
                                l ↦ (#true))%I.

  (* The is_lock predicate is persistent *)
  Global Instance is_lock_persistent γ l Φ : Persistent (is_lock γ l Φ).
  Proof. apply _. Qed.
  
End lock_model.

Section lock_code.

  (* Here is the standard spin lock code *)
  
  Definition newlock : val := λ: <>, ref #false.
    
  Definition acquire : val :=
    rec: "acquire" "l" :=
      if: CAS "l" #false #true then #() else "acquire" "l".
    
  Definition release : val := λ: "l", "l" <- #false.

End lock_code.

Section lock_spec.
  Context `{heapG Σ}.
  Context `{inG Σ (exclR unitR)}.
  
  Lemma newlock_spec P:
    {{{ P }}} newlock #() {{{ℓ, RET #ℓ; ∃ (γ : gname), is_lock γ ℓ P}}}.
  Proof.    
    iIntros (ϕ) "HP Hϕ".
    iMod (own_alloc (Excl ())) as (γ) "Hk". {
      constructor.
    }
    rewrite /newlock -wp_fupd. wp_pures. wp_alloc ℓ as "Hℓ".
    iApply "Hϕ".
    rewrite /is_lock. iExists γ.
    iApply (inv_alloc (lockN ℓ) _ _).
    rewrite /locked.
    iNext. iLeft. iFrame.
  Qed.           

  Lemma acquire_spec γ ℓ P:
    {{{ is_lock γ ℓ P }}} acquire #ℓ {{{RET #(); P ∗ locked γ}}}.
  Proof.
    iIntros (ϕ) "#HP Hϕ".
    iLöb as "IH".
    rewrite /acquire. wp_pures. wp_bind (CmpXchg _ _ _).
    iInv "HP" as "[(Hℓ & Hpred & Hkey) | Hlocked]" "Hclose".
    - wp_cmpxchg_suc. 
     iMod ("Hclose" with "[Hℓ]") as "_". (* Ask why this step works. *)
     { iNext. iRight. iFrame. }                                                
     iModIntro. wp_pures. iApply "Hϕ". iFrame.
   - wp_cmpxchg_fail. 
     iMod ("Hclose" with "[Hlocked]") as "_".
     { iNext. iRight. iFrame. }
     iModIntro. wp_proj. wp_if.
     iApply "IH". iNext. done.
  Qed.
          
  Lemma release_spec γ ℓ P:
    {{{ is_lock γ ℓ P ∗ locked γ ∗ P }}} release #ℓ {{{RET #(); True}}}.
  Proof.
    iIntros (ϕ) "(#Hil & Hl & HP) Hϕ".
    rewrite /release. wp_pures.
    iInv "Hil" as "[(Hℓ & Hpred & Hkey) | Hlocked]" "Hclose".
    - wp_store.
      rewrite /locked.
      iPoseProof (own_valid_2 with "Hl Hkey") as "%".
      exfalso.
      apply (exclusive_l (Excl ()) (Excl ())); assumption.
    - wp_store.
      iMod ("Hclose" with "[Hl HP Hlocked]") as "_".
      { iNext. iLeft. iFrame. }
      iModIntro. iApply "Hϕ". trivial.
  Qed.       
  Global Opaque newlock release acquire.
End lock_spec.

Section bag_code.

  (* A bag is a pair of (optional list of values, lock)  *)
  Definition new_bag : val :=
    λ: <>, (newlock #(), ref NONEV).

  (* Insert a value into the bag. Return unit. *)
  Definition insert : val :=
    λ: "bag" "v",
      let: "lst" := Snd "bag" in
      let: "lock" := Fst "bag" in
      acquire "lock";;
      "lst" <- SOME ("v", !"lst");;
      release "lock";;        
      #().        

  (* Remove the value last-added to the bag (wrapped in an option), if the
     bag is non-empty. If the bag is empty, return NONE. *)
  Definition remove : val :=
    λ: "bag",
      let: "lst" := Snd "bag" in
      let: "lock" := Fst "bag" in
      acquire "lock";;
      let: "res" :=
         match: !"lst" with
           NONE => NONEV
         | SOME "pair" =>
           "lst" <- Snd "pair";;
           SOME (Fst "pair")
         end
      in           
      release "lock";;
      "res".        
  
End bag_code.

Section bag_spec.

  Context `{!heapG Σ}.
  Context `{inG Σ (exclR unitR)}.
  
  Notation iProp := (iProp Σ).

  Variable Φ : val -> iProp.
  
  Fixpoint bag_list (xs : val) (n : nat) : iProp :=
    match n with
    | O => ⌜xs = NONEV⌝
    | S n => ∃ (x r : val), ⌜xs = SOMEV (x, r)⌝ ∗ Φ x ∗ bag_list r n
    end.
  
  Definition is_bag (γ : gname ) (bag : val) : iProp :=
    ∃ (lock lst : loc), ⌜bag = (#lock, #lst)%V⌝ ∗ is_lock γ lock (∃ (xs : val) (n : nat), lst ↦ xs ∗ bag_list xs n).

  (* Why is this predicate persistent? *)
  Global Instance is_bag_persistent γ bag : Persistent (is_bag γ bag).
  Proof. apply _. Qed.

  Definition new_bag_spec :
    {{{ True }}} new_bag #() {{{ v, RET v; ∃ γ, is_bag γ v }}}.
  Proof.
    iIntros (ϕ) "_ HPost".
    rewrite /new_bag. wp_pures. wp_bind (ref _)%E.
    wp_alloc lst as "Hl". wp_bind (newlock _).
    wp_apply (newlock_spec (∃ (xs : val) (n : nat), lst ↦ xs ∗ bag_list xs n)%I with "[Hl]").
    - iExists NONEV. iExists O. by iFrame.
    - iIntros (ℓ) "Hlock".
      wp_pures. iApply "HPost". iDestruct "Hlock" as (γ) "Hlock".
      iExists γ. rewrite /is_bag. iExists ℓ, lst. by iFrame.
  Qed.
      
  Definition remove_spec γ (bag : val ) : 
    {{{ is_bag γ bag }}} remove bag {{{ v, RET v; ⌜v = NONEV⌝ ∨ ∃ (x : val), ⌜v = SOMEV x⌝ ∗ Φ x }}}.
  Proof.
    iIntros (ϕ) "HPre HPost".
    rewrite /remove. wp_pures.
    rewrite /is_bag. iDestruct "HPre" as (lock lst) "[% #Hlock]".
    rewrite H0. wp_proj. wp_pures.
    wp_apply ((acquire_spec γ lock _) with "[Hlock]").
    { auto. }
    iIntros "[Hbag Hkey]". iDestruct "Hbag" as (xs n) "[Hlst Hbag]".
    wp_pures. wp_load.
    destruct n; rewrite [(_ xs _)]/bag_list. iDestruct "Hbag" as "->".
    - wp_pures. wp_apply (release_spec γ lock (∃ (xs : val) (n : nat), lst ↦ xs ∗ bag_list xs n)  with "[Hkey Hlst]")%I.
      { iFrame. iFrame "#". iExists (InjLV #())%V. iExists O.
        iFrame. by rewrite /bag_list. }
      iIntros "_". wp_pures. iApply "HPost". by iLeft.
    - iDestruct "Hbag" as (x r) "[% [HΦ Htail]]". rewrite H1.
      wp_pures. rewrite -/bag_list. wp_store. wp_pures.
      wp_apply (release_spec γ lock (∃ (xs : val) (n : nat), lst ↦ xs ∗ bag_list xs n)  with "[Hkey Hlst Htail]")%I.
      { iFrame. iFrame "#". iExists r, n. iFrame. }
      iIntros "_". wp_pures. iApply "HPost".
      iRight. iExists x. by iFrame.
  Qed.
      
  Definition insert_spec γ (bag v : val) :
    {{{ is_bag γ bag ∗  Φ v }}} insert bag v {{{ RET #(); True }}}.
  Proof.
    iIntros (ϕ) "[Hbag HΦ] HPost".
    rewrite /insert. wp_pures.
    rewrite /is_bag. iDestruct "Hbag" as (lock lst) "[-> #Hlock]".
    wp_pures. wp_apply (acquire_spec γ lock _ with "Hlock").
    iIntros "[Hbag Hkey]". iDestruct "Hbag" as (xs n) "[Hlst Hbag]".
    wp_pures. wp_bind (! _)%E. wp_load. wp_pures. wp_store.
    wp_apply (release_spec γ lock _ with "[Hkey HΦ Hlst Hbag]").
    { iSplitL "". auto.
      iFrame. iExists (InjRV (v, xs))%V, (S n). iFrame.
      rewrite [_ _ (S n)]/bag_list.
      iExists v, xs. rewrite -/bag_list. by iFrame. }
    iIntros "_". wp_pures. iApply "HPost". done.
  Qed.
      
End bag_spec.

Typeclasses Opaque locked.
Global Opaque locked.
Typeclasses Opaque is_lock.
Global Opaque is_lock.
