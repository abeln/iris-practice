
(*
This file formalizes the "Message Passing" example in Figure 7 of the paper: Strong Logic for Weak Memory
https://people.mpi-sws.org/~dreyer/papers/iris-weak/paper.pdf

Parts of this file have been taken from the coq examples for the Iris lectures notes.xs
*)


From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Export notation lang.
From iris.proofmode Require Export tactics.
From iris.heap_lang Require Import proofmode.
From iris.base_logic.lib Require Export invariants.
From iris.algebra Require Import excl.
From iris.heap_lang.lib Require Import par.

Context `{heapG Σ}.
Context `{inG Σ (exclR unitR)}.
Context (N_out N_in : namespace).
Notation iProp := (iProp Σ).

Section mp_model.
  Definition invN (l : loc) := nroot .@ "inv" .@ l.  
  
  Definition inv_in (l_in : loc) (γ : gname) : iProp :=
    (l_in ↦ #37 ∨ own γ (Excl ()))%I.
  
  Definition inv_out (l_out l_in : loc) (γ : gname) : iProp :=
    (l_out ↦ #0 ∨ l_out ↦ #1 ∗ inv (invN l_in) (inv_in l_in γ))%I.
End mp_model.

Section mp_code.

  (* First we have a function `repeat l`, which reads l until its value is non-zero,
     at which point it returns l's value. *)
  Definition repeat_prog : val :=
    rec: "repeat" "l" :=
      let: "vl" := !"l" in
      if: "vl" = #0 then ("repeat" "l") else "vl".

  (* Then we have the code for the example. *)
  Definition mp : val :=
    λ: <>,
       let: "x" := ref #0 in
       let: "y" := ref #0 in
       let: "res" := (("x" <- #37;; "y" <- #1) ||| (repeat_prog "y";; !"x")) in
       Snd "res".

End mp_code.

Section mp_spec.
  
  Lemma mp_spec :
    {{{ True }}} mp #() {{{ v, RET #v ; ⌜v = 37⌝ }}}.
  Proof.
    iIntros (Φ) "_ HPost".
    rewrite /mp. wp_pures.
    wp_alloc lx as "Hlx". wp_pures. wp_alloc ly as "Hly". wp_pures.
    wp_bind (par _ _).
    iMod (own_alloc (Excl ())) as (γ) "Hown".
    { constructor. }    
    iMod (inv_alloc (invN ly) _ (inv_out ly lx γ) with "[Hly]") as "#Hinv".
    { iNext. rewrite /inv_out. iLeft. iFrame. }
    wp_apply (wp_par (λ _, True)%I (λ vx, ⌜vx = #37⌝)%I with "[Hinv Hlx] [Hinv Hown]").
    - wp_store.
      iMod (inv_alloc (invN lx) _ (inv_in lx γ) with "[Hlx]") as "#Hinv_in".
      { iNext. iLeft. iFrame. }
      iInv (invN ly) as "[Hy0 | [Hy1 _]]" "Hclose"; wp_store.
      * iMod ("Hclose" with "[Hinv_in Hy0]") as "_".        
        iNext; iRight; iFrame; iFrame "#". by iModIntro.
      * iMod ("Hclose" with "[Hinv_in Hy1]") as "_".        
        iNext; iRight; iFrame; iFrame "#". by iModIntro.
    - wp_bind (repeat_prog _).
      iLöb as "IH".
      rewrite /repeat_prog. wp_pures. wp_bind (!_)%E.
      iInv (invN ly) as "[Hy0 | [Hy1 #Hinv_in]]" "Hclose".
      * wp_load.
        iMod ("Hclose" with "[Hy0]") as "_".
        { iLeft. iNext. iFrame. }
        iModIntro.
        wp_let. wp_pure _. wp_if.
        iApply "IH". iFrame.
      * wp_load.
        iInv (invN lx) as "[Hlx | Hown2]" "Hclose_in".
        { rewrite /invN.  }
        + iMod ("Hclose_in" with "[Hown]") as "_".
          { iRight. iNext; iFrame. }
          iMod ("Hclose" with "[Hy1]") as "_".
          { iRight. iNext. by iFrame; iFrame "#". }
          iModIntro. wp_pures. wp_load. iPureIntro; auto.
        +  iDestruct "Hown2" as "> Hown2". iExFalso.
           iDestruct (own_valid_2 with "Hown Hown2") as %Hv. done.
    - iIntros (v1 v2) "[_ ->]".
      iNext. wp_pures. iApply "HPost". iPureIntro. reflexivity.
  Qed.
      
           
  
  (* Global Opaque newlock release acquire. *)
End lock_spec.


Typeclasses Opaque locked.
Global Opaque locked.
Typeclasses Opaque is_lock.
Global Opaque is_lock.
