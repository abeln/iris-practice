
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
Context `{!spawnG Σ}.

Notation iProp := (iProp Σ).

Section mp_model.
  Definition invN (name : string) := nroot .@ "inv" .@ name.  
  
  Definition inv_in (l_in : loc) (γ : gname) : iProp :=
    (l_in ↦ #37 ∨ own γ (Excl ()))%I.
  
  Definition inv_out (l_out l_in : loc) (γ : gname) : iProp :=
    (l_out ↦ #0 ∨ l_out ↦ #1 ∗ inv (invN "inner") (inv_in l_in γ))%I.
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
    iMod (inv_alloc (invN "outer") _ (inv_out ly lx γ) with "[Hly]") as "#Hinv".
    { iNext. rewrite /inv_out. iLeft. iFrame. }
    wp_apply (wp_par (λ _, True)%I (λ vx, ⌜vx = #37⌝)%I with "[Hinv Hlx] [Hinv Hown]").
    - wp_store.
      iMod (inv_alloc (invN "inner") _ (inv_in lx γ) with "[Hlx]") as "#Hinv_in".
      { iNext. iLeft. iFrame. }
      iInv (invN "outer") as "[Hy0 | [Hy1 _]]" "Hclose"; wp_store.
      * iMod ("Hclose" with "[Hinv_in Hy0]") as "_".        
        iNext; iRight; iFrame; iFrame "#". by iModIntro.
      * iMod ("Hclose" with "[Hinv_in Hy1]") as "_".        
        iNext; iRight; iFrame; iFrame "#". by iModIntro.
    - wp_bind (repeat_prog _).
      iLöb as "IH".
      rewrite /repeat_prog. wp_pures. wp_bind (!_)%E.
      iInv (invN "outer") as "[Hy0 | [Hy1 #Hinv_in]]" "Hclose".
      * wp_load.
        iMod ("Hclose" with "[Hy0]") as "_".
        { iLeft. iNext. iFrame. }
        iModIntro.
        wp_let. wp_pure _. wp_if.
        iApply "IH". iFrame.
      * wp_load.
        iInv (invN "inner") as "[Hlx | Hown2]" "Hclose_in".        
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
End mp_spec.


Section mp_code_alt.
  (* Let's try another variation of the code: one where we read x and y only
     _after_ both threads are done and, further, we read _both_ of their values.

   Additionally, we want to retain ownership of the two pointers when we're done
   with the two threads. *)

  Definition mp_alt : val :=
    λ: <>,
       let: "x" := ref #0 in
       let: "y" := ref #0 in
       let: "tmp" := (("x" <- #37;; "y" <- #1) ||| (repeat_prog "y";; #())) in
       let: "res" := ref (!"x", !"y") in
       "res".

End mp_code_alt.

Section mp_alt_model.

  Definition stateRes (γ : gname) : iProp := own γ (Excl ()).

  Variable l_out l_in : loc.
  Variable γ1 γ2 γ3 γ4: gname. (* state index *)
  Variable t1 t2 : gname. (* tokens for last state *)
  
  (* The idea behind the invariants below is the little state transition system:
      st1 -> st2 -> st3, where each `st` is decorated with the values of `x` and `y`.
   *)
  
  Definition st1 : iProp :=
    (l_out ↦ #0 ∗ l_in ↦ #0 ∗ stateRes γ2 ∗ stateRes γ3 ∗ stateRes γ4)%I.

  Definition st2 : iProp :=
    (l_out ↦ #0 ∗ l_in ↦ #37 ∗ stateRes γ1 ∗ stateRes γ3 ∗ stateRes γ4)%I.
  
  Definition st3 : iProp :=
     (l_out ↦ #1 ∗ l_in ↦ #37 ∗ stateRes γ1 ∗ stateRes γ2 ∗ stateRes γ4)%I. 

  Definition st4 : iProp :=
    (stateRes t1 ∗ stateRes t2 ∗ stateRes γ1 ∗ stateRes γ2 ∗ stateRes γ3)%I.
   
  Definition inv_alt : iProp := (st1 ∨ st2 ∨ st3 ∨ st4)%I.
 
End mp_alt_model.

Section mp_alt_spec.

  Definition mpName : namespace := nroot .@ "mp".

    
  Lemma mp_alt_spec :
    {{{ True }}} mp_alt #() {{{ v, RET #v ; v ↦ (#37, #1) ∗ (∃ (lx ly : loc), ly ↦ #1 ∗ lx ↦ #37) }}}.
  Proof.
    iIntros (ϕ) "_ Post".
    rewrite /mp_alt. wp_pures.
    wp_alloc lx as "Hx". wp_alloc ly as "Hy". wp_pures. wp_bind (par _ _).
    iMod (own_alloc (Excl ())) as (γ1) "Hγ1"; try done.
    iMod (own_alloc (Excl ())) as (γ2) "Hγ2"; try done.
    iMod (own_alloc (Excl ())) as (γ3) "Hγ3"; try done.
    iMod (own_alloc (Excl ())) as (γ4) "Hγ4"; try done.
    iMod (own_alloc (Excl ())) as (t1) "Ht1"; try done.
    iMod (own_alloc (Excl ())) as (t2) "Ht2"; try done.
    iMod (inv_alloc mpName _ (inv_alt ly lx γ1 γ2 γ3 γ4 t1 t2) with "[Hγ2 Hγ3 Hγ4 Hx Hy]") as "#Hinv".
    { iNext. iLeft. rewrite /st1.
      rewrite /stateRes.
      iFrame. }
    wp_apply (wp_par (λ _, stateRes γ3 ∗ stateRes t1)%I (λ vx, stateRes t2)%I with "[Hγ1 Ht1] [Ht2]").
    - wp_bind (_ <- _)%E.
      iInv mpName as "> [(Hx & Hy & Hst2 & Hst3 & Hst4) | [(_ & _ & Hst1 & _ & _) | [(_ & _ & Hst1 & _ & _) | (_ & _ & Hst1 & _ & _)]]]" "Hclose"; rewrite /stateRes;
      try (by iExFalso; iDestruct (own_valid_2 with "Hγ1 Hst1") as "%").   
      wp_store. iMod ("Hclose" with "[Hx Hy Hγ1 Hst3 Hst4]") as "_".
      { iNext. rewrite /inv_alt. iRight. iLeft. iFrame. }
      iModIntro. wp_pures.
      iInv mpName as "> [(_ & _ & Hγ2 & _ & _) | [(Hy & Hx & Hst1 & Hst3 & Hst4) | [(_ & _ & _ & Hγ2 & _) | (_ & _ & _ & Hγ2 & _)]]]" "Hclose"; rewrite /stateRes;
      try (by iExFalso; iDestruct (own_valid_2 with "Hγ2 Hst2") as "%").
      wp_store. iMod ("Hclose" with "[Hx Hy Hst1 Hst2 Hst4]") as "_".
      { iNext. iRight. iRight. iLeft. iFrame. }
      iModIntro. iFrame.
    - iLöb as "IH".
      rewrite /repeat_prog. wp_pures. wp_bind (!_)%E.
      iInv mpName as "> [(Hy & Hx & Hst2 & Hst3 & Hst4) | [(Hy & Hx & Hst1 & Hst3 & Hst4) | [(Hy & Hx & Hst1 & Hst2 & Hst4) | (_ & t2 & _ & _ & _)]]]" "Hclose"; rewrite /stateRes.
      + wp_load. iMod ("Hclose" with "[Hy Hx Hst2 Hst3 Hst4]") as "_".
        iNext. rewrite /inv_alt. iLeft. iFrame.
        iModIntro.
        wp_let. wp_pure _. wp_pure _.
        iApply "IH". iFrame.
      + wp_load. iMod ("Hclose" with "[Hy Hx Hst1 Hst3 Hst4]") as "_".
        iNext. rewrite /inv_alt. iRight. iLeft. iFrame.
        iModIntro.
        wp_let. wp_pure _. wp_pure _.
        iApply "IH". iFrame.
      + wp_load. iMod ("Hclose" with "[Hy Hx Hst1 Hst2 Hst4]") as "_".
        { iNext. rewrite /inv_alt. iRight. iRight. iLeft. iFrame. }
        iModIntro.
        wp_pures. done.
      + by iExFalso; iDestruct (own_valid_2 with "Ht2 t2") as "%".
    - iIntros (v1 v2) "[(Hst3 & Ht1) Ht2]".
      iNext. wp_pures. wp_bind (!#ly)%E.
      iInv mpName as "> [(_ & _ & _ & Hγ3 & _) | [(_ & _ & _ & Hγ3 & _) | [(Hy & Hx & Hst1 & Hst2 & Hst4) | (_ & _ & _ & _ & Hγ3)]]]" "Hclose"; rewrite /stateRes;
      try (by iExFalso; iDestruct (own_valid_2 with "Hγ3 Hst3") as "%").
      wp_load. iMod ("Hclose" with "[Ht1 Ht2 Hst1 Hst2 Hst3]") as "_".
      { iNext. rewrite /inv_alt. iRight. iRight. iRight. iFrame. }
      iModIntro.
      wp_bind (!#lx)%E. wp_load. wp_pures. wp_alloc l_res as "Hres". wp_pures.
      iApply "Post". iFrame. iExists lx, ly. iFrame.
Qed.

End mp_alt_spec.
