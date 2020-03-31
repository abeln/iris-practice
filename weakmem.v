
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

Section mp_model. 
  Context `{heapG Σ}.
  Context `{inG Σ (exclR unitR)}.
  Context (N_out N_in : namespace).
  Notation iProp := (iProp Σ).

  Definition inv_in (l_in : loc) (γ : gname) : iProp :=
    (l_in ↦ #37 ∨ own γ (Excl ()))%I.
  
  Definition inv_out (l_out l_in : loc) (γ : gname) : iProp :=
    inv N_out (l_out ↦ #0 ∨ l_out ↦ #1 ∗ inv N_in (inv_in l_in γ))%I.   
End mp_model.

Section mp_code.

  (* First we have a function `repeat l`, which reads l until its value is non-zero,
     at which point it returns l's value. *)
  Definition repeat : val :=
    rec: "repeat" "l" :=
      let: "vl" := !"l" in
      if: "vl" = #0 then "repeat" "l" else "vl".

  (* Then we have the code for the example. *)
  Definition mp : val :=
    λ: <>,
       let: "x" := ref #0 in
       let: "y" := ref #0 in
       (("x" <- #37;; "y" <- #1) ||| (repeat "y";; !"x")).

End mp_code.

Section mp_spec.
  Context `{heapG Σ}.
  Context `{inG Σ (exclR unitR)}.
   
  (* Global Opaque newlock release acquire. *)
End lock_spec.


Typeclasses Opaque locked.
Global Opaque locked.
Typeclasses Opaque is_lock.
Global Opaque is_lock.
