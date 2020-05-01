(** 
Adapted from:

    Concurrent bag specification from the HOCAP paper.
    "Modular Reasoning about Separation of Concurrent Data Structures"
    <http://www.kasv.dk/articles/hocap-ext.pdf>

This file: abstract bag specification
*)
From iris.heap_lang Require Export lifting notation.
From iris.base_logic.lib Require Export invariants.
From iris.program_logic Require Export weakestpre.
From iris.base_logic.lib Require Export invariants.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode.
From iris.heap_lang Require Import notation lang.
From iris.heap_lang.lib Require Import par.
From iris.bi Require Export notation.



Record ops Σ `{!heapG Σ} :=
  Ops {
      (* operations *)
      read : val;

      (* specs *)
      read_spec (l : loc) (m : val) (q : Qp) (E : coPset) (N : namespace) : 
        (True ={E, E ∖ ↑N}=> (▷ l ↦{q} m) ∗ (▷ l ↦{q} m -∗ |={E ∖ ↑N, E}=> True)) -∗
        {{{ True }}} read #l @E {{{RET m; True}}};
    }.


Arguments read {_ _} _.
Arguments read_spec {_ _} _ _ _ _.


Section impl.
  Context Σ `{!heapG Σ}.

  Definition read_impl : val :=
    λ: "l", !"l".

  Lemma read_impl_spec (l : loc) (m : val) (q : Qp) (E : coPset) (N : namespace) :
    (True ={E, E ∖ ↑N}=> (▷ l ↦{q} m) ∗ (▷ l ↦{q} m -∗ |={E ∖ ↑N, E}=> True)) -∗
    {{{ True }}} read_impl #l @E {{{RET m; True}}}.
  Proof.
    iIntros "#Hvs" (ϕ).
    iModIntro. iIntros "_ Hcont".
    rewrite /read_impl. wp_pures.
    iMod ("Hvs" with "[]") as "[Hl Hclose]"; auto.
    wp_load. iMod ("Hclose" with "Hl") as "_".
    iModIntro. by iApply "Hcont".
  Qed.

  (*
  iModIntro.
  Qed.
  *)

  Definition ops_impl :=
    {|
      read := read_impl;
      read_spec := read_impl_spec;
    |}.    
  
End impl.

Section client.
  Context Σ `{!heapG Σ}.
  
  Variable O : ops Σ.
  Variable N : namespace.

  Lemma read_seq_spec (l : loc) (w : val) :
    {{{ l ↦ w }}} O.(read) #l {{{ RET w; l ↦ w }}}.
  Proof.
    iIntros (ϕ) "Hpre Hcont".
    wp_apply ((O.(read_spec) l w 1%Qp (l ↦ w)%I True N) with "[] [Hpre] [Hcont]"); auto.
    iModIntro. iIntros "[_ Hl]". iApply "Hcont". iFrame.
  Qed.
  
  (* Demonstrate logical atomicity *)
  Definition par_read : val :=
    λ: <>,
       let: "l" := ref #0 in
       O.(read) "l";;
       (O.(read) "l") ||| (O.(read) "l").

  Lemma par_read_spec :
    {{{ True }}} par_read #() {{{ RET (#0, #0); True }}}.
  Proof.
    iIntros (ϕ) "_ Hcont".
    rewrite /par_read. wp_pures.
    wp_alloc l as "Hl". wp_pures.
    (* Use the sequential spec *)
    wp_apply (read_seq_spec with "Hl").
    iIntros "Hl". wp_pures.
    iMod (inv_alloc N _ (l ↦ #0) with "Hl") as "#Hinv".
    wp_apply (wp_par (λ v, ⌜v = #0⌝)%I (λ v, ⌜v = #0⌝)%I).
    - wp_apply (O.(read_spec) l #0 1%Qp True True N); auto.
      iModIntro. iIntros "_".
      iInv N as "Hinv2".
      iPoseProof (O.(read_spec) l #0 1%Qp True True N) as "Hspec".
      iApply "Hspec"; auto.
      
      
    
  
End client.

 (*                                
  (* -- operations -- *)
  newBag : val;
  pushBag : val;
  popBag : val;
  (* -- predicates -- *)
  (* name is used to associate bag_contents with is_bag *)
  name : Type;
  is_bag (N: namespace) (γ: name) (b: val) : iProp Σ;
  bag_contents (γ: name) (X: gmultiset val) : iProp Σ;
  (* -- ghost state theory -- *)
  is_bag_persistent N γ b : Persistent (is_bag N γ b);
  bag_contents_timeless γ X : Timeless (bag_contents γ X);
  bag_contents_agree γ X Y: bag_contents γ X -∗ bag_contents γ Y -∗ ⌜X = Y⌝;
  bag_contents_update γ X X' Y:
    bag_contents γ X ∗ bag_contents γ X' ==∗
    bag_contents γ Y ∗ bag_contents γ Y;
  (* -- operation specs -- *)
  newBag_spec N :
    {{{ True }}} newBag #() {{{ x γ, RET x; is_bag N γ x ∗ bag_contents γ ∅ }}};
  pushBag_spec N P Q γ b v :
    □ (∀ (X : gmultiset val), bag_contents γ X ∗ P
                     ={⊤∖↑N}=∗ ▷ (bag_contents γ ({[v]} ⊎ X) ∗ Q)) -∗
    {{{ is_bag N γ b ∗ P }}}
      pushBag b (of_val v)
    {{{ RET #(); Q }}};
  popBag_spec N P Q γ b :
    □ (∀ (X : gmultiset val) (y : val),
               bag_contents γ ({[y]} ⊎ X) ∗ P
               ={⊤∖↑N}=∗ ▷ (bag_contents γ X ∗ Q (SOMEV y))) -∗
    □ (bag_contents γ ∅ ∗ P ={⊤∖↑N}=∗ ▷ (bag_contents γ ∅ ∗ Q NONEV)) -∗
    {{{ is_bag N γ b ∗ P }}}
      popBag b
    {{{ v, RET v; Q v }}};
  *)

(*
Arguments newBag {_ _} _.
Arguments popBag {_ _} _.
Arguments pushBag {_ _} _.
Arguments newBag_spec {_ _} _ _ _.
Arguments popBag_spec {_ _} _ _ _ _ _ _.
Arguments pushBag_spec {_ _} _ _ _ _ _ _ _.
Arguments is_bag {_ _} _ _ _ _.
Arguments bag_contents {_ _} _ _.
Arguments bag_contents_update {_ _} _ {_ _ _}.
Existing Instances is_bag_persistent bag_contents_timeless.


