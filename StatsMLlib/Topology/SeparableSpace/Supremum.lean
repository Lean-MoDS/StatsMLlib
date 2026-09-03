/-
Copyright (c) 2024 Kei Tsukamoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kei Tsukamoto, Kazumi Kasaura, Naoto Onda, Yuma Mizuno, Sho Sonoda
-/
import Mathlib.Topology.Bases
import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Mathlib.Topology.Order.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.MeasureTheory.MeasurableSpace.Basic

universe u v w

open TopologicalSpace

lemma closure_mem_le_sSup {E : Type v} [ConditionallyCompleteLattice E] [TopologicalSpace E] [OrderClosedTopology E]
  {s : Set E} (hs' : BddAbove s) {b : E} (hb : b ∈ closure s) :
  b ≤ sSup s := by
    have : s ⊆ Set.Iic (sSup s) := by
      intro x hx
      exact le_csSup hs' hx
    have : closure s ⊆ Set.Iic (sSup s) := by
      apply closure_minimal this isClosed_Iic
    exact this hb

lemma sSup_eq_closure_sSup {E : Type v} [ConditionallyCompleteLattice E] [TopologicalSpace E] [OrderClosedTopology E]
  {s : Set E} (hs : s.Nonempty) (hs' : BddAbove s) :
  sSup s = sSup (closure s) := by
  have h' : (BddAbove (closure s)) := by
    use sSup s
    intro b hb
    exact closure_mem_le_sSup hs' hb
  apply le_antisymm
  · apply csSup_le_csSup h' hs
    exact subset_closure
  · apply csSup_le (by aesop)
    exact fun b hb ↦ closure_mem_le_sSup hs' hb

lemma closure_range_eq_closure_denseSeq {X : Type u} [TopologicalSpace X] [SeparableSpace X] [Nonempty X]
  {E : Type v} [ConditionallyCompleteLattice E] [TopologicalSpace E] [OrderClosedTopology E]
  {f : X → E} (hf : Continuous f) :
  closure (Set.range f) = closure (Set.range (f ∘ denseSeq X)) := by
  rw [Set.range_comp f (denseSeq X)]
  apply Set.Subset.antisymm
  · have : Dense (Set.range (denseSeq X)) := denseRange_denseSeq X
    have := hf.range_subset_closure_image_dense this
    exact closure_minimal this isClosed_closure
  · apply closure_mono
    exact Set.image_subset_range f (Set.range (denseSeq X))

theorem separableSpaceSup_eq {X : Type u} [TopologicalSpace X] [SeparableSpace X] [Nonempty X]
  {E : Type v} [ConditionallyCompleteLattice E] [TopologicalSpace E] [OrderClosedTopology E]
  {f : X → E} (hf : Continuous f) (hf' : BddAbove (Set.range f)) :
  ⨆ x : X, f x = ⨆ i : Nat, f (denseSeq X i) := by
  calc
    _ = sSup (closure (Set.range f)) := by
      exact sSup_eq_closure_sSup (Set.range_nonempty f) hf'
    _ = sSup (closure (Set.range (f ∘ denseSeq X))) := by
      rw [closure_range_eq_closure_denseSeq hf]
    _ = sSup (Set.range (f ∘ denseSeq X)) := by
      have hf'' : BddAbove (Set.range (f ∘ denseSeq X)) := by
        rw [Set.range_comp f (denseSeq X)]
        have := Set.image_subset_range f (Set.range (denseSeq X))
        exact BddAbove.mono this hf'
      exact (sSup_eq_closure_sSup (Set.range_nonempty (f ∘ denseSeq X)) hf'').symm

theorem separableSpaceSup_eq_real {X : Type u} [TopologicalSpace X] [SeparableSpace X] [Nonempty X]
  {f : X → ℝ} (hf : Continuous f) :
  ⨆ x : X, f x = ⨆ i : Nat, f (denseSeq X i) := by
  if bdd : BddAbove (Set.range f) then
    exact separableSpaceSup_eq hf bdd
  else
    have : ¬ (BddAbove (Set.range (f ∘ (denseSeq X)))) := by
      intro h
      have : BddAbove (closure (Set.range (f ∘ (denseSeq X)))) := bddAbove_closure.mpr h
      rw [←closure_range_eq_closure_denseSeq hf] at this
      exact bdd <| bddAbove_closure.mp this
    calc
      _ = 0 := Real.iSup_of_not_bddAbove bdd
      _ = _ := (Real.iSup_of_not_bddAbove this).symm

/--
Restriction of a family to Mathlib's chosen countable dense sequence.

The definition includes its value, rather than merely introducing a type:

`denseRestriction F = F ∘ denseSeq H`.
-/
noncomputable abbrev denseRestriction
    {H : Type u} {α : Type w}
    [TopologicalSpace H] [SeparableSpace H] [Nonempty H]
    (F : H → α) : ℕ → α :=
  F ∘ denseSeq H

@[simp]
lemma denseRestriction_apply
    {H : Type u} {α : Type w}
    [TopologicalSpace H] [SeparableSpace H] [Nonempty H]
    (F : H → α) (i : ℕ) :
    denseRestriction F i = F (denseSeq H i) :=
  rfl

lemma measurable_denseRestriction_apply
    {H : Type u} {α : Type w} {β : Type*}
    [TopologicalSpace H] [SeparableSpace H] [Nonempty H]
    [MeasurableSpace α] [MeasurableSpace β]
    {F : H → α → β} (hF : ∀ h, Measurable (F h)) (i : ℕ) :
    Measurable (denseRestriction F i) :=
  hF (denseSeq H i)

lemma abs_denseRestriction_le
    {H : Type u} {α : Type w}
    [TopologicalSpace H] [SeparableSpace H] [Nonempty H]
    {F : H → α → ℝ} {b : ℝ}
    (hF : ∀ h x, |F h x| ≤ b) :
    ∀ i x, |denseRestriction F i x| ≤ b :=
  fun i x ↦ hF (denseSeq H i) x

/-- Canonical form of `separableSpaceSup_eq_real`: the supremum of a continuous family
over a separable space is the supremum of its restriction to the chosen countable dense
sequence. -/
theorem separableSpaceSup_eq_denseRestriction {X : Type u}
    [TopologicalSpace X] [SeparableSpace X] [Nonempty X]
    {f : X → ℝ} (hf : Continuous f) :
    ⨆ x : X, f x = ⨆ n : ℕ, denseRestriction f n :=
  separableSpaceSup_eq_real hf
