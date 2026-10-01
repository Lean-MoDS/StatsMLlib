/-
Copyright (c) 2026 Kei Tsukamoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kei Tsukamoto
-/
import Mathlib.Data.Finset.Basic

/-!
# Semigraphoids and graphoids

An *independence model* on a vertex type `V` is a ternary relation `I A B C` on finite vertex sets,
read as "`X_A` is independent of `X_B` given `X_C`". Semigraphoids and graphoids are the
independence models satisfying the standard conditional-independence axioms. This module is purely
order-theoretic: it uses no probability, so that the Markov properties of graphical models can be
related using the axioms alone, and probability distributions enter later as instances.

Every axiom is required only on pairwise disjoint vertex sets.

## Main definitions

* `GraphicalModel.Semigraphoid I`: triviality, symmetry, decomposition, weak union, contraction.
* `GraphicalModel.Graphoid I`: a semigraphoid that also satisfies the intersection axiom.

## Main results

* `GraphicalModel.Semigraphoid.decomp_left`: decomposition in the first argument.
-/

namespace GraphicalModel

variable {V : Type*} [DecidableEq V]

/-- A semigraphoid: an independence model satisfying triviality, symmetry, decomposition, weak
union and contraction on pairwise disjoint vertex sets. -/
structure Semigraphoid (I : Finset V → Finset V → Finset V → Prop) : Prop where
  /-- Triviality: everything is independent of the empty set. -/
  trivial : ∀ {A C : Finset V}, Disjoint A C → I A ∅ C
  /-- Symmetry. -/
  symm : ∀ {A B C : Finset V}, Disjoint A B → Disjoint A C → Disjoint B C → I A B C → I B A C
  /-- Decomposition: `A ⫫ B ∪ D | C` implies `A ⫫ B | C`. -/
  decomp : ∀ {A B C D : Finset V}, Disjoint A B → Disjoint A C → Disjoint A D → Disjoint B C →
    Disjoint B D → Disjoint C D → I A (B ∪ D) C → I A B C
  /-- Weak union: `A ⫫ B ∪ D | C` implies `A ⫫ B | C ∪ D`. -/
  weakUnion : ∀ {A B C D : Finset V}, Disjoint A B → Disjoint A C → Disjoint A D → Disjoint B C →
    Disjoint B D → Disjoint C D → I A (B ∪ D) C → I A B (C ∪ D)
  /-- Contraction: `A ⫫ B | C ∪ D` and `A ⫫ D | C` imply `A ⫫ B ∪ D | C`. -/
  contraction : ∀ {A B C D : Finset V}, Disjoint A B → Disjoint A C → Disjoint A D →
    Disjoint B C → Disjoint B D → Disjoint C D → I A B (C ∪ D) → I A D C → I A (B ∪ D) C

/-- A graphoid: a semigraphoid that also satisfies the intersection axiom. -/
structure Graphoid (I : Finset V → Finset V → Finset V → Prop) : Prop extends Semigraphoid I where
  /-- Intersection: `A ⫫ B | C ∪ D` and `A ⫫ D | C ∪ B` imply `A ⫫ B ∪ D | C`. -/
  intersection : ∀ {A B C D : Finset V}, Disjoint A B → Disjoint A C → Disjoint A D →
    Disjoint B C → Disjoint B D → Disjoint C D → I A B (C ∪ D) → I A D (C ∪ B) → I A (B ∪ D) C

namespace Semigraphoid

variable {I : Finset V → Finset V → Finset V → Prop}

/-- Decomposition in the first argument: `A ∪ D ⫫ B | C` implies `A ⫫ B | C`. -/
theorem decomp_left (hI : Semigraphoid I) {A B C D : Finset V} (hAB : Disjoint A B)
    (hAC : Disjoint A C) (hAD : Disjoint A D) (hBC : Disjoint B C) (hBD : Disjoint B D)
    (hCD : Disjoint C D) (h : I (A ∪ D) B C) : I A B C := by
  have hADB : Disjoint (A ∪ D) B := Finset.disjoint_union_left.2 ⟨hAB, hBD.symm⟩
  have hADC : Disjoint (A ∪ D) C := Finset.disjoint_union_left.2 ⟨hAC, hCD.symm⟩
  exact hI.symm hAB.symm hBC hAC <|
    hI.decomp hAB.symm hBC hBD hAC hAD hCD (hI.symm hADB hADC hBC h)

end Semigraphoid

end GraphicalModel
