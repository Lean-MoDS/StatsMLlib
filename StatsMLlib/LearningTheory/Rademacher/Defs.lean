/-
Copyright (c) 2024 Kei Tsukamoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kei Tsukamoto, Kazumi Kasaura, Naoto Onda, Yuma Mizuno, Sho Sonoda
-/
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Notation

/-!
# Rademacher Complexity Definitions

Core definitions for empirical Rademacher complexity and uniform deviations.

## Main definitions

* `Signs`: finite vectors of Rademacher signs.
* `empiricalRademacherComplexity`: empirical Rademacher complexity of a function class.
* `rademacherComplexity`: expected empirical Rademacher complexity.

## Main results

This module supplies definitions used by the downstream symmetrization and concentration results.
-/

noncomputable
section

universe u v w

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal

variable {n : ℕ}

@[reducible] def Signs (n : ℕ) : Type := Fin n → ({-1, 1} : Finset ℤ)

instance : Fintype (Signs n) := inferInstanceAs (Fintype (Fin n → { x // x ∈ {-1, 1} }))

instance : Neg { x // x ∈ ({-1, 1} : Finset ℤ) } where
  neg x := ⟨-x.val, by
    cases x with
    | mk val h =>
      simp at h
      cases h
      · simp [*]
      · simp [*]
  ⟩

variable {Ω : Type u} [MeasurableSpace Ω] {ι : Type v} {𝒳 : Type w}

set_option hygiene false

local notation "μⁿ" => Measure.pi (fun _ ↦ μ)

def empiricalRademacherComplexity (n : ℕ) (f : ι → 𝒳 → ℝ) (S : Fin n → 𝒳) : ℝ :=
  (Fintype.card (Signs n) : ℝ)⁻¹ *
    ∑ σ : Signs n, ⨆ i, |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * f i (S k)|

def rademacherComplexity (n : ℕ) (f : ι → 𝒳 → ℝ) (μ : Measure Ω) (X : Ω → 𝒳) : ℝ :=
  μⁿ[fun ω : Fin n → Ω ↦ empiricalRademacherComplexity n f (X ∘ ω)]

def empiricalRademacherComplexity_without_abs (n : ℕ) (f : ι → 𝒳 → ℝ) (S : Fin n → 𝒳) : ℝ :=
  (Fintype.card (Signs n) : ℝ)⁻¹ *
    ∑ σ : Signs n, ⨆ i, (n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * f i (S k)

end
