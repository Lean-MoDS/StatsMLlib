/-
Copyright (c) 2024 Kei Tsukamoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kei Tsukamoto, Kazumi Kasaura, Naoto Onda, Yuma Mizuno, Sho Sonoda
-/
import StatsMLlib.LearningTheory.EmpiricalProcess.Metric
import StatsMLlib.Topology.MetricSpace.CoveringNumber.Basic

/-!
# Empirical Pseudo-Metric Spaces

The sample-indexed empirical pseudo-metric used by the Rademacher Dudley argument. Its norm and
metric structure are induced from StatsMLlib's canonical empirical space.

## Main definitions

* `empiricalNorm`: sample-indexed view of `EmpiricalProcess.empiricalNorm`.
* `empiricalDist`: empirical distance between two functions.
* `EmpiricalFunctionSpace`: a function family equipped with its empirical pseudo-metric.

## Main results

* `empiricalDist_proj`: bounds a sample coordinate by the empirical norm.
-/

universe v
open scoped BigOperators
variable {𝒳 : Type v}
variable {n : ℕ}

/-- The sample-indexed view of StatsMLlib's canonical empirical norm. -/
noncomputable abbrev empiricalNorm (S : Fin n → 𝒳) (f : 𝒳 → ℝ) : ℝ :=
  EmpiricalProcess.empiricalNorm n (fun i ↦ f (S i))

lemma empiricalNorm_def (S : Fin n → 𝒳) (f : 𝒳 → ℝ) :
    empiricalNorm S f = Real.sqrt ((1 / n) * ∑ i : Fin n, (f (S i))^2) :=
  by simp [EmpiricalProcess.empiricalNorm, one_div]

noncomputable def empiricalDist (S : Fin n → 𝒳) (f g : 𝒳 → ℝ) : ℝ :=
  empiricalNorm S (f - g)

@[simp]
lemma empiricalDist_def (S : Fin n → 𝒳) (f g : 𝒳 → ℝ) :
    empiricalDist S f g = empiricalNorm S (f - g) :=
  rfl

@[reducible] noncomputable def empiricalPMet (S : Fin n → 𝒳) :
    PseudoMetricSpace (𝒳 → ℝ) :=
  PseudoMetricSpace.induced
    (fun f ↦ EmpiricalProcess.empiricalMetricImage n S f)
    (EmpiricalProcess.EmpiricalSpace.instPseudoMetricSpace n)

@[simp]
lemma empiricalDist_app (S : Fin n → 𝒳) (f g : 𝒳 → ℝ) :
    empiricalDist S f g = empiricalNorm S (f - g) :=
  rfl

@[simp] lemma empiricalDist_comm (S : Fin n → 𝒳) (f g : 𝒳 → ℝ) :
    empiricalDist S f g = empiricalDist S g f := by
  exact (empiricalPMet S).dist_comm f g

lemma empiricalDist_proj (S : Fin n → 𝒳) (f : 𝒳 → ℝ) (i : Fin n):
    |f (S i)|/√n ≤ empiricalNorm S f := by
  calc
  _ = √(f (S i)^2)/√n := by
    have : √(f (S i)^2) = |f (S i)| := by exact Real.sqrt_sq_eq_abs (f (S i))
    rw [this]
  _ = √((f (S i)^2)/n) := by
    simp
  _ ≤ _ := by
    dsimp [empiricalNorm]
    apply Real.sqrt_le_sqrt
    rw [inv_mul_eq_div]
    refine div_le_div_of_nonneg_right ?_ ?_
    · have hnonneg : ∀ j ∈ Finset.univ, 0 ≤ (f (S j))^2 := by
        intro j hj; exact sq_nonneg _
      have hi : i ∈ Finset.univ := by simp
      simpa using
        (Finset.single_le_sum
          (s := Finset.univ)
          (f := fun j => (f (S j))^2)
          hnonneg hi)
    · simp

section

universe u
variable {ι : Type u} {F : ι → 𝒳 → ℝ}
variable {S : Fin n → 𝒳}

structure EmpiricalFunctionSpace (F : ι → 𝒳 → ℝ) (S : Fin n → 𝒳) where
  index : ι

instance : CoeFun (EmpiricalFunctionSpace F S) (fun _ ↦ 𝒳 → ℝ) where
  coe f := F f.index

@[simps!]
noncomputable instance : Dist (EmpiricalFunctionSpace F S) where
  dist f g := empiricalDist S f g

noncomputable instance : PseudoMetricSpace (EmpiricalFunctionSpace F S) :=
  PseudoMetricSpace.induced (fun f ↦ F f.index) (empiricalPMet S)

end
