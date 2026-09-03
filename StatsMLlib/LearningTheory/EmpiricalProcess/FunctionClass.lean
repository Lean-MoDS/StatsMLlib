/-
Copyright (c) 2024 Kei Tsukamoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kei Tsukamoto, Kazumi Kasaura, Naoto Onda, Yuma Mizuno, Sho Sonoda
-/
import StatsMLlib.LearningTheory.EmpiricalProcess.Metric
import StatsMLlib.Topology.MetricSpace.CoveringNumber.Basic
import StatsMLlib.Analysis.FiniteSample

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


@[simp]
lemma empiricalNorm_neg (S : Fin n → 𝒳) (f : 𝒳 → ℝ) :
    empiricalNorm S (-f) = empiricalNorm S f := by
  simp [empiricalNorm, EmpiricalProcess.empiricalNorm]

@[simp]
lemma empiricalDist_neg_neg (S : Fin n → 𝒳) (f g : 𝒳 → ℝ) :
    empiricalDist S (-f) (-g) = empiricalDist S f g := by
  rw [empiricalDist, empiricalDist]
  have h : (-f) - (-g) = -(f - g) := by
    ext x
    dsimp
    ring
  rw [h, empiricalNorm_neg]

/--
The empirical norm is at most a uniform bound on the sampled coordinates.
-/
lemma empiricalNorm_le_of_abs_le
    (hn : 0 < n) (S : Fin n → 𝒳) (f : 𝒳 → ℝ)
    {b : ℝ} (hb : 0 ≤ b) (hf : ∀ k, |f (S k)| ≤ b) :
    empiricalNorm S f ≤ b := by
  have havg :
      (n : ℝ)⁻¹ * ∑ k : Fin n, f (S k) ^ 2 ≤ b ^ 2 := by
    calc
      (n : ℝ)⁻¹ * ∑ k : Fin n, f (S k) ^ 2 ≤
          |(n : ℝ)⁻¹ * ∑ k : Fin n, f (S k) ^ 2| :=
        le_abs_self _
      _ ≤ b ^ 2 := by
        apply abs_normalized_fin_sum_le hn
          (fun k (_ : Unit) ↦ f (S k) ^ 2) (fun _ ↦ ())
        intro k _
        rw [abs_of_nonneg (sq_nonneg _)]
        rw [← sq_abs]
        exact (sq_le_sq₀ (abs_nonneg _) hb).2 (hf k)
  calc
    empiricalNorm S f =
        Real.sqrt ((n : ℝ)⁻¹ * ∑ k : Fin n, f (S k) ^ 2) := by
      simp only [empiricalNorm, EmpiricalProcess.empiricalNorm]
    _ ≤ Real.sqrt (b ^ 2) := Real.sqrt_le_sqrt havg
    _ = b := by rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hb]

/--
A pointwise Lipschitz estimate on a sample implies the same estimate for the
empirical pseudometric.
-/
lemma empiricalDist_le_of_abs_sub_le
    (hn : 0 < n) (S : Fin n → 𝒳) (f g : 𝒳 → ℝ)
    {b : ℝ} (hb : 0 ≤ b)
    (hfg : ∀ k, |f (S k) - g (S k)| ≤ b) :
    empiricalDist S f g ≤ b := by
  rw [empiricalDist]
  apply empiricalNorm_le_of_abs_le hn S (f - g) hb
  intro k
  exact hfg k



instance [Nonempty ι] : Nonempty (EmpiricalFunctionSpace F S) :=
  ⟨⟨Classical.choice inferInstance⟩⟩

/-- `EmpiricalFunctionSpace F S` has the same underlying indices as `ι`. -/
def empiricalFunctionSpaceEquiv :
    EmpiricalFunctionSpace F S ≃ ι where
  toFun q := q.index
  invFun h := ⟨h⟩
  left_inv q := by cases q; rfl
  right_inv _ := rfl

noncomputable instance [Fintype ι] :
    Fintype (EmpiricalFunctionSpace F S) :=
  Fintype.ofEquiv ι empiricalFunctionSpaceEquiv.symm

@[simp]
lemma card_empiricalFunctionSpace [Fintype ι] :
    Fintype.card (EmpiricalFunctionSpace F S) = Fintype.card ι :=
  Fintype.card_congr empiricalFunctionSpaceEquiv

-- The left-hand side has a variable head, so Lean warns that this would be tried
-- on every `simp` step. Later modules rely on it firing implicitly, so the
-- attribute is kept and the warning silenced here rather than dropping it.
set_option warning.simp.varHead false in
@[simp] lemma EmpiricalFunctionSpace.coe_apply
    (q : EmpiricalFunctionSpace F S) :
    (q : 𝒳 → ℝ) = F q.index := rfl

/-- A finitely indexed empirical function space is totally bounded. -/
lemma empiricalFunctionSpace_totallyBounded [Fintype ι] :
    TotallyBounded
      (Set.univ : Set (EmpiricalFunctionSpace F S)) :=
  Set.finite_univ.totallyBounded
end
