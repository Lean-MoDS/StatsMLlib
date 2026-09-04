/-
Copyright (c) 2026 Kei Tsukamoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sho Sonoda, Kei Tsukamoto
-/
import StatsMLlib.Analysis.FiniteSample
import StatsMLlib.LearningTheory.EmpiricalRiskMinimization.Defs
import StatsMLlib.LearningTheory.Rademacher.Signs

/-!
# A Rademacher contraction inequality for a uniformly bounded class

For the absolute empirical Rademacher complexity used in this project, a
Lipschitz map vanishing at zero costs a factor `2`.  The factor appears when
the absolute supremum is split into its positive and negative one-sided
parts.  For the one-sided convention the contraction lemma below has factor
`1`.

The hypothesis type carries no structure; the class is assumed uniformly
bounded, which is what makes the suprema over hypotheses meaningful.
-/

noncomputable section

universe u v

open Real
open scoped BigOperators

variable {H : Type u} {𝒳 : Type v}

private lemma bddAbove_range_of_forall_le {ι : Type*} {f : ι → ℝ} {M : ℝ}
    (hf : ∀ i, f i ≤ M) : BddAbove (Set.range f) :=
  ⟨M, by rintro _ ⟨i, rfl⟩; exact hf i⟩

/-- A normalized signed average of a uniformly bounded family stays in `[-b, b]`. -/
private lemma abs_signedAverage_le {ι : Type*} {n : ℕ}
    (f : ι → 𝒳 → ℝ) (S : Fin n → 𝒳) (σ : Signs n) {b : ℝ}
    (hb : 0 ≤ b) (hf : ∀ i x, |f i x| ≤ b) (i : ι) :
    |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * f i (S k)| ≤ b := by
  by_cases hn : n = 0
  · subst hn
    simpa using hb
  · exact abs_normalized_fin_sum_le (Nat.pos_of_ne_zero hn)
      (fun k x ↦ (σ k : ℝ) * f i x) S
      (fun k x ↦ by simpa [abs_mul, abs_sigma] using hf i x)

/--
The one-coordinate contraction step.  Both suprema on the right have to be
bounded above for the comparison to be meaningful.
-/
private lemma two_iSup_contraction
    [Nonempty H]
    (A x : H → ℝ) (ψ : ℝ → ℝ) {L : ℝ}
    (hbddP : BddAbove (Set.range fun h ↦ A h + L * x h))
    (hbddM : BddAbove (Set.range fun h ↦ A h - L * x h))
    (hψ : ∀ u v, |ψ u - ψ v| ≤ L * |u - v|) :
    (⨆ h, A h + ψ (x h)) + (⨆ h, A h - ψ (x h)) ≤
      (⨆ h, A h + L * x h) + (⨆ h, A h - L * x h) := by
  refine ciSup_add_ciSup_le ?_
  intro h₁ h₂
  by_cases hx : x h₂ ≤ x h₁
  · have hdiff : ψ (x h₁) - ψ (x h₂) ≤ L * (x h₁ - x h₂) := by
      calc
        ψ (x h₁) - ψ (x h₂) ≤ |ψ (x h₁) - ψ (x h₂)| :=
          le_abs_self _
        _ ≤ L * |x h₁ - x h₂| := hψ _ _
        _ = L * (x h₁ - x h₂) := by rw [abs_of_nonneg (sub_nonneg.mpr hx)]
    calc
      (A h₁ + ψ (x h₁)) + (A h₂ - ψ (x h₂)) =
          A h₁ + A h₂ + (ψ (x h₁) - ψ (x h₂)) := by ring
      _ ≤ A h₁ + A h₂ + L * (x h₁ - x h₂) := by linarith
      _ = (A h₁ + L * x h₁) + (A h₂ - L * x h₂) := by ring
      _ ≤ (⨆ h, A h + L * x h) + (⨆ h, A h - L * x h) :=
        add_le_add (le_ciSup hbddP h₁) (le_ciSup hbddM h₂)
  · have hx' : x h₁ ≤ x h₂ := le_of_not_ge hx
    have hdiff : ψ (x h₁) - ψ (x h₂) ≤ L * (x h₂ - x h₁) := by
      calc
        ψ (x h₁) - ψ (x h₂) ≤ |ψ (x h₁) - ψ (x h₂)| :=
          le_abs_self _
        _ ≤ L * |x h₁ - x h₂| := hψ _ _
        _ = L * (x h₂ - x h₁) := by
          rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hx')]
    calc
      (A h₁ + ψ (x h₁)) + (A h₂ - ψ (x h₂)) =
          A h₁ + A h₂ + (ψ (x h₁) - ψ (x h₂)) := by ring
      _ ≤ A h₁ + A h₂ + L * (x h₂ - x h₁) := by linarith
      _ = (A h₂ + L * x h₂) + (A h₁ - L * x h₁) := by ring
      _ ≤ (⨆ h, A h + L * x h) + (⨆ h, A h - L * x h) :=
        add_le_add (le_ciSup hbddP h₂) (le_ciSup hbddM h₁)

/--
The finite-sign, one-sided contraction principle, strengthened by an arbitrary
offset `c`.  The offset is what makes induction over the sample coordinates
possible.
-/
private theorem sum_iSup_contraction_one_sided
    [Nonempty H]
    (n : ℕ) (a : H → Fin n → ℝ) (ψ : Fin n → ℝ → ℝ)
    (c : H → ℝ) {L b : ℝ} (hL : 0 ≤ L)
    (ha : ∀ h k, |a h k| ≤ b)
    (hc : BddAbove (Set.range c))
    (hψ : ∀ k u v, |ψ k u - ψ k v| ≤ L * |u - v|) :
    (∑ σ : Signs n,
        ⨆ h, c h + ∑ k : Fin n, (σ k : ℝ) * ψ k (a h k)) ≤
      ∑ σ : Signs n,
        ⨆ h, c h + L * ∑ k : Fin n, (σ k : ℝ) * a h k := by
  induction n generalizing c with
  | zero =>
      simp
  | succ m ih =>
      let a₀ : H → Fin m → ℝ := fun h k ↦ a h k.castSucc
      let ψ₀ : Fin m → ℝ → ℝ := fun k ↦ ψ k.castSucc
      let x : H → ℝ := fun h ↦ a h (Fin.last m)
      have hψ₀ : ∀ k u v, |ψ₀ k u - ψ₀ k v| ≤ L * |u - v| :=
        fun k u v ↦ hψ k.castSucc u v
      have ha₀ : ∀ h k, |a₀ h k| ≤ b := fun h k ↦ ha h k.castSucc
      have hxb : ∀ h, |x h| ≤ b := fun h ↦ ha h (Fin.last m)
      obtain ⟨C, hC⟩ := hc
      have hCle : ∀ h, c h ≤ C := fun h ↦ hC ⟨h, rfl⟩
      have hLx : ∀ h, |L * x h| ≤ L * b := by
        intro h
        rw [abs_mul, abs_of_nonneg hL]
        exact mul_le_mul_of_nonneg_left (hxb h) hL
      have hψb : ∀ (k : Fin (m + 1)) (h : H),
          |ψ k (a h k)| ≤ |ψ k 0| + L * b := by
        intro k h
        have h1 : |ψ k (a h k) - ψ k 0| ≤ L * |a h k - 0| := hψ k _ _
        have h2 : L * |a h k - 0| ≤ L * b := by
          rw [sub_zero]
          exact mul_le_mul_of_nonneg_left (ha h k) hL
        have h3 : |ψ k (a h k)| ≤ |ψ k (a h k) - ψ k 0| + |ψ k 0| := by
          simpa using abs_add_le (ψ k (a h k) - ψ k 0) (ψ k 0)
        linarith
      have hsum : ∀ (τ : Signs m) (h : H),
          |∑ k : Fin m, (τ k : ℝ) * ψ₀ k (a₀ h k)| ≤
            ∑ k : Fin m, (|ψ k.castSucc 0| + L * b) := by
        intro τ h
        calc
          |∑ k : Fin m, (τ k : ℝ) * ψ₀ k (a₀ h k)| ≤
              ∑ k : Fin m, |(τ k : ℝ) * ψ₀ k (a₀ h k)| :=
            Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ k : Fin m, (|ψ k.castSucc 0| + L * b) := by
            apply Finset.sum_le_sum
            intro k _
            rw [abs_mul, abs_sigma, one_mul]
            exact hψb k.castSucc h
      have hbddP : ∀ τ : Signs m,
          BddAbove (Set.range fun h ↦
            (c h + ∑ k : Fin m, (τ k : ℝ) * ψ₀ k (a₀ h k)) + L * x h) := by
        intro τ
        refine bddAbove_range_of_forall_le
          (M := C + (∑ k : Fin m, (|ψ k.castSucc 0| + L * b)) + L * b) ?_
        intro h
        have h1 : ∑ k : Fin m, (τ k : ℝ) * ψ₀ k (a₀ h k) ≤
            ∑ k : Fin m, (|ψ k.castSucc 0| + L * b) :=
          (le_abs_self _).trans (hsum τ h)
        have h2 : L * x h ≤ L * b := (le_abs_self _).trans (hLx h)
        linarith [hCle h]
      have hbddM : ∀ τ : Signs m,
          BddAbove (Set.range fun h ↦
            (c h + ∑ k : Fin m, (τ k : ℝ) * ψ₀ k (a₀ h k)) - L * x h) := by
        intro τ
        refine bddAbove_range_of_forall_le
          (M := C + (∑ k : Fin m, (|ψ k.castSucc 0| + L * b)) + L * b) ?_
        intro h
        have h1 : ∑ k : Fin m, (τ k : ℝ) * ψ₀ k (a₀ h k) ≤
            ∑ k : Fin m, (|ψ k.castSucc 0| + L * b) :=
          (le_abs_self _).trans (hsum τ h)
        have h2 : -(L * x h) ≤ L * b := (neg_le_abs _).trans (hLx h)
        linarith [hCle h]
      have hcM : BddAbove (Set.range fun h ↦ c h - L * x h) := by
        refine bddAbove_range_of_forall_le (M := C + L * b) ?_
        intro h
        have h2 : -(L * x h) ≤ L * b := (neg_le_abs _).trans (hLx h)
        linarith [hCle h]
      have hcP : BddAbove (Set.range fun h ↦ c h + L * x h) := by
        refine bddAbove_range_of_forall_le (M := C + L * b) ?_
        intro h
        have h2 : L * x h ≤ L * b := (le_abs_self _).trans (hLx h)
        linarith [hCle h]
      have hlast :
          ∑ τ : Signs m,
              ((⨆ h,
                  c h + (∑ k : Fin m, (τ k : ℝ) * ψ₀ k (a₀ h k)) +
                    ψ (Fin.last m) (x h)) +
                (⨆ h,
                  c h + (∑ k : Fin m, (τ k : ℝ) * ψ₀ k (a₀ h k)) -
                    ψ (Fin.last m) (x h))) ≤
            ∑ τ : Signs m,
              ((⨆ h,
                  c h + (∑ k : Fin m, (τ k : ℝ) * ψ₀ k (a₀ h k)) +
                    L * x h) +
                (⨆ h,
                  c h + (∑ k : Fin m, (τ k : ℝ) * ψ₀ k (a₀ h k)) -
                    L * x h)) := by
        apply Finset.sum_le_sum
        intro τ _
        let A : H → ℝ :=
          fun h ↦ c h + ∑ k : Fin m, (τ k : ℝ) * ψ₀ k (a₀ h k)
        simpa [A, add_assoc] using
          two_iSup_contraction A x (ψ (Fin.last m))
            (hbddP τ) (hbddM τ) (hψ (Fin.last m))
      have hminus :=
        ih (a := a₀) (ψ := ψ₀) (c := fun h ↦ c h - L * x h) ha₀ hcM hψ₀
      have hplus :=
        ih (a := a₀) (ψ := ψ₀) (c := fun h ↦ c h + L * x h) ha₀ hcP hψ₀
      let q : ℤ → Signs m → ℝ :=
        fun s τ ↦
          ⨆ h,
            c h +
              ((∑ k : Fin m, (τ k : ℝ) * ψ₀ k (a₀ h k)) +
                (s : ℝ) * ψ (Fin.last m) (x h))
      let qL : ℤ → Signs m → ℝ :=
        fun s τ ↦
          ⨆ h,
            c h +
              L *
                ((∑ k : Fin m, (τ k : ℝ) * a₀ h k) +
                  (s : ℝ) * x h)
      calc
        (∑ σ : Signs (m + 1),
            ⨆ h, c h + ∑ k : Fin (m + 1),
              (σ k : ℝ) * ψ k (a h k)) =
          ∑ σ : Signs (m + 1), q (σ (Fin.last m)) (Fin.init σ) := by
              apply Finset.sum_congr rfl
              intro σ _
              dsimp only [q]
              apply congrArg
              funext h
              rw [Fin.sum_univ_castSucc]
              rfl
        _ =
          ∑ s ∈ ({-1, 1} : Finset ℤ), ∑ τ : Signs m,
              ⨆ h,
                c h +
                  ((∑ k : Fin m, (τ k : ℝ) * ψ₀ k (a₀ h k)) +
                    (s : ℝ) * ψ (Fin.last m) (x h)) := by
              exact (sigma_eq (n := m) q).symm
        _ =
            ∑ τ : Signs m,
              ((⨆ h,
                  c h + (∑ k : Fin m, (τ k : ℝ) * ψ₀ k (a₀ h k)) -
                    ψ (Fin.last m) (x h)) +
                (⨆ h,
                  c h + (∑ k : Fin m, (τ k : ℝ) * ψ₀ k (a₀ h k)) +
                    ψ (Fin.last m) (x h))) := by
              simp [Finset.sum_add_distrib, add_comm, add_left_comm]
              apply Finset.sum_congr rfl
              intro τ _
              apply congrArg
              funext h
              ring
        _ ≤ ∑ τ : Signs m,
              ((⨆ h,
                  c h + (∑ k : Fin m, (τ k : ℝ) * ψ₀ k (a₀ h k)) -
                    L * x h) +
                (⨆ h,
                  c h + (∑ k : Fin m, (τ k : ℝ) * ψ₀ k (a₀ h k)) +
                    L * x h)) := by
              simpa [add_comm] using hlast
        _ = (∑ τ : Signs m,
              ⨆ h,
                (c h - L * x h) +
                  ∑ k : Fin m, (τ k : ℝ) * ψ₀ k (a₀ h k)) +
            ∑ τ : Signs m,
              ⨆ h,
                (c h + L * x h) +
                  ∑ k : Fin m, (τ k : ℝ) * ψ₀ k (a₀ h k) := by
              simp only [Finset.sum_add_distrib]
              congr 1 <;> apply Finset.sum_congr rfl <;> intro τ _ <;>
                apply congrArg <;> funext h <;> ring
        _ ≤ (∑ τ : Signs m,
              ⨆ h,
                (c h - L * x h) +
                  L * ∑ k : Fin m, (τ k : ℝ) * a₀ h k) +
            ∑ τ : Signs m,
              ⨆ h,
                (c h + L * x h) +
                  L * ∑ k : Fin m, (τ k : ℝ) * a₀ h k :=
              add_le_add hminus hplus
        _ = ∑ s ∈ ({-1, 1} : Finset ℤ), ∑ τ : Signs m,
              ⨆ h,
                c h +
                  L *
                    ((∑ k : Fin m, (τ k : ℝ) * a₀ h k) +
                      (s : ℝ) * x h) := by
              simp [add_comm, add_assoc]
              congr 1 <;> apply Finset.sum_congr rfl <;> intro τ _ <;>
                apply congrArg <;> funext h <;> ring
        _ = ∑ σ : Signs (m + 1), qL (σ (Fin.last m)) (Fin.init σ) :=
              sigma_eq (n := m) qL
        _ = ∑ σ : Signs (m + 1),
              ⨆ h, c h + L * ∑ k : Fin (m + 1),
                (σ k : ℝ) * a h k := by
              apply Finset.sum_congr rfl
              intro σ _
              dsimp only [qL]
              apply congrArg
              funext h
              rw [Fin.sum_univ_castSucc]
              rfl

/--
One-sided empirical Rademacher contraction for a uniformly bounded class.

Unlike the absolute convention, the one-sided convention has constant `L`.
The map may depend on the observation `x`; this is useful for supervised
losses, where the contraction map depends on the observed label.
-/
theorem empiricalRademacherComplexity_without_abs_contraction
    [Nonempty H]
    (n : ℕ) (F : H → 𝒳 → ℝ) (ψ : 𝒳 → ℝ → ℝ)
    (S : Fin n → 𝒳) {L b : ℝ} (hL : 0 ≤ L)
    (hF : ∀ h x, |F h x| ≤ b)
    (hψ : ∀ x u v, |ψ x u - ψ x v| ≤ L * |u - v|) :
    empiricalRademacherComplexity_without_abs n
        (fun h x ↦ ψ x (F h x)) S ≤
      L * empiricalRademacherComplexity_without_abs n F S := by
  let q : ℝ := (n : ℝ)⁻¹
  have hq : 0 ≤ q := by positivity
  have hcontract :=
    sum_iSup_contraction_one_sided (L := q * L) (b := b) n
      (fun h k ↦ F h (S k))
      (fun k u ↦ q * ψ (S k) u)
      (fun _ ↦ 0) (mul_nonneg hq hL)
      (fun h k ↦ hF h (S k))
      (bddAbove_range_of_forall_le (M := (0 : ℝ)) (fun _ ↦ le_rfl))
      (by
        intro k u v
        rw [← mul_sub, abs_mul, abs_of_nonneg hq]
        calc
          q * |ψ (S k) u - ψ (S k) v| ≤
              q * (L * |u - v|) := by
            gcongr
            exact hψ (S k) u v
          _ = (q * L) * |u - v| := by ring)
  dsimp only [empiricalRademacherComplexity_without_abs]
  calc
    (Fintype.card (Signs n) : ℝ)⁻¹ *
        (∑ σ : Signs n,
        ⨆ h, (n : ℝ)⁻¹ *
          ∑ k : Fin n, (σ k : ℝ) * ψ (S k) (F h (S k))) =
      (Fintype.card (Signs n) : ℝ)⁻¹ *
        (∑ σ : Signs n,
          ⨆ h, (0 : ℝ) +
            ∑ k : Fin n, (σ k : ℝ) *
              (q * ψ (S k) (F h (S k)))) := by
        congr 1
        apply Finset.sum_congr rfl
        intro σ _
        apply congrArg
        funext h
        simp only [zero_add, q]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        ring
    _ ≤ (Fintype.card (Signs n) : ℝ)⁻¹ *
        (∑ σ : Signs n,
          ⨆ h, (0 : ℝ) + (q * L) *
            ∑ k : Fin n, (σ k : ℝ) * F h (S k)) :=
      mul_le_mul_of_nonneg_left hcontract (by positivity)
    _ = (Fintype.card (Signs n) : ℝ)⁻¹ *
        (L * ∑ σ : Signs n,
          ⨆ h, (n : ℝ)⁻¹ *
            ∑ k : Fin n, (σ k : ℝ) * F h (S k)) := by
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro σ _
      rw [Real.mul_iSup_of_nonneg hL]
      apply congrArg
      funext h
      simp only [zero_add, q]
      ring
    _ = L * ((Fintype.card (Signs n) : ℝ)⁻¹ *
        ∑ σ : Signs n,
          ⨆ h, (n : ℝ)⁻¹ *
            ∑ k : Fin n, (σ k : ℝ) * F h (S k)) := by ring

/-- Add a zero function to a function class. -/
def withZeroClass (F : H → 𝒳 → ℝ) : Option H → 𝒳 → ℝ
  | none, _ => 0
  | some h, x => F h x

private lemma empiricalRademacherComplexity_le_pos_add_neg
    [Nonempty H]
    (n : ℕ) (G : H → 𝒳 → ℝ) (S : Fin n → 𝒳) {b : ℝ} (hb : 0 ≤ b)
    (hG : ∀ h x, |G h x| ≤ b) :
    empiricalRademacherComplexity n G S ≤
      empiricalRademacherComplexity_without_abs n (withZeroClass G) S +
      empiricalRademacherComplexity_without_abs n
        (fun oh x ↦ -withZeroClass G oh x) S := by
  dsimp only [empiricalRademacherComplexity,
    empiricalRademacherComplexity_without_abs]
  rw [← mul_add, ← Finset.sum_add_distrib]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro σ _
  let A : H → ℝ :=
    fun h ↦ (n : ℝ)⁻¹ *
      ∑ k : Fin n, (σ k : ℝ) * G h (S k)
  let B : Option H → ℝ
    | none => 0
    | some h => A h
  have hA : ∀ h, |A h| ≤ b := fun h ↦ abs_signedAverage_le G S σ hb hG h
  have hB : ∀ oh, |B oh| ≤ b := by
    intro oh
    cases oh with
    | none => simpa [B] using hb
    | some h => exact hA h
  have hBbdd : BddAbove (Set.range B) :=
    bddAbove_range_of_forall_le fun oh ↦ (le_abs_self _).trans (hB oh)
  have hBbdd' : BddAbove (Set.range fun oh ↦ -B oh) :=
    bddAbove_range_of_forall_le fun oh ↦ (neg_le_abs _).trans (hB oh)
  have hneg :
      (fun oh : Option H ↦
        (n : ℝ)⁻¹ * ∑ k : Fin n,
          (σ k : ℝ) * -withZeroClass G oh (S k)) = fun oh ↦ -B oh := by
    funext oh
    cases oh <;> simp [B, A, withZeroClass, Finset.sum_neg_distrib]
  have hpos :
      (fun oh : Option H ↦
        (n : ℝ)⁻¹ * ∑ k : Fin n,
          (σ k : ℝ) * withZeroClass G oh (S k)) = B := by
    funext oh
    cases oh <;> simp [B, A, withZeroClass]
  rw [hpos, hneg]
  apply ciSup_le
  intro h
  rw [abs_eq_max_neg]
  apply max_le
  · calc
      A h ≤ ⨆ oh, B oh := le_ciSup hBbdd (some h)
      _ ≤ (⨆ oh, B oh) + ⨆ oh, -B oh := by
        have hz : 0 ≤ ⨆ oh, -B oh := by
          have : (0 : ℝ) = -B none := by simp [B]
          rw [this]
          exact le_ciSup hBbdd' none
        linarith
  · calc
      -A h ≤ ⨆ oh, -B oh := le_ciSup hBbdd' (some h)
      _ ≤ (⨆ oh, B oh) + ⨆ oh, -B oh := by
        have hz : 0 ≤ ⨆ oh, B oh := by
          have : (0 : ℝ) = B none := by simp [B]
          rw [this]
          exact le_ciSup hBbdd none
        linarith

private lemma empiricalRademacherComplexity_without_abs_withZero_le
    [Nonempty H]
    (n : ℕ) (F : H → 𝒳 → ℝ) (S : Fin n → 𝒳) {b : ℝ} (hb : 0 ≤ b)
    (hF : ∀ h x, |F h x| ≤ b) :
    empiricalRademacherComplexity_without_abs n (withZeroClass F) S ≤
      empiricalRademacherComplexity n F S := by
  dsimp only [empiricalRademacherComplexity_without_abs,
    empiricalRademacherComplexity]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro σ _
  have hbdd : BddAbove (Set.range fun h ↦ |(n : ℝ)⁻¹ *
      ∑ k : Fin n, (σ k : ℝ) * F h (S k)|) :=
    bddAbove_range_of_forall_le fun h ↦ abs_signedAverage_le F S σ hb hF h
  apply ciSup_le
  intro oh
  cases oh with
  | none =>
      simp only [withZeroClass, mul_zero, Finset.sum_const_zero, mul_zero]
      exact Real.iSup_nonneg fun h ↦
        abs_nonneg ((n : ℝ)⁻¹ *
          ∑ k : Fin n, (σ k : ℝ) * F h (S k))
  | some h =>
      calc
        (n : ℝ)⁻¹ *
            ∑ k : Fin n, (σ k : ℝ) * withZeroClass F (some h) (S k) =
            (n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * F h (S k) := by
          rfl
        _ ≤ |(n : ℝ)⁻¹ *
            ∑ k : Fin n, (σ k : ℝ) * F h (S k)| :=
          le_abs_self _
        _ ≤ ⨆ h, |(n : ℝ)⁻¹ *
            ∑ k : Fin n, (σ k : ℝ) * F h (S k)| :=
          le_ciSup hbdd h

/--
Absolute empirical Rademacher contraction for a uniformly bounded class.

Because `empiricalRademacherComplexity` takes an absolute value inside the
hypothesis supremum, the general Lipschitz contraction constant is `2 * L`.
For the one-sided definition, use
`empiricalRademacherComplexity_without_abs_contraction`, whose constant is `L`.
-/
theorem empiricalRademacherComplexity_contraction
    [Nonempty H]
    (n : ℕ) (F : H → 𝒳 → ℝ) (ψ : 𝒳 → ℝ → ℝ)
    (S : Fin n → 𝒳) {L b : ℝ} (hL : 0 ≤ L) (hb : 0 ≤ b)
    (hF : ∀ h x, |F h x| ≤ b)
    (hψ_zero : ∀ x, ψ x 0 = 0)
    (hψ : ∀ x u v, |ψ x u - ψ x v| ≤ L * |u - v|) :
    empiricalRademacherComplexity n
        (fun h x ↦ ψ x (F h x)) S ≤
      2 * L * empiricalRademacherComplexity n F S := by
  let G : H → 𝒳 → ℝ := fun h x ↦ ψ x (F h x)
  have hGbound : ∀ h x, |G h x| ≤ L * b := by
    intro h x
    have h1 : |ψ x (F h x) - ψ x 0| ≤ L * |F h x - 0| := hψ x _ _
    rw [hψ_zero x, sub_zero, sub_zero] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left (hF h x) hL)
  have hFO : ∀ (oh : Option H) (x : 𝒳), |withZeroClass F oh x| ≤ b := by
    intro oh x
    cases oh with
    | none => simpa [withZeroClass] using hb
    | some h => exact hF h x
  have hsplit :=
    empiricalRademacherComplexity_le_pos_add_neg n G S
      (mul_nonneg hL hb) hGbound
  have hpos :
      empiricalRademacherComplexity_without_abs n (withZeroClass G) S ≤
        L * empiricalRademacherComplexity_without_abs n
          (withZeroClass F) S := by
    have hclass :
        (fun oh x ↦ ψ x (withZeroClass F oh x)) = withZeroClass G := by
      funext oh x
      cases oh <;> simp [withZeroClass, G, hψ_zero]
    rw [← hclass]
    exact empiricalRademacherComplexity_without_abs_contraction
      n (withZeroClass F) ψ S hL hFO hψ
  have hneg :
      empiricalRademacherComplexity_without_abs n
          (fun oh x ↦ -withZeroClass G oh x) S ≤
        L * empiricalRademacherComplexity_without_abs n
          (withZeroClass F) S := by
    let ψneg : 𝒳 → ℝ → ℝ := fun x u ↦ -ψ x u
    have hψneg : ∀ x u v, |ψneg x u - ψneg x v| ≤ L * |u - v| := by
      intro x u v
      change |-ψ x u - -ψ x v| ≤ L * |u - v|
      rw [show -ψ x u - -ψ x v = -(ψ x u - ψ x v) by ring, abs_neg]
      exact hψ x u v
    have hclass :
        (fun oh x ↦ ψneg x (withZeroClass F oh x)) =
          fun oh x ↦ -withZeroClass G oh x := by
      funext oh x
      cases oh <;> simp [withZeroClass, G, ψneg, hψ_zero]
    rw [← hclass]
    exact empiricalRademacherComplexity_without_abs_contraction
      n (withZeroClass F) ψneg S hL hFO hψneg
  have hraw :=
    empiricalRademacherComplexity_without_abs_withZero_le n F S hb hF
  calc
    empiricalRademacherComplexity n G S ≤
        empiricalRademacherComplexity_without_abs n (withZeroClass G) S +
          empiricalRademacherComplexity_without_abs n
            (fun oh x ↦ -withZeroClass G oh x) S :=
      hsplit
    _ ≤ L * empiricalRademacherComplexity_without_abs n
          (withZeroClass F) S +
        L * empiricalRademacherComplexity_without_abs n
          (withZeroClass F) S :=
      add_le_add hpos hneg
    _ ≤ L * empiricalRademacherComplexity n F S +
        L * empiricalRademacherComplexity n F S := by
      gcongr
    _ = 2 * L * empiricalRademacherComplexity n F S := by ring

/--
Contraction for a centered supervised loss class over a uniformly bounded
predictor class.  The loss is centered by subtracting `loss 0 y`, so the
contraction map vanishes at zero.
-/
theorem empiricalRademacherComplexity_centered_supervisedLossClass_le
    {𝒴 : Type*}
    [Nonempty H]
    (n : ℕ) (F : H → 𝒳 → ℝ) (loss : ℝ → 𝒴 → ℝ)
    (S : Fin n → 𝒳 × 𝒴) {L b : ℝ} (hL : 0 ≤ L) (hb : 0 ≤ b)
    (hF : ∀ h x, |F h x| ≤ b)
    (hloss : ∀ y u v, |loss u y - loss v y| ≤ L * |u - v|) :
    empiricalRademacherComplexity n
        (supervisedLossClass F (centeredLoss loss)) S ≤
      2 * L *
        empiricalRademacherComplexity n
          (fun (h : H) (z : 𝒳 × 𝒴) ↦ F h z.1) S := by
  apply empiricalRademacherComplexity_contraction
    n (fun (h : H) (z : 𝒳 × 𝒴) ↦ F h z.1)
      (fun z u ↦ centeredLoss loss u z.2) S hL hb
    (fun h z ↦ hF h z.1)
  · intro z
    exact centeredLoss_zero loss z.2
  · intro z u v
    simpa [centeredLoss, sub_sub_sub_cancel_right] using hloss z.2 u v

end
