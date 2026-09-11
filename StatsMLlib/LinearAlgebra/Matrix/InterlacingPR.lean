/-
  Copyright (c) 2026 Yakov Kuzmin. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Yakov Kuzmin
-/
import StatsMLlib.LinearAlgebra.Matrix.CourantFischer

/-!
# Courant–Fischer monotonicity under Rayleigh-preserving embeddings

Generic monotonicity of the Courant–Fischer max-min / min-max quantities under
an injective linear embedding that preserves the Rayleigh quotient. This is the
reusable core behind Cauchy eigenvalue interlacing for nested Hermitian
principal blocks.

Contents:
* boundedness of the restricted Rayleigh families (`bddAbove_cfMaxMin_family`,
  `bddBelow_cfMinMax_family`);
* transport of the restricted Rayleigh maximum along a Rayleigh-preserving
  embedding (`maxRayleighQuotientOn_map_eq`);
* monotonicity of the Courant–Fischer quantities under such embeddings
  (`cfMaxMin_mono_of_isometry`, `cfMinMax_mono_of_isometry`) — the lower and
  upper halves of Cauchy interlacing respectively.
-/

open Module Submodule LinearMap

noncomputable section

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E_N E_M : Type*} [NormedAddCommGroup E_N] [InnerProductSpace 𝕜 E_N]
  [NormedAddCommGroup E_M] [InnerProductSpace 𝕜 E_M]
  [FiniteDimensional 𝕜 E_N] [FiniteDimensional 𝕜 E_M]
variable {T_N : E_N →ₗ[𝕜] E_N} {T_M : E_M →ₗ[𝕜] E_M}
variable {f : E_N →ₗ[𝕜] E_M}

/-- A submodule whose finite rank equals a positive `k` is nontrivial. -/
private theorem nontrivial_of_finrank_eq {E : Type*} [AddCommGroup E] [Module 𝕜 E]
    {U : Submodule 𝕜 E} {k : ℕ} (hU : finrank 𝕜 U = k) (hk : 0 < k) : Nontrivial U :=
  Module.nontrivial_of_finrank_pos (by rw [hU]; exact hk)

/-! ### Boundedness of the restricted Rayleigh families -/

/-- The family of restricted Rayleigh minima over `k`-dimensional subspaces of
`E_M` is bounded above, by the operator norm `‖T_M‖`. -/
theorem bddAbove_cfMaxMin_family (k : ℕ) (hk : 0 < k) :
    BddAbove (Set.range fun U : { U : Submodule 𝕜 E_M // finrank 𝕜 U = k } =>
      minRayleighQuotientOn T_M U) := by
  refine ⟨‖T_M.toContinuousLinearMap‖, fun y hy => ?_⟩
  rcases hy with ⟨U, rfl⟩
  have := nontrivial_of_finrank_eq U.property hk
  obtain ⟨x, hx0U⟩ := exists_ne (0 : (U : Submodule 𝕜 E_M))
  have hx0 : (x : E_M) ≠ 0 := fun hz => hx0U (Subtype.ext hz)
  calc minRayleighQuotientOn T_M U ≤ rayleighQuotient T_M (x : E_M) :=
        minRayleighQuotientOn_le_of_mem T_M x.property hx0
    _ = T_M.toContinuousLinearMap.rayleighQuotient (x : E_M) :=
        (rayleighQuotient_toContinuousLinearMap T_M x).symm
    _ ≤ ‖T_M.toContinuousLinearMap‖ :=
        le_trans (le_abs_self _) (T_M.toContinuousLinearMap.rayleighQuotient_le_norm x)

/-- The family of restricted Rayleigh maxima over `k`-dimensional subspaces of
`E_M` is bounded below, by `-‖T_M‖`. -/
theorem bddBelow_cfMinMax_family (k : ℕ) (hk : 0 < k) :
    BddBelow (Set.range fun U : { U : Submodule 𝕜 E_M // finrank 𝕜 U = k } =>
      maxRayleighQuotientOn T_M U) := by
  refine ⟨-‖T_M.toContinuousLinearMap‖, fun y hy => ?_⟩
  rcases hy with ⟨U, rfl⟩
  have := nontrivial_of_finrank_eq U.property hk
  obtain ⟨x, hx0U⟩ := exists_ne (0 : (U : Submodule 𝕜 E_M))
  have hx0 : (x : E_M) ≠ 0 := fun hz => hx0U (Subtype.ext hz)
  calc -‖T_M.toContinuousLinearMap‖ ≤ rayleighQuotient T_M (x : E_M) := by
        rw [rayleighQuotient_toContinuousLinearMap T_M x]
        exact neg_le.mp (le_trans (neg_le_abs _)
          (T_M.toContinuousLinearMap.rayleighQuotient_le_norm x))
    _ ≤ maxRayleighQuotientOn T_M U := le_maxRayleighQuotientOn_of_mem T_M x.property hx0

/-! ### Transport along Rayleigh-preserving embeddings -/

/-- The restricted Rayleigh maximum is preserved on the image of a subspace of
positive dimension under an injective embedding that preserves the Rayleigh
quotient. This is the transport step for Cauchy interlacing of nested principal
blocks: the supremum over `map f U` coincides with the one over `U`. -/
theorem maxRayleighQuotientOn_map_eq (hf : Function.Injective f)
    (hRQ : ∀ x, x ≠ 0 → rayleighQuotient T_M (f x) = rayleighQuotient T_N x)
    (U : Submodule 𝕜 E_N) (hUpos : 0 < finrank 𝕜 U) :
    maxRayleighQuotientOn T_M (Submodule.map f U) = maxRayleighQuotientOn T_N U := by
  have := nontrivial_of_finrank_eq (k := finrank 𝕜 U) rfl hUpos
  have : Nonempty { x : U // (x : E_N) ≠ 0 } := by
    obtain ⟨w, hw⟩ := exists_ne (0 : U); exact ⟨⟨w, fun hz => hw (Subtype.ext hz)⟩⟩
  have : Nonempty { y : Submodule.map f U // (y : E_M) ≠ 0 } := by
    obtain ⟨w, hw⟩ := exists_ne (0 : U)
    have hwE : (w : E_N) ≠ 0 := fun hz => hw (Subtype.ext hz)
    refine ⟨⟨⟨f w, mem_map_of_mem w.property⟩,
      fun hz => hwE (hf (hz.trans (map_zero f).symm))⟩⟩
  apply le_antisymm
  · refine ciSup_le (fun y => ?_)
    rcases mem_map.mp y.val.property with ⟨x, hxU, hfx⟩
    have hx0 : x ≠ 0 := by intro hz; rw [hz, map_zero] at hfx; exact y.property hfx.symm
    calc rayleighQuotient T_M (y.val : E_M) = rayleighQuotient T_M (f x) := by rw [hfx]
      _ = rayleighQuotient T_N x := hRQ x hx0
      _ ≤ maxRayleighQuotientOn T_N U := le_maxRayleighQuotientOn_of_mem T_N hxU hx0
  · refine ciSup_le (fun x => ?_)
    have hx0 : (x : E_N) ≠ 0 := x.property
    have hfx0 : f (x : E_N) ≠ 0 := by
      intro hz; exact x.property (hf (by rw [map_zero]; exact hz))
    calc rayleighQuotient T_N (x : E_N) = rayleighQuotient T_M (f x) := (hRQ x hx0).symm
      _ ≤ maxRayleighQuotientOn T_M (Submodule.map f U) :=
          le_maxRayleighQuotientOn_of_mem T_M (mem_map_of_mem x.val.property) hfx0

/-! ### Monotonicity of the Courant–Fischer quantities (interlacing core) -/

/-- Max-min monotonicity under a Rayleigh-preserving embedding (the lower half
of Cauchy interlacing): transporting each `k`-dimensional subspace of `E_N`
along `f` and applying the Courant–Fischer characterisation (`le_ciSup`) yields
`courantFischerMaxMin T_N k ≤ courantFischerMaxMin T_M k`. -/
theorem cfMaxMin_mono_of_isometry (hf : Function.Injective f)
    (hRQ : ∀ x, x ≠ 0 → rayleighQuotient T_M (f x) = rayleighQuotient T_N x)
    (k : ℕ) (hk : 0 < k) (hne : Nonempty { U : Submodule 𝕜 E_N // finrank 𝕜 U = k }) :
    courantFischerMaxMin T_N k ≤ courantFischerMaxMin T_M k := by
  refine ciSup_le (fun U => ?_)
  let V := Submodule.map f U.val
  have hVdim : finrank 𝕜 V = k := by
    rw [← (equivMapOfInjective f hf U.val).finrank_eq, U.property]
  have := nontrivial_of_finrank_eq hVdim hk
  have : Nonempty { y : V // (y : E_M) ≠ 0 } := by
    obtain ⟨w, hw⟩ := exists_ne (0 : V); exact ⟨⟨w, fun hz => hw (Subtype.ext hz)⟩⟩
  calc minRayleighQuotientOn T_N U.val ≤ minRayleighQuotientOn T_M V := by
        refine le_ciInf (fun y => ?_)
        rcases mem_map.mp y.val.property with ⟨x, hxU, hfx⟩
        have hx0 : x ≠ 0 := by intro hz; rw [hz, map_zero] at hfx; exact y.property hfx.symm
        calc minRayleighQuotientOn T_N U.val ≤ rayleighQuotient T_N x :=
              minRayleighQuotientOn_le_of_mem T_N hxU hx0
          _ = rayleighQuotient T_M (f x) := (hRQ x hx0).symm
          _ = rayleighQuotient T_M (y.val : E_M) := by rw [hfx]
      _ ≤ courantFischerMaxMin T_M k := le_ciSup (bddAbove_cfMaxMin_family k hk) ⟨V, hVdim⟩

/-- Min-max monotonicity under a Rayleigh-preserving embedding (the upper half
of Cauchy interlacing): follows from `maxRayleighQuotientOn_map_eq` and the
Courant–Fischer characterisation `ciInf_le` of the min-max quantity. -/
theorem cfMinMax_mono_of_isometry (hf : Function.Injective f)
    (hRQ : ∀ x, x ≠ 0 → rayleighQuotient T_M (f x) = rayleighQuotient T_N x)
    (k : ℕ) (hk : 0 < k) (hne : Nonempty { U : Submodule 𝕜 E_N // finrank 𝕜 U = k }) :
    courantFischerMinMax T_M k ≤ courantFischerMinMax T_N k := by
  refine le_ciInf (fun U => ?_)
  let V := Submodule.map f U.val
  have hVdim : finrank 𝕜 V = k := by
    rw [← (equivMapOfInjective f hf U.val).finrank_eq, U.property]
  calc courantFischerMinMax T_M k ≤ maxRayleighQuotientOn T_M V :=
        ciInf_le (bddBelow_cfMinMax_family k hk) ⟨V, hVdim⟩
    _ = maxRayleighQuotientOn T_N U.val :=
        maxRayleighQuotientOn_map_eq hf hRQ U.val (by rw [U.property]; exact hk)

end
