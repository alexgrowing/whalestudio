import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SelmerOrderCounts.TwoLe
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90

open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.ZK UpperTheory.V.ZK.Ct

theorem UpperTheory.V.ZK.Ct.h90 :
    ∀ (L F : Type) [Field L] [NumberField L] [Field F] [NumberField F] [Algebra L F] (γ : F ≃ₐ[L] F) (l : ℕ), IsGalois L F → (∀ σ : F ≃ₐ[L] F, σ ∈ Subgroup.zpowers γ) → ∀ x y : Fˣ, actU γ x = x * y ^ l → Algebra.norm L (y : F) = 1 → ∃ (x₀ : Lˣ) (z : Fˣ), x = Units.map (algebraMap L F : L →* F) x₀ * z ^ l := by
  intro L F _ _ _ _ _ γ l hG hγ x y hx hy
  haveI : FiniteDimensional L F := Module.Finite.of_restrictScalars_finite ℚ L F
  haveI : IsCyclic (F ≃ₐ[L] F) := ⟨⟨γ, hγ⟩⟩
  obtain ⟨w, hw⟩ := groupCohomology.exists_div_of_norm_eq_one hγ hy
  have hx' : γ (x : F) = (x : F) * (y : F) ^ l := by
    have := congrArg (fun u : Fˣ => (u : F)) hx
    simpa [actU] using this
  have hw0 : (w : F) ≠ 0 := w.ne_zero
  have hgw0 : γ (w : F) ≠ 0 := by simp
  have hfix : γ ((x : F) * (w : F) ^ l) = (x : F) * (w : F) ^ l := by
    rw [map_mul, map_pow, hx', ← hw, mul_assoc, ← mul_pow, div_mul_cancel₀ _ hgw0]
  have hall : ∀ σ : F ≃ₐ[L] F, σ ((x : F) * (w : F) ^ l) = (x : F) * (w : F) ^ l := by
    intro σ
    have hle : Subgroup.zpowers γ ≤ MulAction.stabilizer (F ≃ₐ[L] F) ((x : F) * (w : F) ^ l) := by
      rw [Subgroup.zpowers_le]
      exact hfix
    exact hle (hγ σ)
  obtain ⟨a, ha⟩ := (IsGalois.mem_range_algebraMap_iff_fixed _).2 hall
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at ha
    exact (mul_ne_zero x.ne_zero (pow_ne_zero l hw0)) ha.symm
  refine ⟨Units.mk0 a ha0, w⁻¹, ?_⟩
  ext
  simp only [Units.val_mul, Units.coe_map, MonoidHom.coe_coe, Units.val_mk0, ha,
    Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val]
  rw [mul_assoc, ← mul_pow, mul_inv_cancel₀ hw0, one_pow, mul_one]
