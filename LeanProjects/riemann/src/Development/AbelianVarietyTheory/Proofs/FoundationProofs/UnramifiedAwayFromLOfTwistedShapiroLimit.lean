import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ShCocOn
import Development.AbelianVarietyTheory.Definitions.Foundations.IsLocallyConstantCycMod
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ShiftedCocycleLimitIntegralStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.KA
open scoped Matrix

noncomputable section

namespace GlobalTheory.KA

variable {l : ℕ} [Fact l.Prime] {Ω : Type} [Field Ω] [Algebra ℚ Ω]

def untwist (W : R2 Ω l) (θ : G ℚ Ω →* (Qbar l)ˣ) : R2 Ω l where
  toFun s := Units.map (algebraMap (Qbar l) (Matrix (Fin 2) (Fin 2) (Qbar l))).toMonoidHom (θ s)⁻¹ * W s
  map_one' := by simp
  map_mul' s t := by
    apply Units.ext
    simp only [map_mul, mul_inv, Units.val_mul, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe,
      ← Algebra.smul_def, smul_mul_assoc, mul_smul_comm, smul_smul, Algebra.algebraMap_eq_smul_one, one_mul, mul_comm]

theorem mat_untwist (W : R2 Ω l) (θ : G ℚ Ω →* (Qbar l)ˣ) (s : G ℚ Ω) :
    mat (untwist W θ) s = (((θ s)⁻¹ : (Qbar l)ˣ) : Qbar l) • mat W s := by
  show algebraMap (Qbar l) (Matrix (Fin 2) (Fin 2) (Qbar l)) (((θ s)⁻¹ : (Qbar l)ˣ) : Qbar l) * mat W s = _
  rw [← Algebra.smul_def]

theorem continuous_untwist {W : R2 Ω l} {θ : G ℚ Ω →* (Qbar l)ˣ} (hW : Continuous W) (hθ : Continuous θ) :
    Continuous (untwist W θ) := by
  have h1 : Continuous fun s => mat (untwist W θ) s := by
    simp only [mat_untwist]
    exact (Units.continuous_coe_inv.comp hθ).smul (Units.continuous_val.comp hW)
  refine Units.continuous_iff.2 ⟨h1, ?_⟩
  have h2 : (fun s => (((untwist W θ s)⁻¹ : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l))) =
      fun s => (θ s : Qbar l) • (((W s)⁻¹ : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) := by
    funext s
    rw [← map_inv, ← map_inv]
    have := mat_untwist W θ s⁻¹
    rw [map_inv θ, inv_inv] at this
    exact this
  rw [h2]
  exact (Units.continuous_val.comp hθ).smul (Units.continuous_coe_inv.comp hW)

theorem unr_of_twisted_limit : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (W : R2 Ω l) (c : Coef l) (θ : G ℚ Ω →* (Qbar l)ˣ) (ρ : G ℚ Ω → Matrix (Fin 2) (Fin 2) (Qbar l)) (Y : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Fin 2 → Qbar l) (η : ∀ r : ℕ, (ZMod (l ^ r))ˣ → Qbar l) (y : G ℚ Ω → Fin 2 → Qbar l), Continuous W → Continuous θ → (∀ s i j, mat W s i j ∈ c.O) → (∀ s, mat W s = (θ s : Qbar l) • ρ s) → (∀ s i j, ρ s i j ∈ c.O) → (∀ r x i, Continuous fun s => Y r s x i) → (∀ r s x i, Y r s x i ∈ c.O) → (∀ r, ShCoc ρ (cycMod ℚ Ω l r)⁻¹ (Y r)) → (∀ r s, Y r s = push (Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom) (Y (r + 1)) s) → (∀ r x, η r x ∈ c.O) → (∀ r s x, ‖η r (x * cycMod ℚ Ω l r s) - η r x * (θ s : Qbar l)‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖) → y ∈ Z1 (Loc.colRep W) → (∀ r s i, ‖y s i - spec (η r) (Y r) s i‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖) → Unr W y := by
  intro l _ Ω _ _ _ W c θ ρ Y η y hW hθ _ hWρ hρ hYc hYi hSh hpush hη _ hy hlim q hq
  have hρ' : mat (untwist W θ) = ρ := by
    funext s
    rw [mat_untwist, hWρ, smul_smul, Units.inv_mul, one_smul]
  obtain ⟨B, hB, v, hv⟩ := GlobalTheory.T.shifted_cocycle_limit_integral l Ω (untwist W θ) c Y η y (continuous_untwist hW hθ)
    (by rw [hρ']; exact hρ) hYc hYi (by rw [hρ']; exact hSh) hpush hη hlim q hq
  refine ⟨B, hB, ?_⟩
  by_cases h : ∀ s ∈ Ine (F := ℚ) B, θ s = 1
  · refine ⟨v, fun s hs => ?_⟩
    rw [hv s hs, mat_untwist, h s hs]
    simp
  · push Not at h
    obtain ⟨s, hs, hne⟩ := h
    refine ⟨0, fun t ht => ?_⟩
    have hc : y (s * t) = y s + mat W s *ᵥ y t := by
      rw [hy.2 s t]
      rfl
    have hm : mat (untwist W θ) (s * t) = mat (untwist W θ) s * mat (untwist W θ) t := by
      simp only [mat, map_mul, Units.val_mul]
    have hc' : y (s * t) = y s + mat (untwist W θ) s *ᵥ y t := by
      rw [hv _ (mul_mem hs ht), hv s hs, hv t ht, hm, Matrix.mulVec_sub, Matrix.mulVec_mulVec]
      abel
    rw [hc, mat_untwist, Matrix.smul_mulVec, add_right_inj] at hc'
    have h0 : mat W s *ᵥ y t = 0 := by
      have h1 : (1 - (((θ s)⁻¹ : (Qbar l)ˣ) : Qbar l)) • (mat W s *ᵥ y t) = 0 := by
        rw [sub_smul, one_smul, ← hc', sub_self]
      refine (smul_eq_zero.1 h1).resolve_left fun h2 => hne ?_
      have h3 : (θ s)⁻¹ = 1 := Units.ext (sub_eq_zero.1 h2).symm
      exact inv_eq_one.1 h3
    have h4 : y t = 0 := by
      have h5 : mat W s⁻¹ *ᵥ (mat W s *ᵥ y t) = y t := by
        rw [Matrix.mulVec_mulVec]
        have : mat W s⁻¹ * mat W s = 1 := by
          simp only [mat]
          rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
        rw [this, Matrix.one_mulVec]
      rw [← h5, h0, Matrix.mulVec_zero]
    rw [h4]
    simp

end GlobalTheory.KA

end
