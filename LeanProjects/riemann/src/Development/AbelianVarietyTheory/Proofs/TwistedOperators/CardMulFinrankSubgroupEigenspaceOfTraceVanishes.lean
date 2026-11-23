import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FactTypePrime

noncomputable section

namespace GlobalTheory.DefFree

theorem isProj_eig_average {G M : Type} [Group G] [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ G M)
    (P : Subgroup G) [Fintype P] (χ : P →* ℂˣ) :
    LinearMap.IsProj (GlobalTheory.DefFree.eig ρ P fun g => ((χ g : ℂˣ) : ℂ))
      ((Fintype.card P : ℂ)⁻¹ • ∑ g : P, (((χ g)⁻¹ : ℂˣ) : ℂ) • (ρ g : M →ₗ[ℂ] M)) := by
  classical
  have hcard : (Fintype.card P : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have happ : ∀ x : M, ((Fintype.card P : ℂ)⁻¹ • ∑ g : P, (((χ g)⁻¹ : ℂˣ) : ℂ) • (ρ g : M →ₗ[ℂ] M)) x
      = (Fintype.card P : ℂ)⁻¹ • ∑ g : P, (((χ g)⁻¹ : ℂˣ) : ℂ) • ρ g x := by
    intro x
    simp only [LinearMap.smul_apply, LinearMap.sum_apply]
  refine ⟨fun x => ?_, fun x hx => ?_⟩
  ·
    rw [happ, mem_eig]
    intro h
    have hsum : ρ h (∑ g : P, (((χ g)⁻¹ : ℂˣ) : ℂ) • ρ g x)
        = ((χ h : ℂˣ) : ℂ) • ∑ g : P, (((χ g)⁻¹ : ℂˣ) : ℂ) • ρ g x := by
      rw [map_sum, Finset.smul_sum]
      refine Fintype.sum_equiv (Equiv.mulLeft h) _ _ fun g => ?_
      have hc : ((χ h : ℂˣ) : ℂ) * (((χ (h * g))⁻¹ : ℂˣ) : ℂ) = (((χ g)⁻¹ : ℂˣ) : ℂ) := by
        rw [← Units.val_mul, map_mul, mul_inv, mul_inv_cancel_left]
      show ρ h ((((χ g)⁻¹ : ℂˣ) : ℂ) • ρ g x)
        = ((χ h : ℂˣ) : ℂ) • ((((χ (h * g))⁻¹ : ℂˣ) : ℂ) • ρ ((h * g : P) : G) x)
      rw [smul_smul, hc, map_smul, Subgroup.coe_mul, map_mul, Module.End.mul_apply]
    show ρ h (_ • _) = ((χ h : ℂˣ) : ℂ) • (_ • _)
    rw [map_smul, hsum, smul_comm]
  ·
    have hx' : ∀ g : P, ρ g x = ((χ g : ℂˣ) : ℂ) • x := fun g => (mem_eig.mp hx) g
    have hterm : ∀ g : P, (((χ g)⁻¹ : ℂˣ) : ℂ) • ρ g x = x := fun g => by
      rw [hx' g, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
    rw [happ]
    simp only [hterm, Finset.sum_const, Finset.card_univ]
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hcard, one_smul]

theorem card_mul_finrank_eig (G M : Type) [Group G] [Finite G] [AddCommGroup M] [Module ℂ M]
    [FiniteDimensional ℂ M] (ρ : Representation ℂ G M) (P : Subgroup G) (χ : P →* ℂˣ)
    (h : ∀ g ∈ P, g ≠ 1 → LinearMap.trace ℂ M (ρ g) = 0) :
    Nat.card P * Module.finrank ℂ (GlobalTheory.DefFree.eig ρ P fun g => ((χ g : ℂˣ) : ℂ)) = Module.finrank ℂ M := by
  classical
  haveI : Fintype P := Fintype.ofFinite P
  have htr := (isProj_eig_average ρ P χ).trace
  rw [map_smul, map_sum, smul_eq_mul] at htr
  simp only [map_smul, smul_eq_mul] at htr

  rw [Finset.sum_eq_single (1 : P) (fun g _ hg => by
      rw [h g g.2 (fun h1 => hg (Subtype.ext h1)), mul_zero])
    (fun h1 => absurd (Finset.mem_univ _) h1)] at htr
  rw [map_one, inv_one, Units.val_one, one_mul, OneMemClass.coe_one, map_one,
    LinearMap.trace_one] at htr
  have hcard : (Fintype.card P : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [Nat.card_eq_fintype_card]
  have key : (Fintype.card P : ℂ) * (Module.finrank ℂ (GlobalTheory.DefFree.eig ρ P fun g => ((χ g : ℂˣ) : ℂ)) : ℂ)
      = (Module.finrank ℂ M : ℂ) := by
    rw [← htr, ← mul_assoc, mul_inv_cancel₀ hcard, one_mul]
  exact_mod_cast key

end GlobalTheory.DefFree

end
