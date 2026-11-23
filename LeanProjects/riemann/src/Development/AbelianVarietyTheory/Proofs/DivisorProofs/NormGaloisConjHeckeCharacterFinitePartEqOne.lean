import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValCoordOfMemHatOUnits
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
open GlobalTheory.ToricTransport (coordIn)
open scoped nonZeroDivisors

noncomputable section

namespace GlobalTheory.CMVal.NormConj

theorem norm_sigma_ratio {E : Type} [Field E] [NumberField E] [IsCMField E] (σ : ℂ ≃+* ℂ) (φ : E →+* ℂ) (α : Eˣ) :
    ‖σ (φ (α : E) / starRingEnd ℂ (φ (α : E)))‖ = 1 := by
  rw [← IsCMField.complexEmbedding_complexConj, map_div₀]
  have e2 : σ (φ (IsCMField.complexConj E (α : E))) = starRingEnd ℂ (((σ : ℂ →+* ℂ).comp φ) (α : E)) := by
    rw [← IsCMField.complexEmbedding_complexConj]; rfl
  have e1 : σ (φ (α : E)) = ((σ : ℂ →+* ℂ).comp φ) (α : E) := rfl
  have h0 : ((σ : ℂ →+* ℂ).comp φ) (α : E) ≠ 0 := by simp
  rw [e2, e1, norm_div, Complex.norm_conj, div_self (norm_ne_zero_iff.2 h0)]

end GlobalTheory.CMVal.NormConj

open GlobalTheory.CMVal.NormConj in

theorem GlobalTheory.CMVal.norm_conj_finPart : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {I : Type} [Fintype I]
    (φ : I → E →+* ℂ) (hφ : IsCMType φ) (s : ℕ) (κ : I → ℕ) (c : Ideal (OF E)) (hc : c ≠ ⊥) (χ : HChar E)
    (hχ : HasInf χ φ (fun i => (κ i : ℤ) + s)) (hu : ∀ u ∈ hatOUnits c, finPart χ u = 1) (σ : ℂ ≃+* ℂ) (y : (Af E)ˣ),
    ‖σ (finPart χ y : ℂ)‖ = 1 := by
  intro E _ _ _ I _ φ _ s κ c hc χ hinf hχ σ y
  classical
  have hfin := GlobalTheory.CMVal.PicFin.finite_picO E c hc
  have hpos : 0 < Nat.card (PicO c) := Nat.card_pos
  have hmem : y ^ Nat.card (PicO c) ∈ (princ ⊔ hatOUnits c : Subgroup (Af E)ˣ) := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact pow_card_eq_one'
  obtain ⟨p, ⟨α, rfl⟩, u, hu, hpu⟩ := Subgroup.mem_sup.1 hmem
  set h := Nat.card (PicO c)
  have hf : ((finPart χ y : ℂ)) ^ h = ((χ.inf α : ℂˣ) : ℂ)⁻¹ := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, ← hpu, map_mul, hχ u hu, mul_one,
      eq_inv_of_mul_eq_one_left (finPart_mul_inf χ α), Units.val_inv_eq_inv_val]
  have hn : ‖σ (finPart χ y : ℂ)‖ ^ h = 1 := by
    rw [← norm_pow, ← map_pow, hf, (hasInfRatio_iff χ φ _).1 hinf α, map_inv₀, norm_inv, map_prod, norm_prod]
    simp only [map_zpow₀, norm_zpow, norm_sigma_ratio, one_zpow, Finset.prod_const_one, inv_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hpos.ne').1 hn
