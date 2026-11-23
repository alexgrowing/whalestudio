import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.StandardFiveNontrivial
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CharacterIdempotents.Scalar
import Formalism.LocalToGlobal.Divisibility.ProjLemmas

noncomputable section
open Polynomial Classical GlobalTheory.BadShare
namespace GlobalTheory.BadShare.ZCalc

variable {G : Type} [Group G] [Fintype G]

theorem character_inv (V : FDRep ℂ G) (t : G) : V.character t⁻¹ = (starRingEnd ℂ) (V.character t) := by
  let b := Module.finBasis ℂ V
  have htr : ∀ s, V.character s = (LinearMap.toMatrix b b (V.ρ s)).trace := fun s =>
    LinearMap.trace_eq_matrix_trace ℂ b _
  rw [htr, htr]
  refine Formalism.L2.DIV.trace_inv_of_pow_eq_one _ _ (N := Fintype.card G) Fintype.card_ne_zero ?_ ?_
  · rw [LinearMap.toMatrix_pow, ← map_pow, pow_card_eq_one, map_one, LinearMap.toMatrix_one]
  · rw [← LinearMap.toMatrix_mul, ← map_mul, inv_mul_cancel, map_one, LinearMap.toMatrix_one]

theorem op_zc (V W : FDRep ℂ G) :
    op W.ρ (zc V.character) = PI.CharIdem.act W (PI.CharIdem.charIdem V) := by
  rw [PI.CharIdemW.act_charIdem]
  simp only [op, zc, FDRep.char_one]

theorem conv_zc_of_scalar (χ : G → ℂ) (W : FDRep ℂ G) (c : ℂ) (h : op W.ρ (zc χ) = c • 1) (x : G) :
    conv (zc χ) (zc W.character) x = c * zc W.character x := by
  have h1 : ∑ y, zc χ y * W.character (y * x⁻¹) = c * W.character x⁻¹ := by
    have h2 : LinearMap.trace ℂ W (op W.ρ (zc χ) * W.ρ x⁻¹) = c * W.character x⁻¹ := by
      rw [h, smul_mul_assoc, one_mul, map_smul, smul_eq_mul]; rfl
    rw [← h2, op, Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [smul_mul_assoc, map_smul, smul_eq_mul, ← map_mul]; rfl
  have h3 : ∀ y, zc χ y * zc W.character (y⁻¹ * x) =
      W.character 1 / (Fintype.card G : ℂ) * (zc χ y * W.character (y * x⁻¹)) := by
    intro y
    have : W.character (y⁻¹ * x)⁻¹ = W.character (y * x⁻¹) := by
      rw [mul_inv_rev, inv_inv, FDRep.char_mul_comm]
    rw [show zc W.character (y⁻¹ * x) = W.character 1 / (Fintype.card G : ℂ) * W.character (y⁻¹ * x)⁻¹ from rfl, this]
    ring
  rw [conv, Finset.sum_congr rfl fun y _ => h3 y, ← Finset.mul_sum, h1,
    show zc W.character x = W.character 1 / (Fintype.card G : ℂ) * W.character x⁻¹ from rfl]
  ring

theorem op_conv_eq {M : Type} [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ G M) (a b : G → ℂ) :
    op ρ (conv a b) = op ρ a * op ρ b := by
  simp only [op, conv, Finset.sum_smul, Finset.sum_mul_sum, smul_mul_smul_comm, ← map_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  refine (Fintype.sum_equiv (Equiv.mulLeft y) _ _ fun x => ?_).symm
  simp

theorem rk_eq_trace {M : Type} [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] (ρ : Representation ℂ G M)
    (e : G → ℂ) (he : conv e e = e) : (rk ρ e : ℂ) = ∑ γ, e γ * LinearMap.trace ℂ M (ρ γ) := by
  have hi : IsIdempotentElem (op ρ e) := by
    rw [IsIdempotentElem, ← op_conv_eq, he]
  have hp := (LinearMap.IsIdempotentElem.isProj_range _ hi).trace
  rw [rk, ← hp, op, map_sum]
  simp only [map_smul, smul_eq_mul]

theorem zc_calc : ∀ (G : Type) [Group G] [Fintype G], ∀ (V : FDRep ℂ G) [CategoryTheory.Simple V], IsProj (zc V.character) ∧ (∀ a : G → ℂ, conv (zc V.character) a = conv a (zc V.character)) ∧ (∀ (W : FDRep ℂ G) [CategoryTheory.Simple W], V.character ≠ W.character → conv (zc V.character) (zc W.character) = 0) ∧ ∀ e : G → ℂ, conv e e = e → conv (zc V.character) e 1 = (Module.finrank ℂ V : ℂ) * (rk V.ρ e : ℂ) / (Fintype.card G : ℂ) := by
  intro G _ _ V hV
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · funext x
    have h := (PI.CharIdemW.scalar G V V hV hV).1 ⟨CategoryTheory.Iso.refl V⟩
    rw [conv_zc_of_scalar _ V 1 (by rw [op_zc, h, one_smul]), one_mul]
  · intro x
    simp only [zc, map_mul, map_div₀, FDRep.char_one, map_natCast]
    rw [character_inv V x⁻¹]
  · intro a
    funext x
    simp only [conv]
    refine Fintype.sum_equiv ((Equiv.inv G).trans (Equiv.mulRight x)) _ _ fun y => ?_
    simp only [Equiv.trans_apply, Equiv.inv_apply, Equiv.coe_mulRight, zc]
    have : V.character ((y⁻¹ * x)⁻¹ * x)⁻¹ = V.character y⁻¹ := by
      rw [← FDRep.char_conj V y⁻¹ x⁻¹]
      congr 1
      group
    rw [this, mul_comm]
  · intro W hW hne
    funext x
    have h := (PI.CharIdemW.scalar G V W hV hW).2 ⟨fun i => hne (FDRep.char_iso i)⟩
    rw [conv_zc_of_scalar _ W 0 (by rw [op_zc, h, zero_smul]), zero_mul]
    rfl
  · intro e he
    rw [rk_eq_trace _ e he, conv, Finset.mul_sum, Finset.sum_div]
    refine Fintype.sum_equiv (Equiv.inv G) _ _ fun y => ?_
    simp only [Equiv.inv_apply, zc, mul_one, FDRep.char_one]
    rw [show LinearMap.trace ℂ V (V.ρ y⁻¹) = V.character y⁻¹ from rfl]
    ring

end GlobalTheory.BadShare.ZCalc
