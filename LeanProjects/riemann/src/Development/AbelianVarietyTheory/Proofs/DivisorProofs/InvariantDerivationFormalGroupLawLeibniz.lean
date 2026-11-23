import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvDer
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LawDer

theorem atZero_subst_of_unit (R : Type) [CommRing R] (d : ℕ)
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (hc : ∀ i, constantCoeff (μ i) = 0)
    (hu : op μ (fun i => (X i : MvPowerSeries (Fin d) R)) (fun _ => 0) = fun i => X i)
    (F : MvPowerSeries (Fin d) R) : atZero (subst μ F) = F := by
  have hμ : HasSubst μ := hasSubst_of_constantCoeff_zero hc
  have hz : HasSubst (Sum.elim (fun i : Fin d => (X i : MvPowerSeries (Fin d) R)) fun _ : Fin d => (0 : MvPowerSeries (Fin d) R)) :=
    hasSubst_of_constantCoeff_zero (by intro s; cases s <;> simp)
  unfold atZero
  rw [subst_comp_subst_apply hμ hz]
  have : (fun i => subst (Sum.elim (fun i : Fin d => (X i : MvPowerSeries (Fin d) R)) fun _ : Fin d => (0 : MvPowerSeries (Fin d) R)) (μ i))
      = fun i => X i := hu
  rw [this, subst_self]
  rfl

theorem invDer_mul : ∀ (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), (∀ i, constantCoeff (μ i) = 0) → op μ (fun i => (X i : MvPowerSeries (Fin d) R)) (fun _ => 0) = (fun i => X i) → ∀ (u : Fin d → R) (F G : MvPowerSeries (Fin d) R), invDer μ u (F * G) = invDer μ u F * G + F * invDer μ u G := by
  intro R _ d μ hc hu u F G
  have hμ : HasSubst μ := hasSubst_of_constantCoeff_zero hc
  have hz : HasSubst (Sum.elim (fun i : Fin d => (X i : MvPowerSeries (Fin d) R)) fun _ : Fin d => (0 : MvPowerSeries (Fin d) R)) :=
    hasSubst_of_constantCoeff_zero (by intro s; cases s <;> simp)
  have hmul : ∀ H K : MvPowerSeries (Fin d ⊕ Fin d) R, atZero (H * K) = atZero H * atZero K := by
    intro H K; unfold atZero; exact subst_mul hz H K
  have h0 := atZero_subst_of_unit R d μ hc hu
  have key : ∀ i, atZero (pderiv R (Sum.inr i) (subst μ (F * G))) =
      atZero (pderiv R (Sum.inr i) (subst μ F)) * G + F * atZero (pderiv R (Sum.inr i) (subst μ G)) := by
    intro i
    rw [subst_mul hμ, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    unfold atZero
    rw [subst_add hz, subst_mul hz, subst_mul hz]
    have hF := h0 F; have hG := h0 G; unfold atZero at hF hG
    rw [hF, hG]; ring
  unfold invDer
  simp_rw [key, smul_add, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm]

end GlobalTheory.LawDer
