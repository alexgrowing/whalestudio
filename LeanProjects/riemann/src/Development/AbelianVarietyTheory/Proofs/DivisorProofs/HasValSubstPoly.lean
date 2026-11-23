import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasPAdicPowerSeriesValueMapOfContinuousEvaluatioStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasPAdicPowerSeriesValueAddSmulMapStatement
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.QLog

theorem hasVal_subst_poly : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ (σ : Type) [Fintype σ] [DecidableEq σ] (z : σ → B), (∀ i, ∃ N : ℕ, (p : B) ∣ z i ^ N) → ∀ E : MvPowerSeries σ B →ₐ[B] B, IsEval p z E → ∀ (τ : Type) [Fintype τ] [DecidableEq τ] (u : τ → MvPowerSeries σ B), (∀ j, constantCoeff (u j) = 0) → ∀ g : MvPolynomial τ Q, HasVal p z (subst (up Q u) (g : MvPowerSeries τ Q)) (MvPolynomial.eval (fun j => algebraMap B Q (E (u j))) g) := by
  intro p _ B O Q _ _ _ _ θ hF σ _ _ z hz E hE τ _ _ u hu g
  have ha : HasSubst (up Q u) := hasSubst_of_constantCoeff_zero fun j => by
    simp [up, hu j]
  induction g using MvPolynomial.induction_on' with
  | monomial α c =>
    rw [MvPolynomial.coe_monomial, subst_monomial ha, MvPolynomial.eval_monomial]
    have hprod : α.prod (fun s n => (up Q u s) ^ n) = map (algebraMap B Q) (α.prod fun s n => (u s) ^ n) := by
      simp [up, Finsupp.prod, map_prod, map_pow]
    have hEp : E (α.prod fun s n => (u s) ^ n) = α.prod fun s n => (E (u s)) ^ n := by
      simp [Finsupp.prod, map_prod, map_pow]
    have hv := GlobalTheory.T.hasPAdicPowerSeriesValue_map_of_continuousEvaluation p B O Q θ hF σ z hz E hE (α.prod fun s n => (u s) ^ n)
    have hs := (GlobalTheory.T.hasPAdicPowerSeriesValue_add_smul_map p B O Q θ hF σ z _ 0 _ 0 hv).2.1 c
    rw [hprod]
    convert hs using 1
    · rw [MvPowerSeries.smul_eq_C_mul]; rfl
    · rw [hEp]; simp [Finsupp.prod, map_prod, map_pow]
  | add f g hf hg =>
    rw [MvPolynomial.coe_add, subst_add ha, map_add]
    exact (GlobalTheory.T.hasPAdicPowerSeriesValue_add_smul_map p B O Q θ hF σ z _ _ _ _ hf).1 hg

end GlobalTheory.QLog
