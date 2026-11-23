import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TailSubstPAdicallySmallOfIntegralDifferentialStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasValSubstPolyStatement

set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.QLog

theorem hasVal_subst : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ (σ : Type) [Fintype σ] [DecidableEq σ] (z : σ → B), (∀ i, ∃ N : ℕ, (p : B) ∣ z i ^ N) → ∀ E : MvPowerSeries σ B →ₐ[B] B, IsEval p z E → ∀ (τ : Type) [Fintype τ] [DecidableEq τ] (u : τ → MvPowerSeries σ B) (f : MvPowerSeries τ Q) (q : Q), (∀ j, constantCoeff (u j) = 0) → DIn (⊤ : Ideal B) f → HasVal p (fun j => E (u j)) f q → HasVal p z (subst (up Q u) f) q := by
  intro p _ B O Q _ _ _ _ θ hF σ _ _ z hz E hE τ _ _ u f q hu hf hq
  intro m
  obtain ⟨M0, hM0⟩ := GlobalTheory.T.tail_subst_pAdically_small_of_integral_differential p B O Q θ hF σ z hz τ u f hu hf m
  obtain ⟨M1, hM1⟩ := hq m
  obtain ⟨g, hg⟩ : ∃ g : MvPolynomial τ Q, g = trunc' Q (Finsupp.equivFunOnFinite.symm fun _ => max M0 M1) f := ⟨_, rfl⟩
  obtain ⟨N2, hN2⟩ := GlobalTheory.T.hasVal_subst_polynomial_eval p B O Q θ hF σ z hz E hE τ u hu g m
  refine ⟨N2, fun N' hN' => ?_⟩
  obtain ⟨b1, hb1⟩ := hM1 (max M0 M1) (le_max_right _ _)
  obtain ⟨b2, hb2⟩ := hN2 N' hN'
  obtain ⟨b3, hb3⟩ := hM0 (max M0 M1) (le_max_left _ _) (Finsupp.equivFunOnFinite.symm fun _ => N')
  rw [← hg] at hb1 hb3
  have hs : HasSubst (up Q u) := hasSubst_of_constantCoeff_zero fun j => by
    simp [up, hu j]
  have hsplit : subst (up Q u) f = subst (up Q u) (g : MvPowerSeries τ Q) + subst (up Q u) (f - (g : MvPowerSeries τ Q)) := by
    rw [← subst_add hs]; congr 1; ring
  refine ⟨b1 + b2 - b3, ?_⟩
  rw [hsplit, map_add, map_add]
  simp only [map_mul, map_sub, map_add, map_pow, map_natCast] at hb1 hb2 hb3 ⊢
  linear_combination hb1 + hb2 - hb3

end GlobalTheory.QLog
