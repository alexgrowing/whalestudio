import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsEqSumAevalBoundedIntCoeffAmple
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sections_eq_sum_aeval_boundedIntCoeff_ample : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → ∀ (e : ℕ) (x : Fin (D + 1) → X.functionField), Gens P D e x → ∀ a b : ℤ, ∃ (c : ℕ) (w : Fin (Module.finrank (ratF x) X.functionField) → X.functionField) (C : ℝ), 0 < C ∧ ∀ (q : ℕ), ∀ f ∈ P.H (e * q + a) b, ∃ T : Fin (Module.finrank (ratF x) X.functionField) → MvPolynomial (Fin (D + 1)) ℤ, (∀ i, (T i).IsHomogeneous (q + c)) ∧ f = ∑ i, MvPolynomial.aeval x (T i) * w i ∧ ∀ R κ : ℝ, 0 < κ → (∀ (σ : k →+* ℂ) (y : CxPts p σ), ∃ l, κ ≤ P.nu e 0 σ y (x l)) → (∀ (σ : k →+* ℂ) (y : CxPts p σ), P.nu (e * q + a) b σ y f ≤ R) → ∀ i α, |((MvPolynomial.coeff α (T i) : ℤ) : ℝ)| ≤ C * R / κ ^ (q + c) := by
  first | exact @GlobalTheory.HSRep.sections_eq_sum_aeval_bounded | exact GlobalTheory.HSRep.sections_eq_sum_aeval_bounded | (intros; apply GlobalTheory.HSRep.sections_eq_sum_aeval_bounded <;> assumption)
