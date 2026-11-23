import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithHilbertSamuelLowerBoundCountRankAmple
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithHilbertSamuel_lowerBound_count_rank_ample : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → ∀ (e : ℕ) (x : Fin (D + 1) → X.functionField), Gens P D e x → ∀ a b : ℤ, ∃ (c : ℕ) (C : ℝ), 0 < C ∧ ∀ q : ℕ, (∃ v : Fin (Module.finrank (ratF x) X.functionField * (q + D).choose D) → X.functionField, (∀ i, v i ∈ P.H (e * (q + c : ℕ) + a) b) ∧ LinearIndependent ℤ v) ∧ ∀ R : ℝ, 0 ≤ R → (∀ l (σ : k →+* ℂ) (y : CxPts p σ), P.nu e 0 σ y (x l) ≤ 1) → (((2 * ⌊R⌋₊ + 1) ^ (Module.finrank (ratF x) X.functionField * (q + D).choose D) : ℕ) : ℕ∞) ≤ (P.Bl (e * (q + c : ℕ) + a) b (C * (q + D).choose D * R)).encard := by
  first | exact @GlobalTheory.HSAmp.FLower.count_rank_lower | exact GlobalTheory.HSAmp.FLower.count_rank_lower | (intros; apply GlobalTheory.HSAmp.FLower.count_rank_lower <;> assumption)
