import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetSlopeDegreeInequality
import Development.AbelianVarietyTheory.Definitions.Divisors.SecJets4
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
open NumberField MeasureTheory ReciprocityTheory.GeometryOfNumbersTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LieHt
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jet_slope_degree_inequality : ∀ (K : Type) [Field K] [NumberField K] (m : ℕ) (h : HermFam K (Fin m → K)) (L : Submodule (𝓞 K) (Fin m → K)) (x : Fin m → K) (n : ℕ) (ν : ℝ) (β : ℕ → (K →+* ℂ) → ℝ), Full L → x ≠ 0 → (∀ i σ, i ≤ n → 0 < β i σ) → JetSys h L x n ν β → ((n : ℝ) + 1) * ν ≤ ∑ i ∈ Finset.range (n + 1), (-(i : ℝ) * deg h (lineLat L x) + meanLog K (β i)) := by
  first | exact @GlobalTheory.SlopeFilt.slope_filt | exact GlobalTheory.SlopeFilt.slope_filt | (intros; apply GlobalTheory.SlopeFilt.slope_filt <;> assumption)
