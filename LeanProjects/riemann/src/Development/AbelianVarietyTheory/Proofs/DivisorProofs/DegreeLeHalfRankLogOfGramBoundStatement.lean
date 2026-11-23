import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeLeHalfRankLogOfGramBound
import Development.AbelianVarietyTheory.Definitions.Divisors.SecJets4
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.PosSemidefOfForallCombination
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.InhabSt
open NumberField MeasureTheory ReciprocityTheory.GeometryOfNumbersTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LieHt
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degree_le_half_rank_log_of_gram_bound : ∀ (K : Type) [Field K] [NumberField K] (m r : ℕ) (h : HermFam K (Fin m → K)) (ε : Fin r → Fin m → K) (C : ℝ), 0 < C → LinearIndependent K ε → (∀ σ : K →+* ℂ, ((C : ℂ) • h.gram σ ε - 1).PosSemidef) → ∀ W : Submodule (𝓞 K) (Fin m → K), W ≤ Submodule.span (𝓞 K) (Set.range ε) → deg h W ≤ (latRank K W : ℝ) / 2 * Real.log C := by
  first | exact @GlobalTheory.TorusSlope.deg_le_half_log | exact GlobalTheory.TorusSlope.deg_le_half_log | (intros; apply GlobalTheory.TorusSlope.deg_le_half_log <;> assumption)
