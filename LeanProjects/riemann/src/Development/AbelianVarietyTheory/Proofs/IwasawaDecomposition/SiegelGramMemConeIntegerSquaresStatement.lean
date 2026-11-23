import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SiegelGramMemConeIntegerSquares
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSiegelZeroFront
open Matrix GlobalTheory.RedTh NumberField GlobalTheory.PolFan ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelGram_mem_cone_integer_squares : ∀ n : ℕ, ∃ S : Finset (Fin n → ℤ), ∀ (d : Fin n → ℝ) (u : Matrix (Fin n) (Fin n) ℝ), IsSiegel d u → ∃ c : (Fin n → ℤ) → ℝ, (∀ l, 0 ≤ c l) ∧ gram d u = ∑ l ∈ S, c l • vecMulVec (fun i => (l i : ℝ)) (fun i => (l i : ℝ)) := by
  first | exact @GlobalTheory.SiegelCone.gram_mem_cone | exact GlobalTheory.SiegelCone.gram_mem_cone | (intros; apply GlobalTheory.SiegelCone.gram_mem_cone <;> assumption)
