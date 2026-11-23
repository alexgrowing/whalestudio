import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantFibreRankStalkRank
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LiftSemiTmul
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.PerfVB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constant_fibre_rank_stalk_rank : ∀ (R K : Type) [CommRing R] [AddCommGroup K] [Module R K] [Module.Finite R K] [Module.Projective R K] (g : ℕ), (∀ (k : Type) [Field k] [Algebra R k], Module.finrank k (k ⊗[R] K) = g) → ∀ p : PrimeSpectrum R, Module.rankAtStalk K p = g := by
  first | exact @GlobalTheory.CompanionTheory.PerfVB.rankAtStalk_eq_of_finrank_fibres | exact GlobalTheory.CompanionTheory.PerfVB.rankAtStalk_eq_of_finrank_fibres | (intros; apply GlobalTheory.CompanionTheory.PerfVB.rankAtStalk_eq_of_finrank_fibres <;> assumption)
