import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeRankAdditiveExact
import Development.AbelianVarietyTheory.Definitions.Divisors.SecJets4
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.PosSemidefOfForallCombination
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.InhabSt
open NumberField MeasureTheory ReciprocityTheory.GeometryOfNumbersTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LieHt
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_rank_additive_exact : ∀ (K : Type) [Field K] [NumberField K] (m m' : ℕ) (q : (Fin m → K) →ₗ[K] (Fin m' → K)) (W : Submodule (𝓞 K) (Fin m → K)), latRank K W = latRank K (W ⊓ (LinearMap.ker q).restrictScalars (𝓞 K)) + latRank K (W.map (q.restrictScalars (𝓞 K))) := by
  first | exact @GlobalTheory.latRank_eq_latRank_inf_ker_add_latRank_map | exact GlobalTheory.latRank_eq_latRank_inf_ker_add_latRank_map | (intros; apply GlobalTheory.latRank_eq_latRank_inf_ker_add_latRank_map <;> assumption)
