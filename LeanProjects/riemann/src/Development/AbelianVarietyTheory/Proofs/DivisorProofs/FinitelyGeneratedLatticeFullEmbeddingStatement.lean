import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitelyGeneratedLatticeFullEmbedding
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SecJets4
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ConjInvIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogHeightBoundFromInequalityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianLatticeBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiFibrationLieLatticeFullStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetSlopeDegreeInequalityStatement
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.PosSemidefOfForallCombination
import ReciprocityTheory.GeometryOfNumbers.MatrixArithmetic.WeakMatSt
open NumberField MeasureTheory ReciprocityTheory.GeometryOfNumbersTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LieHt
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finitely_generated_lattice_full_embedding : ∀ (K : Type) [Field K] [NumberField K] (m : ℕ) (W : Submodule (𝓞 K) (Fin m → K)), W.FG → ∃ α : (Fin (latRank K W) → K) →ₗ[K] (Fin m → K), Function.Injective α ∧ Full (W.comap (α.restrictScalars (𝓞 K))) ∧ (W.comap (α.restrictScalars (𝓞 K))).map (α.restrictScalars (𝓞 K)) = W := by
  first | exact @GlobalTheory.exists_injective_full_comap_map_eq | exact GlobalTheory.exists_injective_full_comap_map_eq | (intros; apply GlobalTheory.exists_injective_full_comap_map_eq <;> assumption)
