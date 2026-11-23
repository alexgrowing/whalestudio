import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AverageEmbeddingsFieldExtension
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
theorem _root_.GlobalTheory.T.average_embeddings_field_extension : ∀ (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K'] (f : (K →+* ℂ) → ℝ), (∑ σ : K' →+* ℂ, f (σ.comp (algebraMap K K'))) / (Module.finrank ℚ K' : ℝ) = (∑ σ : K →+* ℂ, f σ) / (Module.finrank ℚ K : ℝ) := by
  first | exact @GlobalTheory.mean_embeddings_comp_restrict | exact GlobalTheory.mean_embeddings_comp_restrict | (intros; apply GlobalTheory.mean_embeddings_comp_restrict <;> assumption)
