import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeIsometricEmbeddingEq
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
theorem _root_.GlobalTheory.T.degree_isometric_embedding_eq : ∀ (K : Type) [Field K] [NumberField K] (n m : ℕ) (hW : HermFam K (Fin n → K)) (h : HermFam K (Fin m → K)) (α : (Fin n → K) →ₗ[K] (Fin m → K)), Function.Injective α → (∀ σ y z, hW.form σ y z = h.form σ (α y) (α z)) → ∀ E : Submodule (𝓞 K) (Fin n → K), E.FG → deg hW E = deg h (E.map (α.restrictScalars (𝓞 K))) := by
  first | exact @GlobalTheory.deg_map_of_isometry | exact GlobalTheory.deg_map_of_isometry | (intros; apply GlobalTheory.deg_map_of_isometry <;> assumption)
