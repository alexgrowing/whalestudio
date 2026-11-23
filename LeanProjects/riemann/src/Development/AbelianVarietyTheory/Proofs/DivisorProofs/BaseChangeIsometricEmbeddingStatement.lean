import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeIsometricEmbedding
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
theorem _root_.GlobalTheory.T.base_change_isometric_embedding : ∀ (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K'] (n m : ℕ) (α : (Fin n → K) →ₗ[K] (Fin m → K)) (h : HermFam K (Fin m → K)) (hW : HermFam K (Fin n → K)) (h' : HermFam K' (Fin m → K')) (hW' : HermFam K' (Fin n → K')), (∀ σ y z, hW.form σ y z = h.form σ (α y) (α z)) → IsBC h h' → IsBC hW hW' → ∃ β : (Fin n → K') →ₗ[K'] (Fin m → K'), Function.Injective β ∧ (∀ σ y z, h'.form σ (β y) (β z) = hW'.form σ y z) ∧ ∀ y : Fin n → K, β (fun i => algebraMap K K' (y i)) = fun j => algebraMap K K' (α y j) := by
  first | exact @GlobalTheory.baseChange_isometry_injective | exact GlobalTheory.baseChange_isometry_injective | (intros; apply GlobalTheory.baseChange_isometry_injective <;> assumption)
