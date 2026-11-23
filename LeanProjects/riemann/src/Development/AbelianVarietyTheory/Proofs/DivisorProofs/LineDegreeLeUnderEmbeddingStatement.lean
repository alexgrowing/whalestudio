import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineDegreeLeUnderEmbedding
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
theorem _root_.GlobalTheory.T.line_degree_le_under_embedding : ∀ (K' : Type) [Field K'] [NumberField K'] (n m : ℕ) (hW' : HermFam K' (Fin n → K')) (h' : HermFam K' (Fin m → K')) (β : (Fin n → K') →ₗ[K'] (Fin m → K')) (M' : Submodule (𝓞 K') (Fin n → K')) (M : Submodule (𝓞 K') (Fin m → K')) (x : Fin n → K'), Function.Injective β → (∀ σ y z, h'.form σ (β y) (β z) = hW'.form σ y z) → Full M' → Full M → (∀ y ∈ M', β y ∈ M) → x ≠ 0 → deg hW' (lineLat M' x) ≤ deg h' (lineLat M (β x)) := by
  first | exact @GlobalTheory.deg_lineLat_le_deg_lineLat_map | exact GlobalTheory.deg_lineLat_le_deg_lineLat_map | (intros; apply GlobalTheory.deg_lineLat_le_deg_lineLat_map <;> assumption)
