import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DenominatorNormQuadraticExtension
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsLatIntVec
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.denominator_norm_quadratic_extension : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], Module.finrank F E = 2 → ∀ x : F, Ideal.absNorm (den E (algebraMap F E x)) = Ideal.absNorm (den F x) ^ 2 := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.DenMap.absNorm_den_algebraMap | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.DenMap.absNorm_den_algebraMap | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.DenMap.absNorm_den_algebraMap <;> assumption)
