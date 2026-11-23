import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicModulusNormEqAbs
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipMat

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_modulus_norm_eq_abs : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (x : (AE F E)ˣ),
    (((adeleClass F).modu (Units.map (Algebra.norm (AF F) : AE F E →* AF F) x) : ℝ≥0) : ℝ) = (absE F E x : ℝ) := by
  first | exact @GlobalTheory.ModuAdeleReal.modu_norm_eq_absE_real | exact GlobalTheory.ModuAdeleReal.modu_norm_eq_absE_real | (intros; apply GlobalTheory.ModuAdeleReal.modu_norm_eq_absE_real <;> assumption)
