import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModulusOfNormEqAbs

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

theorem GlobalTheory.ModuAdeleReal.modu_norm_eq_absE_real : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (x : (AE F E)ˣ),
    (((adeleClass F).modu (Units.map (Algebra.norm (AF F) : AE F E →* AF F) x) : ℝ≥0) : ℝ) = (absE F E x : ℝ) := by
  intro F E _ _ _ _ _ x
  exact congrArg (fun r : ℝ≥0 => (r : ℝ)) (GlobalTheory.ModuAdele.modu_norm_eq_absE F E x)
