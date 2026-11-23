import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitDetGramSkewHermitianSignature
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Formalism.LocalToGlobal.IndefiniteReal.DatumF
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnit_det_gram_skewHermitian_signature : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (d : ℕ) (W : Spc F E d) (r s : ℕ), W.IsSkew σ B r s → IsUnit W.J.det := by
  first | exact @GlobalTheory.SkewUnit.isUnit_det_of_isSkew | exact GlobalTheory.SkewUnit.isUnit_det_of_isSkew | (intros; apply GlobalTheory.SkewUnit.isUnit_det_of_isSkew <;> assumption)
