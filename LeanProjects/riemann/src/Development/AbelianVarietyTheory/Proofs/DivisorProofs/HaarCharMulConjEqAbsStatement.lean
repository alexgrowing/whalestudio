import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarCharMulConjEqAbs
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousCA
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.LeviModulus
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haar_char_mul_conj_eq_abs : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ →
    ∀ [IsTopologicalRing (AE F E)] [LocallyCompactSpace (imA σ)] [MeasurableSpace (imA σ)] [BorelSpace (imA σ)]
      (l : (AE F E)ˣ) (L : imA σ ≃ₜ+ imA σ), (∀ b, (L b : AE F E) = l * cA σ l * b) → addEquivAddHaarChar L = absE F E l := by
  first | exact @GlobalTheory.ImaginaryModulus.addEquivAddHaarChar_imA | exact GlobalTheory.ImaginaryModulus.addEquivAddHaarChar_imA | (intros; apply GlobalTheory.ImaginaryModulus.addEquivAddHaarChar_imA <;> assumption)
