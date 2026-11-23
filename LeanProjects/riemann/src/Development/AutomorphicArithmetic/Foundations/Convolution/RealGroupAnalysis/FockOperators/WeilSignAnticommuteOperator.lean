import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.AtLaws
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.PsiShift

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

private theorem wW_sq (F : Type) [Field F] [NumberField F] : wW F * wW F = mD (-1 : (A F)ˣ) := by
  apply Subtype.ext
  change (wW F).1 * (wW F).1 = (mD (-1 : (A F)ˣ)).1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [wW, mD, Matrix.mul_apply, Fin.sum_univ_two]

private theorem cw_neg {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (w : InfinitePlace F) (a : A F) :
    cw w (-a) = -cw w a := by
  simp [cw, map_neg]

private theorem weilSign_anticommute_operator {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [IsTotallyReal F] [IsTotallyComplex E] {D : Dat F E} (W : Weil D) (O : Ops F) (w : InfinitePlace F) (j : Fin 4) :
    W.Om (mD (-1 : (A F)ˣ)) * O.x w j = -(O.x w j * W.Om (mD (-1 : (A F)ˣ))) := by
  apply LinearMap.ext
  intro φ
  apply Subtype.ext
  funext v
  have h1 := W.Om_m (-1 : (A F)ˣ) (O.x w j φ) v
  have h2 := O.x_apply w j (W.Om (mD (-1 : (A F)ˣ)) φ) v
  have h3 := W.Om_m (-1 : (A F)ˣ) φ v
  have h4 := O.x_apply w j φ (fun i => (((-1 : (A F)ˣ) : A F)) * v i)
  change (W.Om (mD (-1 : (A F)ˣ)) (O.x w j φ)).1 v = -((O.x w j (W.Om (mD (-1 : (A F)ˣ)) φ)).1 v)
  rw [h1, h2, h3, h4]
  have h5 : cw w ((((-1 : (A F)ˣ) : A F)) * v j) = -cw w (v j) := by
    rw [Units.val_neg, Units.val_one, neg_one_mul, cw_neg]
  rw [h5]
  ring

private theorem R_p {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [IsTotallyReal F] [IsTotallyComplex E] {D : Dat F E} (W : Weil D) (O : Ops F) (w : InfinitePlace F) (i : Fin 4) :
    W.Om (mD (-1 : (A F)ˣ)) * O.p D.δ w i = -(O.p D.δ w i * W.Om (mD (-1 : (A F)ˣ))) := by
  fin_cases i <;> simp [Ops.p, mul_smul_comm, smul_mul_assoc, weilSign_anticommute_operator W O w]

theorem UpperTheory.ConvolutionTheory.R2.Fo.pW :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (W : Weil D) (O : Ops F) w i, O.p D.δ w i * W.Om (wW F) = -(W.Om (wW F) * O.d w i) := by
  intro F E _ _ _ _ _ _ _ D W O w i
  have hd := UpperTheory.ConvolutionTheory.R2.Fo.dW F E D W O w i
  have hR : W.Om (wW F) * W.Om (wW F) = W.Om (mD (-1 : (A F)ˣ)) := by
    rw [← map_mul, wW_sq]
  have hinv : W.Om (wW F) * W.Om (wW F)⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one]
  have key : (W.Om (wW F) * O.d w i) * W.Om (wW F) = (-(O.p D.δ w i * W.Om (wW F))) * W.Om (wW F) := by
    calc (W.Om (wW F) * O.d w i) * W.Om (wW F)
        = W.Om (wW F) * (O.d w i * W.Om (wW F)) := mul_assoc _ _ _
      _ = (W.Om (wW F) * W.Om (wW F)) * O.p D.δ w i := by rw [hd, mul_assoc]
      _ = -(O.p D.δ w i * (W.Om (wW F) * W.Om (wW F))) := by rw [hR, R_p W O w i]
      _ = (-(O.p D.δ w i * W.Om (wW F))) * W.Om (wW F) := by rw [neg_mul, mul_assoc]
  have key2 : W.Om (wW F) * O.d w i = -(O.p D.δ w i * W.Om (wW F)) := by
    have := congrArg (· * W.Om (wW F)⁻¹) key
    simpa only [mul_assoc, hinv, mul_one] using this
  rw [key2, neg_neg]
