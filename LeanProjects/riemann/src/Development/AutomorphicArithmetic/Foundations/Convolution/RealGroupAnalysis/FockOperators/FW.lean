import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.XApply
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.PsiShift
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.CwShift
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.CoordMk

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Fo.fW :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (W : Weil D) (O : Ops F) w, O.f D.δ w * W.Om (wW F) = -(W.Om (wW F) * O.e D.δ w) := by
  intro F E _ _ _ _ _ _ _ D W O w
  have hc : cw w (rt D.δ) ≠ 0 := (coordMk F E D).2.2.1 w
  have hcc : cc ≠ 0 := by
    simp [cc, Real.pi_ne_zero]
  have h2 : ∀ i j, O.d w i * O.d w j * W.Om (wW F) =
      W.Om (wW F) * (O.p D.δ w i * O.p D.δ w j) := fun i j => by
    rw [mul_assoc, dW, ← mul_assoc, dW, mul_assoc]
  have comm : O.x w 0 * O.x w 1 = O.x w 1 * O.x w 0 := (weyl F O w w 0 1).1
  have p0 : O.p D.δ w 0 = (-cc) • O.x w 1 := rfl
  have p1 : O.p D.δ w 1 = (-cc) • O.x w 0 := rfl
  have p2 : O.p D.δ w 2 = (2 * cc) • O.x w 2 := rfl
  have p3 : O.p D.δ w 3 = (-2 * cw w (rt D.δ) * cc) • O.x w 3 := rfl
  have key : (4 : ℂ)⁻¹ • (O.p D.δ w 2 * O.p D.δ w 2) -
      (4 * cw w (rt D.δ))⁻¹ • (O.p D.δ w 3 * O.p D.δ w 3) -
      O.p D.δ w 1 * O.p D.δ w 0 = cc • O.e D.δ w := by
    rw [p0, p1, p2, p3, Ops.e]
    simp only [smul_mul_smul_comm, comm]
    match_scalars <;> field_simp <;> ring
  have move : ((4 : ℂ)⁻¹ • (O.d w 2 * O.d w 2) - (4 * cw w (rt D.δ))⁻¹ • (O.d w 3 * O.d w 3) -
      O.d w 1 * O.d w 0) * W.Om (wW F) =
      W.Om (wW F) * ((4 : ℂ)⁻¹ • (O.p D.δ w 2 * O.p D.δ w 2) -
        (4 * cw w (rt D.δ))⁻¹ • (O.p D.δ w 3 * O.p D.δ w 3) - O.p D.δ w 1 * O.p D.δ w 0) := by
    simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, h2]
  rw [Ops.f, smul_mul_assoc, move, key, mul_smul_comm, smul_smul,
    neg_mul, inv_mul_cancel₀ hcc, neg_smul, one_smul]
