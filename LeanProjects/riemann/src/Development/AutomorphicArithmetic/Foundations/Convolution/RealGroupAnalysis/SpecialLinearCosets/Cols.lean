import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.GoodU
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.PsiLaws

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.ConvolutionTheory.R2.I
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.I.ptN :
    ∀ (F : Type) [Field F] [NumberField F] (v : P F) (a : M2 v → ℂ) (X : M2 v),
      (∀ b, ψl v (-(b * X.det)) * Pt a X = Pt (fun m => a (m * !![1, b; 0, 1])) X) ∧
      ∀ s, Pt a (X * !![1, 0; -s, 1]) = Pt (fun m => ψl v (-(s * m.det)) * a m) X := by
  intro F _ _ v a X
  haveI : (μ2 v).IsAddHaarMeasure := by unfold μ2; infer_instance
  have hadd := (UpperTheory.ConvolutionTheory.R2.I.psiLaws F v).2.2.1
  refine ⟨fun b => ?_, fun s => ?_⟩
  · unfold Pt
    rw [← integral_const_mul,
      ← integral_add_right_eq_self (μ := μ2 v) (fun c' => ψl v (-(b * X.det)) *
        (a (cols (fun i => X i 1) c') * ψl v (X 0 0 * c' 1 - X 1 0 * c' 0)))
        (b • fun i => X i 1)]
    refine integral_congr_ae (Eventually.of_forall fun c' => ?_)
    have hm : cols (fun i => X i 1) c' * !![1, b; 0, 1]
        = cols (fun i => X i 1) (c' + b • fun i => X i 1) := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [cols, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
    have hp : ψl v (-(b * X.det)) * ψl v (X 0 0 * (c' + b • fun i => X i 1) 1
          - X 1 0 * (c' + b • fun i => X i 1) 0) = ψl v (X 0 0 * c' 1 - X 1 0 * c' 0) := by
      rw [← hadd]
      congr 1
      simp [Matrix.det_fin_two]
      ring
    simp only [hm]
    rw [mul_left_comm, hp]
  · unfold Pt
    rw [show (fun i => (X * !![1, 0; -s, 1]) i 1) = (fun i => X i 1) by
      funext i
      simp [Matrix.mul_apply, Fin.sum_univ_two]]
    refine integral_congr_ae (Eventually.of_forall fun c' => ?_)
    have hp : ψl v ((X * !![1, 0; -s, 1]) 0 0 * c' 1 - (X * !![1, 0; -s, 1]) 1 0 * c' 0)
        = ψl v (-(s * (cols (fun i => X i 1) c').det)) * ψl v (X 0 0 * c' 1 - X 1 0 * c' 0) := by
      rw [← hadd]
      congr 1
      simp [cols, Matrix.det_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
      ring
    simp only []
    rw [hp]
    ring
