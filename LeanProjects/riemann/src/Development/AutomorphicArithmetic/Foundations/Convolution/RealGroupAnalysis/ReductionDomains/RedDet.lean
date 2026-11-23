import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.ContinuousEntry
import GroundTheory.GlobalFields.TateThesis.AdeleScaling

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

theorem UpperTheory.ConvolutionTheory.R2.M.redDet :
    ∀ (F : Type) [Field F] [NumberField F], ∀ (g : G1 F) (γ : GL (Fin 2) F), ∀ b ∈ Reduction.adelicBorel (K := F) (n := 2), ∀ k : GL (Fin 2) (A F), AdelicGLn.diagonal F 2 γ * gl g = b * k → ∃ γ' : Matrix.SpecialLinearGroup (Fin 2) F, ∃ b' ∈ Reduction.adelicBorel (K := F) (n := 2), gl (ratS F γ' * g) = b' * k ∧ b'.val 0 0 = b.val 0 0 ∧ Reduction.adeleAbs (b'.val 1 1) = Reduction.adeleAbs (b.val 1 1) := by
  intro F _ _ g γ b hb k h
  set d : Fˣ := Matrix.GeneralLinearGroup.det γ with hd
  have hdet : γ.val.det = (d : F) := rfl
  set t : (A F)ˣ := (IdeleGroup.diagonal F d)⁻¹ with ht
  have htv : ((t : (A F)ˣ) : A F) = algebraMap F (A F) ((d⁻¹ : Fˣ) : F) := by
    simp [ht, IdeleGroup.diagonal, ← map_inv]
  let γ' : Matrix.SpecialLinearGroup (Fin 2) F :=
    ⟨!![1, 0; 0, ((d⁻¹ : Fˣ) : F)] * γ.val, by
      rw [Matrix.det_mul, hdet, Matrix.det_fin_two_of]; simp⟩
  have hg : gl (ratS F γ') = dM t * AdelicGLn.diagonal F 2 γ := by
    refine Units.ext ?_
    rw [Units.val_mul, val_gl, val_ratS]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [γ', dM, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, htv, map_mul]
  obtain ⟨u, hu⟩ := Reduction.isUnit_apply_self_of_mem_adelicBorel hb 1
  have hlow : b.val 1 0 = 0 := Reduction.mem_adelicBorel.1 hb (by decide)
  refine ⟨γ', dM t * b, ?_, ?_, ?_, ?_⟩
  · refine mul_mem (Reduction.mem_adelicBorel.2 ?_) hb
    intro i j hij
    fin_cases i <;> fin_cases j <;> first | (simp [dM]; done) | (simp at hij)
  · have hm : gl (ratS F γ' * g) = gl (ratS F γ') * gl g := map_mul _ _ _
    rw [hm, hg, mul_assoc, h, mul_assoc]
  · simp [dM, Matrix.mul_apply, Fin.sum_univ_two]
  · have e : (dM t * b).val 1 1 = ((t * u : (A F)ˣ) : A F) := by
      simp [dM, Matrix.mul_apply, Fin.sum_univ_two, hu]
    rw [e, ← hu, Reduction.adeleAbs_units, Reduction.adeleAbs_units]
    have := ab_mul t u
    have h1 : ab t = 1 := by rw [ht, ab_inv, ab_diag, inv_one]
    rw [h1, one_mul] at this
    exact this
