import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.NApply
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.LamGen
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaReindexing.ActMat
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaReindexing.MeasAct
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaReindexing.MapMulInvEqOne

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

private theorem act_meas {F : Type} [Field F] [NumberField F] (g : GL (Fin 4) (A F)) :
    Measurable fun v : V4 F => g.val *ᵥ v :=
  (continuous_const.matrix_mulVec continuous_id).measurable

private theorem idx_of_equiv {F : Type} [Field F] [NumberField F] (δ : F) (b a : A F) (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (T : V4 F ≃ᵐ V4 F) (hadd : ∀ x y, T (x + y) = T x + T y) (hq : ∀ v, q4 δ (T v) = a * q4 δ v)
    (hm : Measure.map T (adeleMeasurePi F) = ENNReal.ofReal r • adeleMeasurePi F (ι := Fin 4))
    (hS : ∀ φ : S4 F, (fun v => φ.1 (T.symm v)) ∈ schwartzBruhatPi F (Fin 4))
    (hc : IsIdx δ b c) : IsIdx δ (b * a) (c * (r : ℂ)) := by
  intro φ
  have hL := (UpperTheory.ConvolutionTheory.R2.C.lamGen).2.2 (V4 F) (V4 F) (adeleMeasurePi F) (adeleMeasurePi F) T
    (ENNReal.ofReal r) hadd hm (fun v => ψ (b * q4 δ v)) (fun v => φ.1 (T.symm v))
  rw [ENNReal.toReal_ofReal hr] at hL
  obtain ⟨h1, h2⟩ := hL
  simp only [MeasurableEquiv.symm_apply_apply, hq] at h1 h2
  have h3 := hc ⟨_, hS φ⟩
  change abelian₂ (adeleMeasurePi F) (fun v => ψ (b * q4 δ v)) (fun v => φ.1 (T.symm v)) = c * ∫ v, φ.1 (T.symm v) ∂(adeleMeasurePi F) at h3
  change abelian₂ (adeleMeasurePi F) (fun v => ψ (b * a * q4 δ v)) φ.1 = _
  simp only [mul_assoc]
  rw [h1, h3, h2]
  ring

theorem UpperTheory.ConvolutionTheory.R2.C.idxNorm :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (D : Dat F E) (b : A F) (c : ℂ) (z : (A E)ˣ), IsIdx D.δ b c →
    IsIdx D.δ (b * (ideleNorm F E z : (A F)ˣ)) (c * (((ab (ideleNorm F E z))⁻¹ ^ 2 : ℝ) : ℂ)) := by
  intro F E _ _ _ _ _ D b c z hc
  obtain ⟨ρ, hρ, hq, -⟩ := UpperTheory.ConvolutionTheory.R2.D.actMat F E D
  have hdet : Matrix.GeneralLinearGroup.det (aE z) = z := by
    apply Units.ext
    change Matrix.det !![(z : A E), 0; 0, 1] = _
    simp [Matrix.det_fin_two]
  have hnu : nu F (aE z) = ideleNorm F E z := by
    rw [nu, hdet]
  have hm := UpperTheory.ConvolutionTheory.R2.D.measAct F E D (aE z)
  rw [hnu] at hm
  have hinv1 : ∀ v, D.act (aE z)⁻¹ (D.act (aE z) v) = v := fun v => by
    rw [hρ, hρ, Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one,
      Units.val_one, Matrix.one_mulVec]
  have hinv2 : ∀ v, D.act (aE z) (D.act (aE z)⁻¹ v) = v := fun v => by
    rw [hρ, hρ, Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one,
      Units.val_one, Matrix.one_mulVec]
  have hme : ∀ h, Measurable (D.act h) := fun h => by
    have : D.act h = fun v => (ρ h).val *ᵥ v := funext (hρ h)
    rw [this]
    exact act_meas (ρ h)
  let T : V4 F ≃ᵐ V4 F :=
    { toFun := D.act (aE z)
      invFun := D.act (aE z)⁻¹
      left_inv := hinv1
      right_inv := hinv2
      measurable_toFun := hme _
      measurable_invFun := hme _ }
  refine idx_of_equiv D.δ b _ c _ (sq_nonneg _) T (fun x y => ?_) (fun v => ?_) hm (fun φ => ?_) hc
  · change D.act (aE z) (x + y) = D.act (aE z) x + D.act (aE z) y
    simp only [hρ, Matrix.mulVec_add]
  · change q4 D.δ (D.act (aE z) v) = _
    rw [hq, hnu]
  · change (fun v => φ.1 (D.act (aE z)⁻¹ v)) ∈ _
    have : (fun v => φ.1 (D.act (aE z)⁻¹ v)) = fun v => φ.1 ((ρ (aE z)⁻¹).val *ᵥ v) :=
      funext fun v => by rw [hρ]
    rw [this]
    exact UpperTheory.ConvolutionTheory.R2.D.sClos F (Fin 4) (ρ (aE z)⁻¹) φ.1 φ.2
