import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.Smooth
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaReindexing.ActMat
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaReindexing.MeasAct

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.D.ftAct :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (D : Dat F E) (h : GL (Fin 2) (A E)) (φ : S4 F) (v : V4 F),
    ft4 D.δ (fun y => φ.1 (D.act h⁻¹ y)) v = ((ab (nu F h) ^ 2 : ℝ) : ℂ) * ft4 D.δ φ.1 (fun i => (nu F h : A F) * D.act h⁻¹ v i) := by
  intro F E _ _ _ _ _ D h φ v
  obtain ⟨ρ, hρ, -, hB⟩ := UpperTheory.ConvolutionTheory.R2.D.actMat F E D
  have hmeas : ∀ k, Measurable (D.act k) := by
    intro k
    have : D.act k = fun x => (ρ k).val *ᵥ x := funext (hρ k)
    rw [this]
    exact (Continuous.matrix_mulVec continuous_const continuous_id).measurable
  have hinv : ∀ y, D.act h⁻¹ (D.act h y) = y := by
    intro y
    rw [hρ, hρ, Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul]
    simp
  have hinv' : ∀ y, D.act h (D.act h⁻¹ y) = y := by
    intro y
    rw [hρ, hρ, Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul]
    simp
  let e : V4 F ≃ᵐ V4 F :=
    { toFun := D.act h, invFun := D.act h⁻¹, left_inv := hinv, right_inv := hinv',
      measurable_toFun := hmeas h, measurable_invFun := hmeas h⁻¹ }
  have hc : 0 < ab (nu F h) := (IdeleGroup.ideleModule F (nu F h)).2
  have key : ∀ g : V4 F → ℂ, ∫ y, g (D.act h y) ∂(adeleMeasurePi F) =
      (((ab (nu F h))⁻¹ ^ 2 : ℝ) : ℂ) * ∫ y, g y ∂(adeleMeasurePi F) := by
    intro g
    have h1 := MeasureTheory.integral_map_equiv (μ := adeleMeasurePi F (ι := Fin 4)) e g
    have h2 : Measure.map (⇑e) (adeleMeasurePi F (ι := Fin 4)) =
        ENNReal.ofReal ((ab (nu F h))⁻¹ ^ 2) • adeleMeasurePi F (ι := Fin 4) :=
      UpperTheory.ConvolutionTheory.R2.D.measAct F E D h
    rw [h2, integral_smul_measure, ENNReal.toReal_ofReal (by positivity)] at h1
    have h3 : ∫ y, g (D.act h y) ∂(adeleMeasurePi F) = ∫ x, g (e x) ∂(adeleMeasurePi F) := rfl
    rw [h3, ← h1, Complex.real_smul]
  have hk := key (fun y => φ.1 (D.act h⁻¹ y) * ψ (B4 D.δ y v))
  have hpt : ∀ y, φ.1 (D.act h⁻¹ (D.act h y)) * ψ (B4 D.δ (D.act h y) v) =
      φ.1 y * ψ (B4 D.δ y (fun i => (nu F h : A F) * D.act h⁻¹ v i)) := by
    intro y
    have hb : B4 D.δ (D.act h y) v = B4 D.δ y (fun i => (nu F h : A F) * D.act h⁻¹ v i) := by
      have h4 : B4 D.δ (D.act h y) (D.act h (D.act h⁻¹ v)) = (nu F h : A F) * B4 D.δ y (D.act h⁻¹ v) := hB h _ _
      rw [hinv' v] at h4
      rw [h4]
      simp only [B4]
      ring
    rw [hinv, hb]
  simp only [hpt] at hk
  unfold ft4
  rw [hk, ← mul_assoc, ← Complex.ofReal_mul]
  have : ab (nu F h) ^ 2 * (ab (nu F h))⁻¹ ^ 2 = 1 := by field_simp
  rw [this]
  simp
