import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocallyConstantMajorants.GammaSplitting.UnipotentTateFunctionalEquation
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MajorantScaled
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LintegralKernelUniformBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MajorantLeSumSwap
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TateLocalL1
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AestronglyMeasurableWhittakerDiagUnits
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Ga
open MeasureTheory Matrix
open Ad3.K Ad3.K.LC Ad3.K.LC.C GlobalTheory.CompanionTheory.GodementFE

namespace GlobalTheory.CompanionTheory.PerUC.Meas

theorem measurable_det_of : Measurable fun h : M22 => (Matrix.of h).det := by
  have h : Continuous fun h : M22 => (Matrix.of h).det :=
    Continuous.matrix_det (continuous_id (X := M22))
  exact h.measurable

theorem measurable_inv_entry (i j : Fin 2) :
    Measurable fun h : M22 => (Matrix.of h)⁻¹ i j := by
  have e : (fun h : M22 => (Matrix.of h)⁻¹ i j) =
      fun h : M22 => (Matrix.of h).det⁻¹ * (Matrix.of h).adjugate i j := by
    funext h
    simp [Matrix.inv_def, Ring.inverse_eq_inv']
  rw [e]
  have hadj : Continuous fun h : M22 => (Matrix.of h).adjugate i j :=
    (Continuous.matrix_adjugate (continuous_id (X := M22))).matrix_elem i j
  exact measurable_det_of.inv.mul hadj.measurable

theorem measurable_det_inv : Measurable fun h : M22 => ((Matrix.of h)⁻¹).det := by
  have e : (fun h : M22 => ((Matrix.of h)⁻¹).det) = fun h : M22 =>
      (Matrix.of h)⁻¹ 0 0 * (Matrix.of h)⁻¹ 1 1 - (Matrix.of h)⁻¹ 0 1 * (Matrix.of h)⁻¹ 1 0 := by
    funext h
    exact Matrix.det_fin_two _
  rw [e]
  exact ((measurable_inv_entry 0 0).mul (measurable_inv_entry 1 1)).sub
    ((measurable_inv_entry 0 1).mul (measurable_inv_entry 1 0))

theorem continuous_innQ_integrand (Ψ : Sw) :
    Continuous fun p : (M22 × ℂ × (Fin 2 → ℂ)) × (Fin 2 → ℂ) =>
      Ψ (Matrix.of.symm (Matrix.of p.1.1 * blk p.2 *
          ((1 : GL (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ)), p.1.2.2) *
        psiC (-(p.1.2.1 * p.2 1)) := by
  refine Continuous.mul (Ψ.continuous.comp (Continuous.prodMk ?_ (by fun_prop)))
    (continuous_psiC.comp (by fun_prop))
  have hb : Continuous fun x : Fin 2 → ℂ => blk x := by
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [blk] <;> fun_prop
  have hh : Continuous fun p : (M22 × ℂ × (Fin 2 → ℂ)) × (Fin 2 → ℂ) => Matrix.of p.1.1 :=
    continuous_fst.fst
  exact (hh.matrix_mul (hb.comp continuous_snd)).matrix_mul continuous_const

theorem stronglyMeasurable_innQ (Ψ : Sw) :
    StronglyMeasurable fun p : M22 × ℂ × (Fin 2 → ℂ) => innQ Ψ 1 p.1 p.2.1 p.2.2 :=
  (continuous_innQ_integrand Ψ).stronglyMeasurable.integral_prod_right'

theorem measurable_whittakerGL2_inner_quotient : ∀ (k : ℕ) (Ψ : Ad3.K.LC.Sw),
    Measurable (fun p : ℂˣ × Ad3.K.LC.M22 =>
      Ad3.K.LC.C.W2 k (Ad3.K.LC.C.innQ Ψ 1 p.2 (p.1 : ℂ)⁻¹) (Matrix.of p.2)⁻¹) := by
  intro k Ψ
  have hT : Measurable fun p : ℂˣ × M22 => ((p.1 : ℂ))⁻¹ :=
    (GlobalTheory.CompanionTheory.TateC.val_measurableEmbedding.measurable.comp measurable_fst).inv
  have hE : ∀ i j : Fin 2, Measurable fun r : ((ℂˣ × M22) × ℂ) × ℂ =>
      (Matrix.of r.1.1.2)⁻¹ i j := fun i j =>
    (measurable_inv_entry i j).comp (measurable_snd.comp (measurable_fst.comp measurable_fst))
  have hV : Measurable fun r : ((ℂˣ × M22) × ℂ) × ℂ =>
      Matrix.vecMul ![r.1.2, r.1.2 * r.2] (Matrix.of r.1.1.2)⁻¹ := by
    refine measurable_pi_iff.2 fun j => ?_
    have e : (fun r : ((ℂˣ × M22) × ℂ) × ℂ =>
        Matrix.vecMul ![r.1.2, r.1.2 * r.2] (Matrix.of r.1.1.2)⁻¹ j) =
        fun r => r.1.2 * (Matrix.of r.1.1.2)⁻¹ 0 j + r.1.2 * r.2 * (Matrix.of r.1.1.2)⁻¹ 1 j := by
      funext r
      simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]
    rw [e]
    have h1 : Measurable fun r : ((ℂˣ × M22) × ℂ) × ℂ => r.1.2 := measurable_snd.comp measurable_fst
    have h2 : Measurable fun r : ((ℂˣ × M22) × ℂ) × ℂ => r.2 := measurable_snd
    exact (h1.mul (hE 0 j)).add ((h1.mul h2).mul (hE 1 j))
  have hA : Measurable fun r : ((ℂˣ × M22) × ℂ) × ℂ =>
      ((r.1.1.2, ((r.1.1.1 : ℂ))⁻¹, Matrix.vecMul ![r.1.2, r.1.2 * r.2] (Matrix.of r.1.1.2)⁻¹) :
        M22 × ℂ × (Fin 2 → ℂ)) :=
    (measurable_snd.comp (measurable_fst.comp measurable_fst)).prodMk
      ((hT.comp (measurable_fst.comp measurable_fst)).prodMk hV)
  have hG : StronglyMeasurable fun r : ((ℂˣ × M22) × ℂ) × ℂ =>
      innQ Ψ 1 r.1.1.2 ((r.1.1.1 : ℂ))⁻¹
          (Matrix.vecMul ![r.1.2, r.1.2 * r.2] (Matrix.of r.1.1.2)⁻¹) * psiC (-r.2) :=
    ((stronglyMeasurable_innQ Ψ).comp_measurable hA).mul
      (continuous_psiC.comp (continuous_snd.neg)).stronglyMeasurable
  have hF : StronglyMeasurable fun q : (ℂˣ × M22) × ℂ =>
      ∫ y : ℂ, innQ Ψ 1 q.1.2 ((q.1.1 : ℂ))⁻¹
          (Matrix.vecMul ![q.2, q.2 * y] (Matrix.of q.1.2)⁻¹) * psiC (-y) :=
    hG.integral_prod_right'
  have hP4 : StronglyMeasurable fun q : (ℂˣ × M22) × ℂ => ph (4 * (k : ℤ) - 4) q.2 :=
    ((measurable_ph _).comp measurable_snd).stronglyMeasurable
  have hH : StronglyMeasurable fun p : ℂˣ × M22 => ∫ t : ℂ, ph (4 * (k : ℤ) - 4) t *
      ∫ y : ℂ, innQ Ψ 1 p.2 ((p.1 : ℂ))⁻¹
          (Matrix.vecMul ![t, t * y] (Matrix.of p.2)⁻¹) * psiC (-y) :=
    (hP4.mul hF).integral_prod_right'
  have hD : Measurable fun p : ℂˣ × M22 => ((Matrix.of p.2)⁻¹).det :=
    measurable_det_inv.comp measurable_snd
  have hP2 : Measurable fun p : ℂˣ × M22 => ph (2 * (k : ℤ) - 2) ((Matrix.of p.2)⁻¹).det :=
    (measurable_ph _).comp hD
  have hN : Measurable fun p : ℂˣ × M22 => (((‖((Matrix.of p.2)⁻¹).det‖ : ℝ)) : ℂ) :=
    Complex.measurable_ofReal.comp hD.norm
  exact (hP2.mul hN).mul hH.measurable

end GlobalTheory.CompanionTheory.PerUC.Meas
