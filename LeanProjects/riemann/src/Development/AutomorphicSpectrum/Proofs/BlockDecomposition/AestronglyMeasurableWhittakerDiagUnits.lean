import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocallyConstantMajorants.GammaSplitting.ComplexMatrixMajorantIntegrable
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableMulCIff
open MeasureTheory Matrix
open Ad3.K Ad3.K.LC Ad3.K.LC.C GlobalTheory.CompanionTheory.GodementFE

namespace GlobalTheory.CompanionTheory.GodementFE

theorem measurable_ph (n : ℤ) : Measurable (ph n) := by
  have h0 : Measurable fun z : ℂ => z / ((‖z‖ : ℝ) : ℂ) := by fun_prop
  cases n with
  | ofNat m =>
    have : ph (Int.ofNat m) = fun z : ℂ => (z / ((‖z‖ : ℝ) : ℂ)) ^ m := by
      funext z
      simp [ph]
    rw [this]
    exact h0.pow_const m
  | negSucc m =>
    have : ph (Int.negSucc m) = fun z : ℂ => ((z / ((‖z‖ : ℝ) : ℂ)) ^ (m + 1))⁻¹ := by
      funext z
      simp only [ph, zpow_negSucc]
    rw [this]
    exact (h0.pow_const (m + 1)).inv

theorem continuous_diag_mul (g : Matrix (Fin 2) (Fin 2) ℂ) :
    Continuous fun a : ℂ => d2 a * g := by
  refine Continuous.matrix_mul ?_ continuous_const
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [d2] <;> fun_prop

theorem continuous_godement (f : SchwartzMap (Fin 2 → ℂ) ℂ) (g : Matrix (Fin 2) (Fin 2) ℂ) :
    Continuous fun p : (ℂ × ℂ) × ℂ =>
      f (Matrix.vecMul ![p.1.2, p.1.2 * p.2] (d2 p.1.1 * g)) * psiC (-p.2) := by
  refine Continuous.mul (f.continuous.comp (Continuous.matrix_vecMul ?_ ?_))
    (continuous_psiC.comp (by fun_prop))
  · exact continuous_vec.comp (Continuous.prodMk (by fun_prop) (by fun_prop))
  · exact (continuous_diag_mul g).comp (by fun_prop)

theorem stronglyMeasurable_whittakerGL2_diag (k : ℕ) (f : SchwartzMap (Fin 2 → ℂ) ℂ)
    (g : Matrix (Fin 2) (Fin 2) ℂ) :
    StronglyMeasurable fun a : ℂ => W2 k f (d2 a * g) := by
  have hF : StronglyMeasurable fun q : ℂ × ℂ =>
      ∫ y : ℂ, f (Matrix.vecMul ![q.2, q.2 * y] (d2 q.1 * g)) * psiC (-y) :=
    (continuous_godement f g).stronglyMeasurable.integral_prod_right'
  have hT : StronglyMeasurable fun q : ℂ × ℂ => ph (4 * (k : ℤ) - 4) q.2 :=
    ((measurable_ph _).comp measurable_snd).stronglyMeasurable
  have hH : StronglyMeasurable fun a : ℂ => ∫ t : ℂ, ph (4 * (k : ℤ) - 4) t *
      ∫ y : ℂ, f (Matrix.vecMul ![t, t * y] (d2 a * g)) * psiC (-y) :=
    (hT.mul hF).integral_prod_right'
  have hdet : Continuous fun a : ℂ => (d2 a * g).det := (continuous_diag_mul g).matrix_det
  have hP : StronglyMeasurable fun a : ℂ => ph (2 * (k : ℤ) - 2) (d2 a * g).det :=
    ((measurable_ph _).comp hdet.measurable).stronglyMeasurable
  have hN : StronglyMeasurable fun a : ℂ => (((‖(d2 a * g).det‖ : ℝ)) : ℂ) :=
    (Complex.continuous_ofReal.comp hdet.norm).stronglyMeasurable
  exact (hP.mul hN).mul hH

theorem aestronglyMeasurable_whittakerGL2_diag : ∀ (k : ℕ) (f : SchwartzMap (Fin 2 → ℂ) ℂ) (g : Matrix (Fin 2) (Fin 2) ℂ),
    AEStronglyMeasurable (fun a : ℂˣ => W2 k f (d2 a * g)) mulC := fun k f g =>
  ((stronglyMeasurable_whittakerGL2_diag k f g).comp_measurable val_measEmb.measurable).aestronglyMeasurable

end GlobalTheory.CompanionTheory.GodementFE
