import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.RationalPrimesBelowPlaces
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.SquareIntegrable.SSmooth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TemperedBoundGL2
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DetThreePointsEqExpansion
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.DualHol

noncomputable section

namespace GlobalTheory.CompanionTheory.DualHol.IwMeas

section

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

theorem continuous_diag_torus_GL2 : Continuous (fun q : Fˣ × Fˣ => (dg2 q.1 q.2 : GL (Fin 2) F)) := by
  have hv1 : Continuous (fun q : Fˣ × Fˣ => (q.1 : F)) := Units.continuous_val.comp continuous_fst
  have hv2 : Continuous (fun q : Fˣ × Fˣ => (q.2 : F)) := Units.continuous_val.comp continuous_snd
  have hi1 : Continuous (fun q : Fˣ × Fˣ => ((q.1⁻¹ : Fˣ) : F)) :=
    (Units.continuous_iff.1 continuous_id).2.comp continuous_fst
  have hi2 : Continuous (fun q : Fˣ × Fˣ => ((q.2⁻¹ : Fˣ) : F)) :=
    (Units.continuous_iff.1 continuous_id).2.comp continuous_snd
  rw [Units.continuous_iff]
  constructor
  · refine continuous_matrix fun i j => ?_
    show Continuous fun q : Fˣ × Fˣ => (!![(q.1 : F), 0; 0, (q.2 : F)] : Matrix (Fin 2) (Fin 2) F) i j
    fin_cases i <;> fin_cases j <;> first | (simpa using hv1) | (simpa using hv2) | (simpa using continuous_const)
  · refine continuous_matrix fun i j => ?_
    show Continuous fun q : Fˣ × Fˣ =>
      (!![((q.1⁻¹ : Fˣ) : F), 0; 0, ((q.2⁻¹ : Fˣ) : F)] : Matrix (Fin 2) (Fin 2) F) i j
    fin_cases i <;> fin_cases j <;> first | (simpa using hi1) | (simpa using hi2) | (simpa using continuous_const)

theorem continuous_tinv {n : Type} [Fintype n] [DecidableEq n] :
    Continuous (GL2LocalData.tinv : GL n F → GL n F) := by
  rw [Units.continuous_iff]
  constructor
  · show Continuous fun g : GL n F => Matrix.transpose (g⁻¹ : GL n F).val
    exact (Units.continuous_iff.1 continuous_id).2.matrix_transpose
  · show Continuous fun g : GL n F => Matrix.transpose g.val
    exact Units.continuous_val.matrix_transpose

theorem em_inv (h : GL (Fin 2) F) : GL2LocalData.em h⁻¹ = (GL2LocalData.em h)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left (Units.ext ?_)
  have h1 : (h⁻¹).val * h.val = 1 := by rw [← Units.val_mul]; simp
  have e : ∀ i j, (h⁻¹).val i 0 * h.val 0 j + (h⁻¹).val i 1 * h.val 1 j = (1 : Matrix (Fin 2) (Fin 2) F) i j := by
    intro i j
    have := congr_fun (congr_fun h1 i) j
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  rw [Units.val_mul, GlobalTheory.CompanionTheory.KTwoWhittakerSubgroup.em_val, GlobalTheory.CompanionTheory.KTwoWhittakerSubgroup.em_val]
  have e00 := e 0 0
  have e01 := e 0 1
  have e10 := e 1 0
  have e11 := e 1 1
  simp at e00 e01 e10 e11
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, e00, e01, e10, e11]

theorem continuous_em : Continuous (GL2LocalData.em : GL (Fin 2) F → GL (Fin 3) F) := by
  have hv : ∀ i j, Continuous fun h : GL (Fin 2) F => h.val i j := fun i j =>
    (Units.continuous_val (M := Matrix (Fin 2) (Fin 2) F)).matrix_elem i j
  have hi : ∀ i j, Continuous fun h : GL (Fin 2) F => (h⁻¹).val i j := fun i j =>
    (Units.continuous_iff.1 (continuous_id (X := GL (Fin 2) F))).2.matrix_elem i j
  rw [Units.continuous_iff]
  constructor
  · refine continuous_matrix fun i j => ?_
    show Continuous fun h : GL (Fin 2) F => (GL2LocalData.em h).val i j
    simp only [GlobalTheory.CompanionTheory.KTwoWhittakerSubgroup.em_val]
    fin_cases i <;> fin_cases j <;> first | (simpa using hv _ _) | (simpa using continuous_const)
  · refine continuous_matrix fun i j => ?_
    show Continuous fun h : GL (Fin 2) F => ((GL2LocalData.em h)⁻¹).val i j
    simp only [← em_inv, GlobalTheory.CompanionTheory.KTwoWhittakerSubgroup.em_val]
    fin_cases i <;> fin_cases j <;> first | (simpa using hi _ _) | (simpa using continuous_const)

end

theorem measurable_dual_iwasawa : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (W : GL (Fin 3) F → ℂ) (W' : GL (Fin 2) F → ℂ), Continuous W → Measurable W' → Measurable (fun p : Fˣ × Fˣ × GL (Fin 2) F => GL2LocalData.dW3 W (GL2LocalData.em (dg2 (p.1 * p.2.1) p.2.1 * p.2.2)) * GL2LocalData.dW2 W' (dg2 (p.1 * p.2.1) p.2.1 * p.2.2)) := by
  intro F _ _ _ _ _ _ W W' hW hW'
  have hΦ : Continuous (fun p : Fˣ × Fˣ × GL (Fin 2) F => (dg2 (p.1 * p.2.1) p.2.1 * p.2.2 : GL (Fin 2) F)) :=
    (continuous_diag_torus_GL2.comp
      ((continuous_fst.mul (continuous_fst.comp continuous_snd)).prodMk
        (continuous_fst.comp continuous_snd))).mul (continuous_snd.comp continuous_snd)
  have h3 : Continuous (fun g : GL (Fin 2) F => GL2LocalData.dW3 W (GL2LocalData.em g)) :=
    hW.comp (continuous_const.mul (continuous_tinv.comp continuous_em))
  have h2 : Continuous (fun g : GL (Fin 2) F => (GL2LocalData.w2 * GL2LocalData.tinv g : GL (Fin 2) F)) :=
    continuous_const.mul continuous_tinv
  have m3 := (h3.comp hΦ).measurable
  have m2 : Measurable (fun g : GL (Fin 2) F => GL2LocalData.dW2 W' g) := hW'.comp h2.measurable
  exact m3.mul (m2.comp hΦ.measurable)

end GlobalTheory.CompanionTheory.DualHol.IwMeas
