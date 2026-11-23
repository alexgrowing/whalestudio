import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.AdelicGaussians.UpperRightUnipotentInvariance
import GroundTheory.AutomorphicForms.ReductionFinite
import GroundTheory.AutomorphicForms.ReductionMahler
import GroundTheory.AutomorphicForms.ReductionSiegel

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.GA
open scoped NumberField.AdeleRing

namespace GlobalTheory.CompanionTheory.GAMajInj

theorem exists_nx_mul (g g' : GL (Fin 2) ℚ)
    (h0 : (g : Matrix (Fin 2) (Fin 2) ℚ) 1 0 = (g' : Matrix (Fin 2) (Fin 2) ℚ) 1 0)
    (h1 : (g : Matrix (Fin 2) (Fin 2) ℚ) 1 1 = (g' : Matrix (Fin 2) (Fin 2) ℚ) 1 1)
    (hd : (g : Matrix (Fin 2) (Fin 2) ℚ).det = (g' : Matrix (Fin 2) (Fin 2) ℚ).det) :
    ∃ x : ℚ, nx (Multiplicative.ofAdd x) * g = g' := by
  have hne : (g : Matrix (Fin 2) (Fin 2) ℚ).det ≠ 0 := (Matrix.isUnits_det_units g).ne_zero
  rw [Matrix.det_fin_two] at hne
  rw [Matrix.det_fin_two, Matrix.det_fin_two] at hd
  obtain ⟨x, hx0, hx1⟩ : ∃ x : ℚ,
      (g' : Matrix (Fin 2) (Fin 2) ℚ) 0 0 = (g : Matrix (Fin 2) (Fin 2) ℚ) 0 0 +
        x * (g : Matrix (Fin 2) (Fin 2) ℚ) 1 0 ∧
      (g' : Matrix (Fin 2) (Fin 2) ℚ) 0 1 = (g : Matrix (Fin 2) (Fin 2) ℚ) 0 1 +
        x * (g : Matrix (Fin 2) (Fin 2) ℚ) 1 1 := by
    rw [← h0, ← h1] at hd
    generalize (g : Matrix (Fin 2) (Fin 2) ℚ) 0 0 = a at *
    generalize (g : Matrix (Fin 2) (Fin 2) ℚ) 0 1 = b at *
    generalize (g : Matrix (Fin 2) (Fin 2) ℚ) 1 0 = c at *
    generalize (g : Matrix (Fin 2) (Fin 2) ℚ) 1 1 = d at *
    generalize (g' : Matrix (Fin 2) (Fin 2) ℚ) 0 0 = a' at *
    generalize (g' : Matrix (Fin 2) (Fin 2) ℚ) 0 1 = b' at *
    by_cases hdz : d = 0
    · subst hdz
      have hc : c ≠ 0 := by
        rintro rfl
        simp at hne
      refine ⟨(a' - a) / c, by field_simp; ring, ?_⟩
      have : (b' - b) * c = 0 := by linear_combination hd
      have hb : b' - b = 0 := (mul_eq_zero.1 this).resolve_right hc
      linear_combination hb
    · refine ⟨(b' - b) / d, ?_, by field_simp; ring⟩
      field_simp
      linear_combination -hd
  refine ⟨x, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [nx, Matrix.mul_apply, Fin.sum_univ_two, hx0, hx1, h0, h1]

theorem maj_inj : ∀ q q' : Ad3.GA.NQ,
    (q.out : Matrix (Fin 2) (Fin 2) ℚ) 1 0 = (q'.out : Matrix (Fin 2) (Fin 2) ℚ) 1 0 →
    (q.out : Matrix (Fin 2) (Fin 2) ℚ) 1 1 = (q'.out : Matrix (Fin 2) (Fin 2) ℚ) 1 1 →
    (q.out : Matrix (Fin 2) (Fin 2) ℚ).det = (q'.out : Matrix (Fin 2) (Fin 2) ℚ).det → q = q' := by
  intro q q' h0 h1 hd
  obtain ⟨x, hx⟩ := exists_nx_mul q.out q'.out h0 h1 hd
  have hr : (QuotientGroup.rightRel nU) q.out q'.out :=
    QuotientGroup.rightRel_apply.2 ⟨Multiplicative.ofAdd x, eq_mul_inv_of_mul_eq hx⟩
  rw [← Quotient.out_eq q, ← Quotient.out_eq q']
  exact Quotient.sound hr

end GlobalTheory.CompanionTheory.GAMajInj
