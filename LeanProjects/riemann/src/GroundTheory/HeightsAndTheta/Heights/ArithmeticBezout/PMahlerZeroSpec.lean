import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsMahler
set_option maxSynthPendingDepth 1

open MeasureTheory MvPolynomial

namespace GroundTheory.Heights₂.Heights

theorem eval_specFirst_zero {n : ℕ} (f : MvPolynomial (Fin 1 × Fin n) ℂ) (u : Fin n → ℂ)
    (v : Fin 0 × Fin n → ℂ) : eval v (specFirst f u) = eval (fun ij => u ij.2) f := by
  unfold specFirst
  show eval₂Hom (RingHom.id ℂ) v (bind₁ (specFirstVar u) f) = eval₂Hom (RingHom.id ℂ) _ f
  rw [eval₂Hom_bind₁]
  congr 2
  funext ij
  obtain ⟨i, j⟩ := ij
  obtain rfl : i = 0 := Fin.fin_one_eq_zero i
  simp [specFirstVar]

theorem MahlerZeroSpec.proof : MahlerZeroSpec.Statement := by
  intro n h f u
  have hS : {v : Fin 0 × Fin n → ℂ | ∀ i : Fin 0, h.norm (fun j => v (i, j)) < 1} = Set.univ := by
    ext v; simp
  unfold mahler sphereMean
  rw [hS]
  simp_rw [eval_specFirst_zero]
  have h1 : (volume : Measure (Fin 0 × Fin n → ℂ)) Set.univ = 1 := by
    rw [volume_pi]; exact Measure.pi_empty_univ _
  exact setAverage_const (by simp [h1]) (by simp [h1]) _

end GroundTheory.Heights₂.Heights
