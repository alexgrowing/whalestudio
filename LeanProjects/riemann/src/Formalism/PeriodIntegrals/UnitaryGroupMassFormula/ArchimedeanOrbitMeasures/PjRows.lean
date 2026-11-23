import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.NormInvSqrtTwoSq

noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Matrix

variable {n k m : ℕ} (S : Finset (Fin n)) (eS : Fin k ≃ {i // i ∈ S}) (eU : Fin m ≃ {i // i ∉ S})

def rowsM (X : Matrix (Fin k) (Fin m) ℂ) (Y : Matrix (Fin m) (Fin m) ℂ) : Matrix (Fin n) (Fin m) ℂ :=
  fun i j => if hi : i ∈ S then X (eS.symm ⟨i, hi⟩) j else Y (eU.symm ⟨i, hi⟩) j

theorem rowsM_S (X Y) (a : Fin k) (j) : rowsM S eS eU X Y (eS a) j = X a j := by
  simp [rowsM]

theorem rowsM_U (X Y) (a : Fin m) (j) : rowsM S eS eU X Y (eU a) j = Y a j := by
  simp [rowsM, (eU a).2]

theorem rows_ext {p : Type} (X Y : Matrix (Fin n) p ℂ) (h1 : ∀ a j, X (eS a) j = Y (eS a) j)
    (h2 : ∀ a j, X (eU a) j = Y (eU a) j) : X = Y := by
  ext i j
  by_cases hi : i ∈ S
  · simpa using h1 (eS.symm ⟨i, hi⟩) j
  · simpa using h2 (eU.symm ⟨i, hi⟩) j

theorem of_cpx_reim {a b : ℕ} (X : Matrix (Fin a) (Fin b) ℂ) : Matrix.of (cpx (reim X)) = X := by
  ext a b
  simp [cpx_reim]

def rsL : EuclideanSpace ℝ (Fin k × Fin m × Bool) × EuclideanSpace ℝ (Fin m × Fin m × Bool) →ₗ[ℝ]
    EuclideanSpace ℝ (Fin n × Fin m × Bool) where
  toFun z := reim (rowsM S eS eU (Matrix.of (cpx z.1)) (Matrix.of (cpx z.2)))
  map_add' a b := by
    ext p
    rcases p with ⟨i, j, c⟩
    by_cases hi : i ∈ S <;> cases c <;> simp [reim, rowsM, hi, cpx]
  map_smul' r z := by
    ext p
    rcases p with ⟨i, j, c⟩
    by_cases hi : i ∈ S <;> cases c <;> simp [reim, rowsM, hi, cpx]

theorem rsL_apply (z) : rsL S eS eU z = reim (rowsM S eS eU (Matrix.of (cpx z.1)) (Matrix.of (cpx z.2))) := rfl

theorem rs_mp : MeasurePreserving (rsL S eS eU) volume volume := by
  apply mp_of_isom_prod
  · intro a b
    rw [rsL_apply, norm_reim_sq, sum_split S eS eU, norm_cpx_sq a, norm_cpx_sq b]
    simp [rowsM_S, rowsM_U]
  · intro y
    obtain ⟨Y, rfl⟩ := reim_surj y
    refine ⟨(reim (Matrix.of fun a j => Y (eS a) j), reim (Matrix.of fun a j => Y (eU a) j)), ?_⟩
    rw [rsL_apply, of_cpx_reim, of_cpx_reim]
    congr 1
    apply rows_ext S eS eU
    · intro a j
      rw [rowsM_S]
      rfl
    · intro a j
      rw [rowsM_U]
      rfl

end PI.AprimeInfW
