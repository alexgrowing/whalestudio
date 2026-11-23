import Mathlib
import Formalism.PeriodIntegrals.UnitaryDense

open Matrix MvPolynomial
open scoped ComplexOrder

namespace PI.UnitaryDenseWork

noncomputable def detPoly {ι : Type} (n : ℕ) (τ : ι) : MvPolynomial (ι × Fin n × Fin n) ℂ :=
  Matrix.det (Matrix.of fun i j : Fin n => (X (τ, i, j) : MvPolynomial (ι × Fin n × Fin n) ℂ))

lemma det_ne_zero_of_frame {n : ℕ} (G y : Matrix (Fin n) (Fin n) ℂ) (hy : yᴴ * G * y = 1) :
    y.det ≠ 0 := by
  intro h0
  have := congrArg Matrix.det hy
  rw [det_mul, det_mul, det_one, h0, mul_zero] at this
  exact zero_ne_one this

end PI.UnitaryDenseWork

open PI.UnitaryDenseWork

theorem unitaryDense_of (h : PI.FramesDense) : PI.UnitaryDense := by
  intro n P hP
  let e : Unit × Fin n × Fin n ≃ Fin n × Fin n := Equiv.punitProd _
  have hR : rename e.symm P = 0 := by
    refine h Unit n (fun _ => 1) (fun _ => Matrix.PosDef.one) (rename e.symm P) ?_
    intro y hy
    rw [eval_rename]
    have h1 := hP (y ()) (by simpa using hy ())
    exact h1
  exact rename_injective _ e.symm.injective (by rw [hR, map_zero])
