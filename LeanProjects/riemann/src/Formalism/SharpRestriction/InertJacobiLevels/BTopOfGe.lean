import Formalism.SharpRestriction.InertJacobiLevels.AsmIface

noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions NumberField

theorem bTopOf_ge {D : D7} (L : SizeData₂ D) (h : L.sc.x ^ L.sc.eps ≤ L.LaG) :
    L.sc.b' + 2 * (D.R.n : ℝ) * L.sc.delta1 * L.sc.x ^ (2 * L.sc.eps) * L.sc.b' / (D.R.k : ℝ) ≤ bTopOf L := by
  have hx : 0 < L.sc.x := lt_trans one_pos L.sc.one_lt_alt
  have hb : 0 ≤ L.sc.b' := by
    unfold Scale.b' Scale.a Scale.b Scale.X'
    positivity
  have hd : 0 ≤ L.sc.delta1 := by
    unfold Scale.delta1
    positivity
  have e4 : L.sc.x ^ (2 * L.sc.eps) = L.sc.x ^ L.sc.eps * L.sc.x ^ L.sc.eps := by rw [two_mul, Real.rpow_add hx]
  have hp : 0 ≤ L.sc.x ^ L.sc.eps := Real.rpow_nonneg hx.le _
  unfold bTopOf
  rw [e4]
  have h1 : L.sc.x ^ L.sc.eps * L.sc.x ^ L.sc.eps ≤ L.sc.x ^ L.sc.eps * L.LaG := mul_le_mul_of_nonneg_left h hp
  have h2 : 2 * (D.R.n : ℝ) * L.sc.delta1 * (L.sc.x ^ L.sc.eps * L.sc.x ^ L.sc.eps) * L.sc.b' / (D.R.k : ℝ) ≤
      2 * (D.R.n : ℝ) * L.sc.delta1 * L.sc.x ^ L.sc.eps * L.LaG * L.sc.b' / (D.R.k : ℝ) := by
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    apply mul_le_mul_of_nonneg_right _ hb
    rw [mul_assoc (2 * (D.R.n : ℝ) * L.sc.delta1) (L.sc.x ^ L.sc.eps) L.LaG]
    exact mul_le_mul_of_nonneg_left h1 (by positivity)
  linarith

def mkSc (eps : ℝ) (h0 : 0 < eps) (h1 : eps < 1 / 52) (x : ℝ) (hx : 1 < x) : Scale := ⟨x, eps, hx, h0, h1, 1, le_rfl⟩

end Formalism.MainNotions.Inhab

end
