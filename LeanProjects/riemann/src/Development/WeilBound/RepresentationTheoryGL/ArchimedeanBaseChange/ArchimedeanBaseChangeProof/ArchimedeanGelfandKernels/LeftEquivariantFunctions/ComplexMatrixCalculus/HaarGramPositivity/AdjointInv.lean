import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.FrMulK
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.HaarGramPositivity.GramStrictPos

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace

namespace PositivityTheory.RgBcC.CxeAvg

open PositivityTheory.RgTw (Mat)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem lefFr_eq (lam : Fin n → ℤ) (x : Mat n) :
    lefFr n lam x = sqQ lam * (clm lam (fr0 lam x) * Ring.inverse (sqQ lam)) := rfl

theorem sq_inv (hA : Avg) (lam : Fin n → ℤ) :
    sqQ lam * Ring.inverse (sqQ lam) = 1 ∧ Ring.inverse (sqQ lam) * sqQ lam = 1 :=
  ⟨Ring.mul_inverse_cancel _ (hA n lam).1, Ring.inverse_mul_cancel _ (hA n lam).1⟩

theorem adjoint_inv (hA : Avg) (lam : Fin n → ℤ) :
    ContinuousLinearMap.adjoint (Ring.inverse (sqQ (n := n) lam)) = Ring.inverse (sqQ lam) := by
  obtain ⟨h1, _⟩ := sq_inv hA lam
  have hs : star (sqQ (n := n) lam) = sqQ lam := (hA n lam).2.1.star_eq
  rw [← ContinuousLinearMap.star_eq_adjoint]
  have key : star (Ring.inverse (sqQ (n := n) lam)) * star (sqQ lam) = 1 := by
    rw [← star_mul, h1, star_one]
  rw [hs] at key
  calc star (Ring.inverse (sqQ (n := n) lam))
      = star (Ring.inverse (sqQ (n := n) lam)) * (sqQ lam * Ring.inverse (sqQ lam)) := by
        rw [h1, mul_one]
    _ = (star (Ring.inverse (sqQ (n := n) lam)) * sqQ lam) * Ring.inverse (sqQ lam) := by
        rw [mul_assoc]
    _ = Ring.inverse (sqQ lam) := by rw [key, one_mul]

theorem clm_mul' (lam : Fin n → ℤ) (A B : Matrix (Ix n lam) (Ix n lam) ℂ) :
    clm lam (A * B) = clm lam A * clm lam B := by simp only [clm, map_mul]

end PositivityTheory.RgBcC.CxeAvg

namespace PositivityTheory.RgBcC

open PositivityTheory.RgBcC.CxeAvg

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem frOne' (hF : MatrixFrechetDerivativeAtZeroLaws) (hA : Avg) : FrOne := by
  intro n lam
  rw [lefFr_eq, (hF n lam).1]
  simp only [clm, map_one, one_mul]
  exact (sq_inv hA lam).1

theorem frMulK' (hF : MatrixFrechetDerivativeAtZeroLaws) (hA : Avg) : FrMulK := by
  intro n lam k k'
  have h2 := (sq_inv hA lam).2
  rw [CxeAvg.lefFr_eq, CxeAvg.lefFr_eq, CxeAvg.lefFr_eq, Submonoid.coe_mul,
    (hF n lam).2.1 _ _ (Matrix.UnitaryGroup.det_isUnit k) (Matrix.UnitaryGroup.det_isUnit k'),
    clm_mul']
  simp only [mul_assoc]
  rw [← mul_assoc (Ring.inverse (sqQ lam)) (sqQ lam), h2, one_mul]

theorem frIso' (_hF : MatrixFrechetDerivativeAtZeroLaws) (hA : Avg) : FrIso := by
  intro n lam k v
  obtain ⟨h1, h2⟩ := sq_inv hA lam
  have hs : star (sqQ (n := n) lam) = sqQ lam := (hA n lam).2.1.star_eq
  have hr : star (Ring.inverse (sqQ (n := n) lam)) = Ring.inverse (sqQ lam) := by
    rw [ContinuousLinearMap.star_eq_adjoint]; exact adjoint_inv hA lam
  set C := clm lam (fr0 lam (k : Matrix (Fin n) (Fin n) ℂ)) with hCdef
  have hC : star C * gramQ lam * C = gramQ lam := by
    rw [ContinuousLinearMap.star_eq_adjoint]; exact (hA n lam).2.2.2.1 k
  have hg : sqQ lam * sqQ lam = gramQ lam := (hA n lam).2.2.1
  have hTT : star (sqQ lam * (C * Ring.inverse (sqQ lam))) * (sqQ lam * (C * Ring.inverse (sqQ lam))) = 1 := by
    rw [star_mul, star_mul, hs, hr]
    calc Ring.inverse (sqQ lam) * star C * sqQ lam * (sqQ lam * (C * Ring.inverse (sqQ lam)))
        = Ring.inverse (sqQ lam) * (star C * (sqQ lam * sqQ lam) * C) * Ring.inverse (sqQ lam) := by
          simp only [mul_assoc]
      _ = 1 := by
          rw [hg, hC, ← hg, ← mul_assoc (Ring.inverse (sqQ lam)) (sqQ lam) (sqQ lam), h2, one_mul, h1]
  rw [CxeAvg.lefFr_eq]
  set T := sqQ lam * (C * Ring.inverse (sqQ lam)) with hT
  have hin : inner ℂ (T v) (T v) = inner ℂ v v := by
    rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.star_eq_adjoint,
      ← ContinuousLinearMap.mul_apply, hTT, ContinuousLinearMap.one_apply]
  have h3 : ‖T v‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), ← inner_self_eq_norm_sq (𝕜 := ℂ), hin]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h3

theorem frCont' (hF : MatrixFrechetDerivativeAtZeroLaws) (hA : Avg) : FrCont := by
  intro n lam
  simp only [lefFr_eq]
  have h1 : ContinuousOn (fr0 (n := n) lam) (GLs n) := ((hF n lam).2.2).continuousOn
  have h2 : Continuous fun k : UK n => fr0 lam k.1 := h1.comp_continuous continuous_subtype_val mem_GLs
  exact continuous_const.mul (((clm_continuous lam).comp h2).mul continuous_const)

end PositivityTheory.RgBcC
