import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitDetOfIsOrth
open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.TorusFrame
open scoped ENNReal

namespace GlobalTheory.TorusAngles

theorem exp_I_arg {w : ℂ} (hw : ‖w‖ = 1) : Complex.exp (Complex.I * (Complex.arg w : ℂ)) = w := by
  have h := Complex.norm_mul_exp_arg_mul_I w
  rw [hw] at h
  simpa [mul_comm] using h

theorem exp_neg_I_arg {w : ℂ} (hw : ‖w‖ = 1) : Complex.exp (-(Complex.I * (Complex.arg w : ℂ))) = w⁻¹ := by
  rw [Complex.exp_neg, exp_I_arg hw]

theorem exists_angles_of_prod_eq_one : ∀ (r : ℕ) (z : Fin r → ℂ), (∀ a, ‖z a‖ = 1) → ∏ a, z a = 1 →
    ∃ φ : Fin (r - 1) → ℝ, ∀ a, Complex.exp (Complex.I * (angles φ a : ℂ)) = z a := by
  intro r z hz hp
  rcases r with _ | n
  · exact ⟨fun _ => 0, fun a => a.elim0⟩
  · refine ⟨fun k => Complex.arg (z ⟨k, by omega⟩), fun a => ?_⟩
    unfold angles
    split_ifs with h
    · exact exp_I_arg (hz _)
    · have ha : a = Fin.last n := by ext; simp at h ⊢; omega
      subst ha
      rw [Fin.prod_univ_castSucc] at hp
      have hlast : z (Fin.last n) = (∏ k : Fin n, z k.castSucc)⁻¹ := by
        exact eq_inv_of_mul_eq_one_right hp
      rw [hlast, Complex.ofReal_neg, Complex.ofReal_sum, mul_neg, Finset.mul_sum, ← Finset.sum_neg_distrib,
        Complex.exp_sum, ← Finset.prod_inv_distrib]
      show ∏ k : Fin n, Complex.exp (-(Complex.I * (Complex.arg (z ⟨k, _⟩) : ℂ))) = _
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [exp_neg_I_arg (hz _)]
      rfl

end GlobalTheory.TorusAngles
