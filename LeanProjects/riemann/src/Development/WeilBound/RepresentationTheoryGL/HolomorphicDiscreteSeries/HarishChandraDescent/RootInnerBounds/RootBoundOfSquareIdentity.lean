import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.HarishChandraDescent.Descent
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirAlgebra.CasimirKKhwVec

noncomputable section

open Finset
open scoped InnerProductSpace

namespace PositivityTheory.RgHe3.RootBounds

open ReciprocityTheory.ChartRestriction.DS

variable {M : Type} [NormedAddCommGroup M] [InnerProductSpace ℂ M]

theorem norm_sq_eq_re' (x : M) : ‖x‖ ^ 2 = (⟪x, x⟫_ℂ).re := by
  rw [@norm_sq_eq_re_inner ℂ]
  rfl

theorem re_inner_real_smul (r : ℝ) (v : M) : (⟪(r : ℂ) • v, v⟫_ℂ).re = r * ‖v‖ ^ 2 := by
  rw [inner_smul_left, Complex.conj_ofReal, Complex.re_ofReal_mul, ← norm_sq_eq_re']

theorem re_inner_smul_real (r : ℝ) (v : M) : (⟪v, (r : ℂ) • v⟫_ℂ).re = r * ‖v‖ ^ 2 := by
  rw [inner_smul_right, Complex.re_ofReal_mul, ← norm_sq_eq_re']

end PositivityTheory.RgHe3.RootBounds

namespace PositivityTheory.RgHe3

open ReciprocityTheory.ChartRestriction.DS RootBounds

theorem root_bound_of_square_identity : SqId → RootBd := by
  intro hsq
  unfold SqId ForAlg at hsq
  unfold RootBd ForAlg
  intro n ε M _ _ E hG hU Λ c v hv hc a b hab
  obtain ⟨_, h2, _⟩ := hsq n ε M E hG hU v
  have hK : casimirK ε E v = ((casValK ε Λ : ℝ) : ℂ) • v := casimirK_khwVec ε hG hv
  rw [hK, hc, re_inner_real_smul, re_inner_real_smul] at h2
  have hnn : ∀ x : M, 0 ≤ ‖x‖ ^ 2 := fun x => sq_nonneg _
  have hv2 := hnn v
  by_cases he : ε b = ε a
  · rcases lt_or_gt_of_ne hab with hlt | hlt
    · rw [hv.2 a b hlt he.symm, norm_zero]
      have : 0 ≤ |Λ a - Λ b| + |casValK ε Λ - c| := by positivity
      rw [zero_pow two_ne_zero]
      exact mul_nonneg this hv2
    · have hba : E b a v = 0 := hv.2 b a hlt he
      have hcomm : E b a (E a b v) = ((Λ b - Λ a : ℝ) : ℂ) • v := by
        have h := congrArg (fun T : Module.End ℂ M => T v) (hG b a a b)
        simp only [LinearMap.sub_apply, Module.End.mul_apply, hba, map_zero, sub_zero,
          ↓reduceIte] at h
        rw [h, hv.1 b, hv.1 a, ← sub_smul, Complex.ofReal_sub]
      have hs : adjSign ε a b = 1 := by simp [adjSign, he.symm]
      have key : ‖E a b v‖ ^ 2 = (Λ b - Λ a) * ‖v‖ ^ 2 := by
        rw [norm_sq_eq_re', hU a b, hs, one_mul, hcomm, re_inner_smul_real]
      rw [key]
      apply mul_le_mul_of_nonneg_right _ hv2
      calc Λ b - Λ a ≤ |Λ a - Λ b| := by rw [abs_sub_comm]; exact le_abs_self _
        _ ≤ _ := le_add_of_nonneg_right (abs_nonneg _)
  · have hle : ‖E a b v‖ ^ 2 ≤ ∑ a' : Fin n, ∑ b' : Fin n with ε b' ≠ ε a', ‖E a' b' v‖ ^ 2 := by
      calc ‖E a b v‖ ^ 2 ≤ ∑ b' : Fin n with ε b' ≠ ε a, ‖E a b' v‖ ^ 2 :=
            Finset.single_le_sum (f := fun b' => ‖E a b' v‖ ^ 2) (fun _ _ => hnn _)
              (by simp [he])
        _ ≤ _ := Finset.single_le_sum
              (f := fun a' => ∑ b' : Fin n with ε b' ≠ ε a', ‖E a' b' v‖ ^ 2)
              (fun _ _ => Finset.sum_nonneg fun _ _ => hnn _) (Finset.mem_univ a)
    rw [← h2, ← sub_mul] at hle
    exact hle.trans (mul_le_mul_of_nonneg_right
      ((le_abs_self _).trans (le_add_of_nonneg_left (abs_nonneg _))) hv2)

end PositivityTheory.RgHe3
