import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockRaisingLowering.FockInnerEqSumRight
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockDegreeOne.OneDegOfHalves

noncomputable section

open MvPolynomial FockH1Action FockRaiseLowInner

namespace PI.FockOneDegW.Inner

export FockRaiseLowInner (fockInner_X_mul fockInner_mul_X fockInner_sum_left fockInner_sum_right
  fockInner_swap fockInner_zero_left fockInner_zero_right fockInner_add_left fockInner_add_right
  fockInner_smul_left fockInner_smul_right fockInner_neg_left fockInner_neg_right fockInner_sub_right
  fockInner_eq_support wt)

section Pos

variable {σ : Type*}

def wtN (α : σ →₀ ℕ) : ℕ := α.prod (fun _ k => k.factorial)

theorem wtN_pos (α : σ →₀ ℕ) : 0 < wtN α := by
  unfold wtN Finsupp.prod
  exact Finset.prod_pos fun i _ ↦ Nat.factorial_pos _

theorem wt_eq_wtN (α : σ →₀ ℕ) : wt α = (wtN α : ℂ) := by
  simp only [wt, wtN, Finsupp.prod, Nat.cast_prod]

theorem fockInner_self_eq (F : MvPolynomial σ ℂ) :
    fockInner F F = ((∑ α ∈ F.support, Complex.normSq (coeff α F) * (wtN α : ℝ) : ℝ) : ℂ) := by
  rw [fockInner_eq_support, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun α _ ↦ ?_
  rw [Complex.ofReal_mul, Complex.normSq_eq_conj_mul_self, Complex.ofReal_natCast, wt_eq_wtN]

theorem fockInner_self_re_nonneg (F : MvPolynomial σ ℂ) : 0 ≤ (fockInner F F).re := by
  rw [fockInner_self_eq, Complex.ofReal_re]
  exact Finset.sum_nonneg fun α _ ↦ mul_nonneg (Complex.normSq_nonneg _) (Nat.cast_nonneg _)

theorem fockInner_self_im (F : MvPolynomial σ ℂ) : (fockInner F F).im = 0 := by
  rw [fockInner_self_eq, Complex.ofReal_im]

theorem eq_zero_of_fockInner_self_re (F : MvPolynomial σ ℂ) (h : (fockInner F F).re = 0) :
    F = 0 := by
  rw [fockInner_self_eq, Complex.ofReal_re] at h
  have hall := (Finset.sum_eq_zero_iff_of_nonneg
    (fun α _ ↦ mul_nonneg (Complex.normSq_nonneg (coeff α F)) (Nat.cast_nonneg (wtN α)))).1 h
  by_contra hF
  obtain ⟨α, hα⟩ := Finset.nonempty_of_ne_empty (mt MvPolynomial.support_eq_empty.1 hF)
  have hc : coeff α F ≠ 0 := MvPolynomial.mem_support_iff.1 hα
  have hne : Complex.normSq (coeff α F) * (wtN α : ℝ) ≠ 0 :=
    mul_ne_zero (Complex.normSq_pos.2 hc).ne' (by exact_mod_cast (wtN_pos α).ne')
  exact hne (hall α hα)

end Pos

end PI.FockOneDegW.Inner

namespace PI.FockOneDegW

open PI.FockOneDegW.Inner in
theorem fock_inner_facts : InnerFacts := by
  intro σ P Q Q' c
  refine ⟨fockInner_add_right _ _ _, fockInner_smul_right _ _ _, fockInner_swap _ _,
    ⟨fockInner_self_im _, fockInner_self_re_nonneg _⟩, fun h ↦ ?_, fun l ↦ fockInner_X_mul l P Q⟩
  exact eq_zero_of_fockInner_self_re P (by rw [h]; simp)

end PI.FockOneDegW
