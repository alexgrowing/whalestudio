import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Legendre

noncomputable section
open scoped BigOperators ComplexConjugate
open Filter

namespace Formalism.L2.Th1.F

namespace SigmaBasic

lemma differentiable_wFactor (l : ℂ) : Differentiable ℂ (wFactor l) := by
  unfold wFactor
  fun_prop

lemma wFactor_zero_right (l : ℂ) : wFactor l 0 = 1 := by
  simp [wFactor]

lemma wFactor_neg_neg (l z : ℂ) : wFactor (-l) (-z) = wFactor l z := by
  simp only [wFactor, neg_div_neg_eq, neg_sq]

lemma wFactor_eq_zero_iff {l : ℂ} (hl : l ≠ 0) (z : ℂ) : wFactor l z = 0 ↔ z = l := by
  unfold wFactor
  rw [mul_eq_zero, or_iff_left (Complex.exp_ne_zero _), sub_eq_zero, eq_comm, div_eq_one_iff_eq hl]

lemma wFactor_zero_left (z : ℂ) : wFactor 0 z = 1 := by
  simp [wFactor]

lemma differentiable_tprod (h : SigmaProdLU) (L : PeriodPair) :
    Differentiable ℂ (fun z => ∏' l : L.lattice, wFactor (l : ℂ) z) := by
  rw [← differentiableOn_univ]
  refine TendstoLocallyUniformlyOn.differentiableOn (h L) ?_ isOpen_univ
  refine Eventually.of_forall fun s => ?_
  refine Differentiable.differentiableOn ?_
  intro x
  exact DifferentiableAt.fun_finset_prod fun l _ => differentiable_wFactor _ x

end SigmaBasic

open SigmaBasic

theorem sigmaEntire_of (h : SigmaProdLU) : SigmaEntire := by
  intro L
  unfold wSigma
  exact differentiable_id.mul (differentiable_tprod h L)

theorem sigma_odd : SigmaOdd := by
  intro L z
  have hP : ∏' l : L.lattice, wFactor (l : ℂ) (-z) = ∏' l : L.lattice, wFactor (l : ℂ) z := by
    have e := (Equiv.neg L.lattice).tprod_eq (fun l : L.lattice => wFactor (l : ℂ) (-z))
    rw [← e]
    congr 1
    ext l
    simp [wFactor_neg_neg]
  unfold wSigma
  rw [hP]
  ring

theorem sigmaZero_of (h : SigmaSummable) : SigmaZero := by
  intro L z
  unfold wSigma
  constructor
  · intro h0
    rcases mul_eq_zero.mp h0 with hz | hp
    · rw [hz]
      exact zero_mem _
    · by_contra hz
      have hne : ∀ l : L.lattice, wFactor (l : ℂ) z ≠ 0 := by
        intro l hl
        by_cases hl0 : (l : ℂ) = 0
        · rw [hl0, wFactor_zero_left] at hl
          exact one_ne_zero hl
        · rw [wFactor_eq_zero_iff hl0] at hl
          exact hz (by rw [hl]; exact l.2)
      have hs : Summable (fun l : L.lattice => Complex.log (wFactor (l : ℂ) z)) := by
        have := Complex.summable_log_one_add_of_summable (Summable.of_norm (h L z))
        simpa only [add_sub_cancel] using this
      rw [← Complex.cexp_tsum_eq_tprod hne hs] at hp
      exact Complex.exp_ne_zero _ hp
  · intro hz
    by_cases hz0 : z = 0
    · rw [hz0, zero_mul]
    · rw [tprod_of_exists_eq_zero ⟨⟨z, hz⟩, (wFactor_eq_zero_iff hz0 z).mpr rfl⟩, mul_zero]

theorem sigmaDerivZero_of (h : SigmaProdLU) : ∀ L : PeriodPair, deriv (wSigma L) 0 = 1 := by
  intro L
  have hP := differentiable_tprod h L 0
  unfold wSigma
  rw [deriv_fun_mul (by fun_prop) hP]
  simp [wFactor_zero_right]

end Formalism.L2.Th1.F
