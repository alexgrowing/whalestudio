import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.SemiCharBasic
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.QuasiPeriodConstUnique

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.H

section SlopeTestRemainingChoices

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem herm_sub_swap (H : Sesq V) (hH : IsHerm H) (x y : V) :
    H x y - H y x = 2 * Complex.I * (altE H x y : ℂ) := by
  rw [hH x y, Complex.sub_conj, altE]
  push_cast
  ring

theorem altE_swap (H : Sesq V) (hH : IsHerm H) (x y : V) : altE H y x = -altE H x y := by
  simp only [altE, hH x y, Complex.conj_im]

theorem re_swap (H : Sesq V) (hH : IsHerm H) (x y : V) : (H y x).re = (H x y).re := by
  rw [hH x y, Complex.conj_re]

end SlopeTestRemainingChoices

theorem heisenbergMul : OpUMul := by
  intro V _ _ H hH x y F z
  have hs := herm_sub_swap H hH x y
  simp only [opU]
  rw [mul_assoc, ← Complex.exp_add, mul_left_comm, ← Complex.exp_add, add_assoc z x y]
  congr 2
  simp only [map_add, LinearMap.add_apply]
  linear_combination (-(Real.pi : ℂ) / 2) * hs

theorem heisenbergComm : OpUComm := by
  intro V _ _ H hH F z
  refine ⟨by simp [opU], fun x y => ?_⟩
  have h1 := heisenbergMul V H hH x y F z
  have h2 := heisenbergMul V H hH y x F z
  rw [add_comm y x, altE_swap H hH] at h2
  rw [h1, h2, ← mul_assoc, ← Complex.exp_add]
  congr 1
  congr 1
  push_cast
  ring

theorem heisenbergNorm : OpUNorm := by
  intro V _ _ H hH x F z
  have hre := re_swap H hH z x
  have hE : (-(Real.pi : ℂ) * H z x - (Real.pi : ℂ) * H x x / 2).re =
      -Real.pi * (H z x).re - Real.pi * (H x x).re / 2 := by
    simp [Complex.sub_re, Complex.mul_re]
  have hzz : (H (z + x) (z + x)).re = (H z z).re + 2 * (H z x).re + (H x x).re := by
    simp only [map_add, LinearMap.add_apply, Complex.add_re]
    linarith
  simp only [opU, norm_mul, Complex.norm_exp, hE]
  rw [hzz, mul_pow, ← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]
  congr 2
  push_cast
  ring

theorem heisenbergIsometry : OpUIsom := by
  intro V W _ _ _ _ H H' g hg x G z
  simp only [opU, map_add]
  rw [hg z x, hg x x]

theorem precompHeisenberg : PullOpU := by
  intro V _ _ H δ hδ x F z
  have h1 : H z (δ x) = H (δ.symm z) x := by
    have h := hδ (δ.symm z) x
    simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at h
    exact h
  have h2 : H (δ x) (δ x) = H x x := by
    have h := hδ x x
    simpa only [LinearEquiv.coe_coe] using h
  simp only [pullInv, opU, map_add, LinearEquiv.symm_apply_apply, h1, h2]

theorem semicharacterBasic : SemiCharBasic := by
  intro V _ _ H hH Λ α hα
  obtain ⟨hpm, hmul⟩ := hα
  have hA0 : ∀ x, altE H x x = 0 := fun x => Complex.conj_eq_iff_im.mp (hH x x).symm
  have h0 : α 0 = 1 := by
    have h := hmul 0 Λ.zero_mem 0 Λ.zero_mem
    rw [add_zero, hA0, Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one] at h
    rcases hpm 0 Λ.zero_mem with h' | h'
    · exact h'
    · rw [h'] at h; norm_num at h
  have hneg : ∀ x ∈ Λ, α (-x) = α x := by
    intro x hx
    have h := hmul x hx (-x) (Λ.neg_mem hx)
    have hA : altE H x (-x) = 0 := by
      have h' := hA0 x
      simp only [altE] at h' ⊢
      rw [map_neg, Complex.neg_im, h', neg_zero]
    rw [add_neg_cancel, h0, hA, Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one] at h
    rcases hpm x hx with h1 | h1 <;> rcases hpm (-x) (Λ.neg_mem hx) with h2 | h2 <;>
      rw [h1, h2] at h ⊢ <;> try norm_num at h
  have hdual : Λ ≤ dualLat H Λ := by
    intro x hx
    show ∀ y ∈ Λ, ∃ m : ℤ, altE H x y = (m : ℝ)
    intro y hy
    have e1 := hmul x hx y hy
    have e2 := hmul y hy x hx
    rw [add_comm y x, altE_swap H hH] at e2
    have hxne : α x ≠ 0 := by rcases hpm x hx with h | h <;> rw [h] <;> norm_num
    have hyne : α y ≠ 0 := by rcases hpm y hy with h | h <;> rw [h] <;> norm_num
    have he : Complex.exp ((Real.pi : ℂ) * Complex.I * (altE H x y : ℂ)) =
        Complex.exp ((Real.pi : ℂ) * Complex.I * ((-altE H x y : ℝ) : ℂ)) := by
      have h := e1.symm.trans e2
      rw [mul_comm (α y) (α x)] at h
      exact mul_left_cancel₀ (mul_ne_zero hxne hyne) h
    rw [Complex.exp_eq_exp_iff_exists_int] at he
    obtain ⟨n, hn⟩ := he
    refine ⟨n, ?_⟩
    have hpi : (Real.pi : ℂ) * Complex.I ≠ 0 :=
      mul_ne_zero (by exact_mod_cast Real.pi_ne_zero) Complex.I_ne_zero
    push_cast at hn
    have h' : ((altE H x y : ℝ) : ℂ) = (n : ℂ) := by
      apply mul_left_cancel₀ (mul_ne_zero (two_ne_zero' ℂ) hpi)
      linear_combination hn
    exact_mod_cast h'
  exact ⟨h0, hneg, hdual⟩

theorem semicharacterHom : SemiHom := by
  intro V _ _ H hH Λ α hα x hx y hy F z
  have hU : opU H x (fun v => α y * opU H y F v) z = α y * opU H x (opU H y F) z := by
    simp only [opU]; ring
  have hd : x ∈ dualLat H Λ := (semicharacterBasic V H hH Λ α hα).2.2 hx
  obtain ⟨m, hm⟩ := (show ∀ y ∈ Λ, ∃ m : ℤ, altE H x y = (m : ℝ) from hd) y hy
  have hexp : Complex.exp (-(Real.pi : ℂ) * Complex.I * (altE H x y : ℂ)) =
      Complex.exp ((Real.pi : ℂ) * Complex.I * (altE H x y : ℂ)) := by
    rw [Complex.exp_eq_exp_iff_exists_int]
    refine ⟨-m, ?_⟩
    rw [hm]
    push_cast
    ring
  rw [hU, heisenbergMul V H hH x y F z, hα.2 x hx y hy, hexp]
  ring

theorem heisenbergAnalytic : OpUAnalytic := by
  intro V _ _ _ H x F hF z _
  let L : V →ₗ[ℂ] ℂ :=
    { toFun := fun v => H v x
      map_add' := fun a b => by simp only [map_add, LinearMap.add_apply]
      map_smul' := fun c a => by simp only [map_smul, LinearMap.smul_apply, RingHom.id_apply] }
  have hlin : AnalyticAt ℂ (fun v => H v x) z := (LinearMap.toContinuousLinearMap L).analyticAt z
  have hF' : AnalyticAt ℂ (fun v => F (v + x)) z :=
    AnalyticAt.comp (x := z) (f := fun v => v + x) (hF (z + x) (Set.mem_univ _))
      (analyticAt_id.add analyticAt_const)
  have hE : AnalyticAt ℂ
      (fun v => Complex.exp (-(Real.pi : ℂ) * H v x - (Real.pi : ℂ) * H x x / 2)) z :=
    ((analyticAt_const.mul hlin).sub analyticAt_const).cexp
  exact hF'.mul hE

theorem matH_apply {n : Type*} [Fintype n] (h : Matrix n n ℂ) (z w : n → ℂ) :
    matH h z w = ∑ i, ∑ j, z i * h i j * conj (w j) := rfl

theorem matrixFormBasic : MatHBasic := by
  intro n _ h
  refine ⟨fun z w => rfl, fun hh x y => ?_⟩
  rw [matH_apply, matH_apply, map_sum]
  simp_rw [map_sum, map_mul, Complex.conj_conj]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have hc : conj (h i j) = h j i := by
    have h' := congrFun (congrFun hh j) i
    simpa [Matrix.conjTranspose_apply] using h'
  rw [hc]
  ring

theorem stdH_apply (L : PeriodPair) (n : Type*) [Fintype n] [DecidableEq n] (z w : n → ℂ) :
    stdH L n z w = ∑ i, Formalism.L2.Th1.F.herm L (z i) (w i) := by
  rw [stdH, matH_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i (fun j _ hj => by simp [Matrix.one_apply, Ne.symm hj]) (by simp)]
  simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one, Formalism.L2.Th1.F.herm]
  ring

theorem standardFormBasic : StdHBasic := by
  intro L n _ _
  have harea := Formalism.L2.Th1.F.PeriodAreaSignLemmas.area_pos L
  refine ⟨stdH_apply L n, fun x y => ?_, fun x hx => ?_⟩
  · rw [stdH_apply, stdH_apply, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Formalism.L2.Th1.F.herm, map_div₀, map_mul, Complex.conj_conj, Complex.conj_ofReal]
    ring
  · have hi : ∀ i, Formalism.L2.Th1.F.herm L (x i) (x i) =
        ((Complex.normSq (x i) / Formalism.L2.Th1.F.area L : ℝ) : ℂ) := by
      intro i
      simp only [Formalism.L2.Th1.F.herm, Complex.mul_conj]
      push_cast
      ring
    rw [stdH_apply, Complex.re_sum]
    simp only [hi, Complex.ofReal_re]
    obtain ⟨i, hi0⟩ : ∃ i, x i ≠ 0 := by
      by_contra h
      push_neg at h
      exact hx (funext h)
    exact Finset.sum_pos' (fun j _ => div_nonneg (Complex.normSq_nonneg _) harea.le)
      ⟨i, Finset.mem_univ _, div_pos (Complex.normSq_pos.mpr hi0) harea⟩

theorem heisenbergStandard : OpUStd := by
  intro L n _ _ x f z
  simp only [opU, Formalism.L2.Th1.F.opU, prodFn, stdH_apply, Pi.add_apply]
  rw [Finset.prod_mul_distrib, ← Complex.exp_sum, Finset.mul_sum, Finset.mul_sum, Finset.sum_div,
    ← Finset.sum_sub_distrib]

theorem matrixForm_fourfoldBlock {n : Type*} [Fintype n] (h : Matrix n n ℂ) (z w : Fin 4 × n → ℂ) :
    matH (blk4 h) z w = ∑ a, matH h (slice a z) (slice a w) := by
  simp only [matH_apply, slice, blk4, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single a (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
  simp

theorem heisenbergFourfold : OpUBlk4 := by
  intro n _ h
  refine ⟨matrixForm_fourfoldBlock h, fun x θ z => ?_⟩
  simp only [opU, matrixForm_fourfoldBlock]
  rw [Finset.prod_mul_distrib, ← Complex.exp_sum, Finset.mul_sum, Finset.mul_sum, Finset.sum_div,
    ← Finset.sum_sub_distrib]
  rfl

end Formalism.L2.Th1.H
