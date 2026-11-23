import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.GaussDegenerate
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.MatrixFormFourfoldBlock
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.GaussSumEighthPower

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.H

namespace SemicharacterExponentialLemmas

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem altE_add_left (H : Sesq V) (x y z : V) : altE H (x + y) z = altE H x z + altE H y z := by
  simp only [altE, map_add, LinearMap.add_apply, Complex.add_im]

theorem altE_add_right (H : Sesq V) (x y z : V) : altE H x (y + z) = altE H x y + altE H x z := by
  simp only [altE, map_add, Complex.add_im]

theorem altE_neg_right (H : Sesq V) (x y : V) : altE H x (-y) = -altE H x y := by
  simp only [altE, map_neg, Complex.neg_im]

theorem altE_self (H : Sesq V) (hH : IsHerm H) (x : V) : altE H x x = 0 := by
  have h := congrArg Complex.im (hH x x)
  rw [Complex.conj_im] at h
  simp only [altE]
  linarith

theorem altE_nsmul_left (H : Sesq V) (k : ℕ) (x y : V) : altE H (k • x) y = k * altE H x y := by
  simp [altE, map_nsmul, nsmul_eq_mul]

theorem altE_nsmul_right (H : Sesq V) (k : ℕ) (x y : V) : altE H x (k • y) = k * altE H x y := by
  simp [altE, map_nsmul, nsmul_eq_mul]

theorem exp_eq_of_int {a c : ℂ} (n : ℤ) (h : a = c + (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) :
    Complex.exp a = Complex.exp c := by
  rw [h, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem semi_sq {H : Sesq V} {Λ : AddSubgroup V} {α : V → ℂ} (hα : IsSemiChar H Λ α) {x : V}
    (hx : x ∈ Λ) : α x * α x = 1 := by
  rcases hα.1 x hx with h | h <;> rw [h] <;> norm_num

theorem semi_norm {H : Sesq V} {Λ : AddSubgroup V} {α : V → ℂ} (hα : IsSemiChar H Λ α) {x : V}
    (hx : x ∈ Λ) : ‖α x‖ = 1 := by
  rcases hα.1 x hx with h | h <;> rw [h] <;> simp

theorem semi_nsmul {H : Sesq V} (hH : IsHerm H) {Λ : AddSubgroup V} {α : V → ℂ}
    (hα : IsSemiChar H Λ α) {x : V} (hx : x ∈ Λ) (k : ℕ) : α (k • x) = α x ^ (k ^ 2) := by
  have hs : α x ^ 2 = 1 := by rw [sq]; exact semi_sq hα hx
  induction k with
  | zero =>
    have h1 := hα.2 0 Λ.zero_mem 0 Λ.zero_mem
    have h2 := semi_sq hα Λ.zero_mem
    simp only [add_zero, altE, map_zero, LinearMap.zero_apply, Complex.zero_im, Complex.ofReal_zero,
      mul_zero, Complex.exp_zero, mul_one] at h1
    rw [zero_nsmul]
    calc α 0 = α 0 * α 0 := h1
      _ = 1 := h2
      _ = α x ^ (0 ^ 2) := by simp
  | succ k ih =>
    have hk : k • x ∈ Λ := Λ.nsmul_mem hx k
    have e := hα.2 (k • x) hk x hx
    have hz : altE H (k • x) x = 0 := by rw [altE_nsmul_left, altE_self H hH, mul_zero]
    rw [succ_nsmul, e, hz, ih]
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one]
    have hk2 : (k + 1) ^ 2 = k ^ 2 + 2 * k + 1 := by ring
    rw [hk2, pow_add, pow_add, pow_mul, hs, one_pow, mul_one, pow_one]

end SemicharacterExponentialLemmas

open SemicharacterExponentialLemmas

theorem triplePhaseQuadratic : PsiQuadratic := by
  intro V _ _ H α Λ₁ Λ₂ Λ₃ hT
  have hH := hT.herm
  have int₁ := (semicharacterBasic V H hH Λ₁ α hT.sc₁).2.2
  have int₂ := (semicharacterBasic V H hH Λ₂ α hT.sc₂).2.2
  have int₃ := (semicharacterBasic V H hH Λ₃ α hT.sc₃).2.2
  have hadd : ∀ z ∈ Λ₃, ∀ y ∈ Λ₂, z + y ∈ Λ₁ → ∀ z' ∈ Λ₃, ∀ y' ∈ Λ₂, z' + y' ∈ Λ₁ →
      psiT H α (z + z') (y + y') = psiT H α z y * psiT H α z' y'
        * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (altE H y z' : ℂ)) := by
    intro z hz y hy hzy z' hz' y' hy' hzy'
    obtain ⟨m, hm⟩ := int₃ hz z' hz'
    obtain ⟨k, hk⟩ := int₂ hy y' hy'
    have hsw := altE_swap H hH y z'
    simp only [psiT]
    rw [show z + z' + (y + y') = (z + y) + (z' + y') by abel, hT.sc₃.2 z hz z' hz',
      hT.sc₂.2 y hy y' hy', hT.sc₁.2 _ hzy _ hzy']
    have key : Complex.exp ((Real.pi : ℂ) * Complex.I * (altE H z z' : ℂ))
        * Complex.exp ((Real.pi : ℂ) * Complex.I * (altE H y y' : ℂ))
        * Complex.exp ((Real.pi : ℂ) * Complex.I * (altE H (z + y) (z' + y') : ℂ))
        * Complex.exp (-(Real.pi : ℂ) * Complex.I * (altE H (z + z') (y + y') : ℂ))
        = Complex.exp (-(Real.pi : ℂ) * Complex.I * (altE H z y : ℂ))
        * Complex.exp (-(Real.pi : ℂ) * Complex.I * (altE H z' y' : ℂ))
        * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (altE H y z' : ℂ)) := by
      simp only [← Complex.exp_add]
      apply exp_eq_of_int (m + k)
      simp only [altE_add_left, altE_add_right, hsw, hm, hk]
      push_cast
      ring
    linear_combination (α z * α z' * α y * α y' * α (z + y) * α (z' + y')) * key
  refine ⟨hadd, ?_, ?_, ?_⟩
  · intro z hz y hy hzy k
    simp only [psiT]
    rw [← smul_add, semi_nsmul hH hT.sc₃ hz, semi_nsmul hH hT.sc₂ hy, semi_nsmul hH hT.sc₁ hzy,
      altE_nsmul_left, altE_nsmul_right, mul_pow, mul_pow, mul_pow, ← Complex.exp_nat_mul]
    congr 2
    push_cast
    ring
  · intro z hz y hy hzy
    simp only [psiT]
    rw [norm_mul, norm_mul, norm_mul, semi_norm hT.sc₃ hz, semi_norm hT.sc₂ hy,
      semi_norm hT.sc₁ hzy,
      show -(Real.pi : ℂ) * Complex.I * (altE H z y : ℂ)
        = ((-Real.pi * altE H z y : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I]
    norm_num
  · intro z hz y hy hzy u' hu' u hu t ht
    have hz' : u' + t ∈ Λ₃ := Λ₃.add_mem hu'.2 ht.2
    have hy' : u - t ∈ Λ₂ := Λ₂.sub_mem hu.2 ht.1
    have hzy' : u' + t + (u - t) ∈ Λ₁ := by
      rw [show u' + t + (u - t) = u' + u by abel]
      exact Λ₁.add_mem hu'.1 hu.1
    rw [show z + u' + t = z + (u' + t) by abel, show y + u - t = y + (u - t) by abel,
      hadd z hz y hy hzy _ hz' _ hy' hzy']
    have h1 : psiT H α (u' + t) (u - t) = 1 := by
      obtain ⟨m, hm⟩ := int₃ hu'.2 t ht.2
      have hsw := altE_swap H hH u t
      have hneg := (semicharacterBasic V H hH Λ₂ α hT.sc₂).2.1 t ht.1
      simp only [psiT]
      rw [show u' + t + (u - t) = u' + u by abel, sub_eq_add_neg, hT.sc₃.2 u' hu'.2 t ht.2,
        hT.sc₂.2 u hu.2 (-t) (Λ₂.neg_mem ht.1), hT.sc₁.2 u' hu'.1 u hu.1, hneg]
      have key : Complex.exp ((Real.pi : ℂ) * Complex.I * (altE H u' t : ℂ))
          * Complex.exp ((Real.pi : ℂ) * Complex.I * (altE H u (-t) : ℂ))
          * Complex.exp ((Real.pi : ℂ) * Complex.I * (altE H u' u : ℂ))
          * Complex.exp (-(Real.pi : ℂ) * Complex.I * (altE H (u' + t) (u + -t) : ℂ)) = 1 := by
        simp only [← Complex.exp_add]
        rw [← Complex.exp_zero]
        apply exp_eq_of_int m
        simp only [altE_add_left, altE_add_right, altE_neg_right, hsw, hm, altE_self H hH t]
        push_cast
        ring
      have a1 := semi_sq hT.sc₁ hu'.1
      have a2 := semi_sq hT.sc₂ hu.2
      have a3 := semi_sq hT.sc₂ ht.1
      calc _ = (α u' * α u') * (α u * α u) * (α t * α t)
            * (Complex.exp ((Real.pi : ℂ) * Complex.I * (altE H u' t : ℂ))
          * Complex.exp ((Real.pi : ℂ) * Complex.I * (altE H u (-t) : ℂ))
          * Complex.exp ((Real.pi : ℂ) * Complex.I * (altE H u' u : ℂ))
          * Complex.exp (-(Real.pi : ℂ) * Complex.I * (altE H (u' + t) (u + -t) : ℂ))) := by ring
        _ = 1 := by rw [key, a1, a2, a3]; norm_num
    have h2 : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (altE H y (u' + t) : ℂ)) = 1 := by
      obtain ⟨m, hm⟩ := int₂ hy t ht.1
      obtain ⟨k, hk⟩ := int₁ hzy u' hu'.1
      obtain ⟨l, hl⟩ := int₃ hz u' hu'.2
      rw [altE_add_left] at hk
      have hyu : altE H y u' = (k : ℝ) - (l : ℝ) := by linarith
      rw [← Complex.exp_zero]
      apply exp_eq_of_int (k - l + m)
      rw [altE_add_right, hyu, hm]
      push_cast
      ring
    rw [h1, h2, mul_one, mul_one]

namespace IsQuadFn0

variable {M : Type*} [AddCommGroup M] {φ : M → ℂ} {b : M → M → ℂ}

theorem b_eq (h : IsQuadFn0 φ b) (x y : M) : b x y = φ (x + y) / (φ x * φ y) := by
  rw [h.1 x y, eq_div_iff (mul_ne_zero (h.4 x) (h.4 y))]
  ring

theorem symm (h : IsQuadFn0 φ b) (x y : M) : b x y = b y x := by
  rw [h.b_eq x y, h.b_eq y x, add_comm y x, mul_comm (φ y)]

theorem b_zero_left (h : IsQuadFn0 φ b) (y : M) : b 0 y = 1 := by
  have h0 : φ 0 = 1 := by simpa using h.3 0 y
  rw [h.b_eq, zero_add, h0, one_mul, div_self (h.4 y)]

theorem b_neg_left (h : IsQuadFn0 φ b) (x y : M) : b (-x) y = (b x y)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← h.2]
  simp [h.b_zero_left]

def rad (h : IsQuadFn0 φ b) : AddSubgroup M where
  carrier := {x | ∀ y, b x y = 1}
  zero_mem' := h.b_zero_left
  add_mem' := by
    intro x x' hx hx' y
    rw [h.left, hx y, hx' y, mul_one]
  neg_mem' := by
    intro x hx y
    rw [h.b_neg_left, hx y, inv_one]

theorem mem_rad (h : IsQuadFn0 φ b) (x : M) : x ∈ h.rad ↔ ∀ y, b x y = 1 := Iff.rfl

theorem phi_rad [Fintype M] (h : IsQuadFn0 φ b) (hS : ∑ x, φ x ≠ 0) {r : M} (hr : r ∈ h.rad) :
    φ r = 1 := by
  have hb : ∀ x, b x r = 1 := fun x => (h.symm x r).trans ((h.mem_rad r).1 hr x)
  have hshift : ∑ x, φ (x + r) = ∑ x, φ x :=
    Fintype.sum_equiv (Equiv.addRight r) (fun x => φ (x + r)) φ (fun x => rfl)
  have hm : ∑ x, φ (x + r) = φ r * ∑ x, φ x := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [h.1, hb, mul_one, mul_comm]
  rw [hshift] at hm
  exact mul_right_cancel₀ hS (hm.symm.trans (one_mul _).symm)

end IsQuadFn0

theorem degenerateGaussSum : GaussDegenerate := by
  classical
  intro M _ _ φ b h hS
  set R : AddSubgroup M := h.rad with hR
  have hφR : ∀ x, ∀ r ∈ R, φ (x + r) = φ x := by
    intro x r hr
    rw [h.add, h.symm, hr x, h.phi_rad hS hr, mul_one, mul_one]
  have hbR : ∀ x y, ∀ r ∈ R, b (x + r) y = b x y := by
    intro x y r hr
    rw [h.left, hr y, mul_one]
  have : Fintype (M ⧸ R) := Fintype.ofFinite _
  have : Fintype R := Fintype.ofFinite _
  let φ' : M ⧸ R → ℂ := fun q => φ q.out
  let b' : M ⧸ R → M ⧸ R → ℂ := fun q q' => b q.out q'.out
  have hφ' : ∀ x : M, φ' (x : M ⧸ R) = φ x := by
    intro x
    obtain ⟨r, hr⟩ := QuotientAddGroup.mk_out_eq_add R x
    change φ (Quotient.out (x : M ⧸ R)) = φ x
    rw [hr, hφR x r r.2]
  have hb' : ∀ x y : M, b' (x : M ⧸ R) (y : M ⧸ R) = b x y := by
    intro x y
    obtain ⟨r, hr⟩ := QuotientAddGroup.mk_out_eq_add R x
    obtain ⟨s, hs⟩ := QuotientAddGroup.mk_out_eq_add R y
    change b (Quotient.out (x : M ⧸ R)) (Quotient.out (y : M ⧸ R)) = b x y
    rw [hr, hs, hbR x _ r r.2, h.symm, hbR y _ s s.2, h.symm]
  have hQ : IsQuadFn φ' b' := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro p q
      obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective p
      obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective q
      rw [← QuotientAddGroup.mk_add, hφ', hφ', hφ', hb', h.add]
    · intro p q s
      obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective p
      obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective q
      obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective s
      rw [← QuotientAddGroup.mk_add, hb', hb', hb', h.left]
    · intro k p
      obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective p
      rw [← QuotientAddGroup.mk_nsmul, hφ', hφ', h.sq]
    · intro p
      exact h.ne _
    · intro p hp
      obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective p
      rw [QuotientAddGroup.eq_zero_iff]
      intro y
      rw [← hb']
      exact hp _
  have hG := gaussSumEighthPower (M ⧸ R) φ' b' hQ
  have hbij : Function.Bijective (fun p : (M ⧸ R) × R => (p.1.out + (p.2 : M) : M)) := by
    constructor
    · rintro ⟨q, r⟩ ⟨q', r'⟩ hqr
      simp only at hqr
      have hq : q = q' := by
        have h1 : ((q.out + (r : M) : M) : M ⧸ R) = ((q'.out + (r' : M) : M) : M ⧸ R) := by rw [hqr]
        rw [QuotientAddGroup.mk_add_of_mem _ r.2, QuotientAddGroup.mk_add_of_mem _ r'.2,
          QuotientAddGroup.out_eq', QuotientAddGroup.out_eq'] at h1
        exact h1
      subst hq
      have hr : (r : M) = r' := add_left_cancel hqr
      rw [Subtype.ext hr]
    · intro x
      obtain ⟨r, hr⟩ := QuotientAddGroup.mk_out_eq_add R x
      refine ⟨((x : M ⧸ R), -r), ?_⟩
      simp only [hr, AddSubgroup.coe_neg]
      abel
  have hsum : ∑ x, φ x = (Fintype.card R : ℂ) * ∑ q, φ' q := by
    rw [← hbij.sum_comp φ, Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    have : ∀ r : R, φ (q.out + (r : M)) = φ' q := fun r => hφR _ r r.2
    simp only [this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  refine ⟨(Fintype.card R : ℝ) ^ 8 * (Fintype.card (M ⧸ R) : ℝ) ^ 4, ?_, ?_⟩
  · have h1 : 0 < Fintype.card R := Fintype.card_pos
    have h2 : 0 < Fintype.card (M ⧸ R) := Fintype.card_pos
    positivity
  · rw [hsum, mul_pow, hG]
    push_cast
    ring

end Formalism.L2.Th1.H
