import Formalism.RealPlaceAnalysis.FockPairGl

open MvPolynomial

noncomputable section

namespace Formalism.REAL

lemma pderiv_pderiv_comm_real_place_taylor {σ : Type*} (v w : σ) (f : MvPolynomial σ ℂ) :
    pderiv v (pderiv w f) = pderiv w (pderiv v f) := by
  classical
  have hc : ⁅(pderiv v : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ)),
      (pderiv w : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ))⁆ = 0 := by
    apply MvPolynomial.derivation_ext
    intro i
    rw [Derivation.commutator_apply]
    simp only [pderiv_X, Pi.single_apply]
    split_ifs <;> simp
  have hf := congrArg (fun D : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ) => D f) hc
  simp only [Derivation.commutator_apply, Derivation.zero_apply] at hf
  exact sub_eq_zero.mp hf

lemma bilinear_commutator_identity {A : Type*} [Ring A] (p1 b1 p2 b2 d1 d2 : A)
    (h1 : b1 * p2 - p2 * b1 = d1) (h2 : b2 * p1 - p1 * b2 = d2)
    (hp : p1 * p2 = p2 * p1) (hb : b1 * b2 = b2 * b1)
    (hd1 : p1 * d1 = d1 * p1) (hd2 : p2 * d2 = d2 * p2) :
    p1 * b1 * (p2 * b2) - p2 * b2 * (p1 * b1) = d1 * (p1 * b2) - d2 * (p2 * b1) := by
  have e1 : b1 * p2 = p2 * b1 + d1 := by rw [← h1]; abel
  have e2 : b2 * p1 = p1 * b2 + d2 := by rw [← h2]; abel
  calc p1 * b1 * (p2 * b2) - p2 * b2 * (p1 * b1)
      = p1 * (b1 * p2) * b2 - p2 * (b2 * p1) * b1 := by simp only [mul_assoc]
    _ = p1 * (p2 * b1 + d1) * b2 - p2 * (p1 * b2 + d2) * b1 := by rw [e1, e2]
    _ = p1 * p2 * (b1 * b2) + p1 * d1 * b2 - (p2 * p1 * (b2 * b1) + p2 * d2 * b1) := by
        simp only [mul_add, add_mul, mul_assoc]
    _ = d1 * (p1 * b2) - d2 * (p2 * b1) := by
        rw [hp, hb, hd1, hd2]
        simp only [mul_assoc]
        abel

section ops
variable {σ : Type*} [DecidableEq σ]

set_option quotPrecheck false
local notation "D" v => ((pderiv v : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ)).toLinearMap :
  Module.End ℂ (MvPolynomial σ ℂ))
local notation "Mx" v => (LinearMap.mulLeft ℂ (X v : MvPolynomial σ ℂ) : Module.End ℂ (MvPolynomial σ ℂ))

lemma deriv_mulX_commutator (v w : σ) : (D v) * (Mx w) - (Mx w) * (D v) = if v = w then 1 else 0 := by
  by_cases h : v = w
  · subst h
    refine LinearMap.ext fun f => ?_
    simp [pderiv_mul, pderiv_X, Pi.single_apply]
    all_goals abel
  · refine LinearMap.ext fun f => ?_
    simp [pderiv_mul, pderiv_X, Pi.single_apply, h, Ne.symm h]

lemma mulX_negDeriv_commutator (v w : σ) : (Mx v) * -(D w) - -(D w) * (Mx v) = if v = w then 1 else 0 := by
  by_cases h : v = w
  · subst h
    refine LinearMap.ext fun f => ?_
    simp [pderiv_mul, pderiv_X, Pi.single_apply]
    all_goals abel
  · refine LinearMap.ext fun f => ?_
    simp [pderiv_mul, pderiv_X, Pi.single_apply, h, Ne.symm h]
    all_goals abel

lemma deriv_mul_deriv_comm (v w : σ) : (D v) * (D w) = (D w) * (D v) := by
  refine LinearMap.ext fun f => ?_
  simpa using pderiv_pderiv_comm_real_place_taylor v w f

lemma mulX_mul_mulX_comm (v w : σ) : (Mx v) * (Mx w) = (Mx w) * (Mx v) := by
  refine LinearMap.ext fun f => ?_
  simp
  all_goals ring

lemma deriv_mul_mulX_comm_of_ne {v w : σ} (h : v ≠ w) : (D v) * (Mx w) = (Mx w) * (D v) := by
  have hs := deriv_mulX_commutator v w
  rw [if_neg h] at hs
  exact sub_eq_zero.mp hs

end ops

theorem canonicalCommutation_holds : CCR := by
  intro M n' ε ε' i j a b
  have hI : (if (i, a) = (j, b) then 1 else 0 : Module.End ℂ (MvPolynomial (Fin M × Fin n') ℂ)) =
      if i = j ∧ a = b then 1 else 0 := by
    by_cases hh : i = j ∧ a = b
    · obtain ⟨rfl, rfl⟩ := hh
      simp
    · rw [if_neg hh, if_neg]
      intro he
      exact hh (Prod.mk.inj he)
  simp only [bop, bpl]
  by_cases h1 : sgnv ε ε' i a = true <;> by_cases h2 : sgnv ε ε' j b = true
  · simp only [if_pos h1, if_pos h2]
    exact ⟨(deriv_mulX_commutator _ _).trans hI, deriv_mul_deriv_comm _ _, mulX_mul_mulX_comm _ _⟩
  · have hne : (i, a) ≠ (j, b) := by
      intro he
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
      exact h2 h1
    have hnd : ¬(i = j ∧ a = b) := fun hh => hne (by rw [hh.1, hh.2])
    simp only [if_pos h1, if_neg h2]
    refine ⟨?_, deriv_mul_mulX_comm_of_ne hne, ?_⟩
    · rw [if_neg hnd, mul_neg, neg_mul, deriv_mul_deriv_comm (i, a) (j, b), sub_self]
    · rw [mul_neg, neg_mul, deriv_mul_mulX_comm_of_ne hne.symm]
  · have hne : (i, a) ≠ (j, b) := by
      intro he
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
      exact h1 h2
    have hnd : ¬(i = j ∧ a = b) := fun hh => hne (by rw [hh.1, hh.2])
    simp only [if_neg h1, if_pos h2]
    refine ⟨?_, (deriv_mul_mulX_comm_of_ne hne.symm).symm, ?_⟩
    · rw [if_neg hnd, mulX_mul_mulX_comm (i, a) (j, b), sub_self]
    · rw [neg_mul, mul_neg, deriv_mul_mulX_comm_of_ne hne]
  · simp only [if_neg h1, if_neg h2]
    refine ⟨(mulX_negDeriv_commutator _ _).trans hI, mulX_mul_mulX_comm _ _, ?_⟩
    rw [neg_mul_neg, neg_mul_neg, deriv_mul_deriv_comm (i, a) (j, b)]

lemma sum_sum_sub_sum_sum {A α β : Type*} [AddCommGroup A] [Fintype α] [Fintype β] (f g : α → β → A) :
    ∑ x, ∑ y, f x y - ∑ x, ∑ y, g x y = ∑ x, ∑ y, (f x y - g x y) := by
  simp only [Finset.sum_sub_distrib]

lemma sum_sum_sub_sum_sum_swap {A α β : Type*} [AddCommGroup A] [Fintype α] [Fintype β] (f : α → β → A)
    (g : β → α → A) :
    ∑ x, ∑ y, f x y - ∑ y, ∑ x, g y x = ∑ x, ∑ y, (f x y - g y x) := by
  simp only [Finset.sum_sub_distrib]
  congr 1
  exact Finset.sum_comm

section weyl
variable {A : Type*} [Ring A] {m n : ℕ} (B P : Fin m → Fin n → A)

def bilinearLeft (i j : Fin m) : A := ∑ a, P i a * B j a

def bilinearRight (a b : Fin n) : A := ∑ i, P i b * B i a

def bilinearNumber : A := ∑ i, ∑ a, P i a * B i a

def bilinearQuartic : A := ∑ i, ∑ j, ∑ a, ∑ b, P i a * P j b * B j a * B i b

variable {B P}
variable (hBP : ∀ i j a b, B i a * P j b - P j b * B i a = if i = j ∧ a = b then 1 else 0)
  (hBB : ∀ i j a b, B i a * B j b = B j b * B i a)
  (hPP : ∀ i j a b, P i a * P j b = P j b * P i a)
include hBP hBB hPP

lemma bilinear_product_commutator (i j k l : Fin m) (a b c d : Fin n) :
    P i a * B j b * (P k c * B l d) - P k c * B l d * (P i a * B j b) =
      (if j = k ∧ b = c then 1 else 0) * (P i a * B l d) -
        (if l = i ∧ d = a then 1 else 0) * (P k c * B j b) :=
  bilinear_commutator_identity _ _ _ _ _ _ (hBP j k b c) (hBP l i d a) (hPP i k a c) (hBB j l b d)
    (by split_ifs <;> simp) (by split_ifs <;> simp)

omit hBB hPP in
lemma lower_mul_raise (i j : Fin m) (a b : Fin n) :
    B i a * P j b = P j b * B i a + if i = j ∧ a = b then 1 else 0 := by
  rw [← hBP i j a b]
  abel

lemma satisfiesGlRelations_bilinearLeft : GlRel (bilinearLeft B P) := by
  intro a b c d
  simp only [bilinearLeft, Finset.sum_mul_sum]
  rw [sum_sum_sub_sum_sum_swap]
  simp only [bilinear_product_commutator hBP hBB hPP]
  simp only [Finset.sum_sub_distrib]
  congr 1
  · by_cases h : b = c <;> simp [h, ite_mul]
  · by_cases h : d = a <;> simp [h, ite_mul]

lemma bilinearRight_commutator (a b c d : Fin n) :
    bilinearRight B P a b * bilinearRight B P c d - bilinearRight B P c d * bilinearRight B P a b =
      (if a = d then bilinearRight B P c b else 0) - (if c = b then bilinearRight B P a d else 0) := by
  simp only [bilinearRight, Finset.sum_mul_sum]
  rw [sum_sum_sub_sum_sum_swap]
  simp only [bilinear_product_commutator hBP hBB hPP]
  simp only [Finset.sum_sub_distrib]
  congr 1
  · by_cases h : a = d <;> simp [h, ite_mul]
  · by_cases h : c = b <;> simp [h, ite_mul]

lemma bilinearLeft_mul_bilinearRight (i j : Fin m) (a b : Fin n) :
    bilinearLeft B P i j * bilinearRight B P a b = bilinearRight B P a b * bilinearLeft B P i j := by
  rw [← sub_eq_zero]
  simp only [bilinearLeft, bilinearRight, Finset.sum_mul_sum]
  rw [sum_sum_sub_sum_sum_swap]
  simp only [bilinear_product_commutator hBP hBB hPP]
  simp only [Finset.sum_sub_distrib]
  rw [sub_eq_zero]
  simp [ite_and, ite_mul]

omit hBB hPP in
lemma casimir_bilinearLeft : Cas (bilinearLeft B P) = bilinearQuartic B P + m • bilinearNumber B P := by
  have e : ∀ i j a b, P i a * B j a * (P j b * B i b) =
      P i a * P j b * B j a * B i b + (if a = b then P i a * B i b else 0) := by
    intro i j a b
    rw [show P i a * B j a * (P j b * B i b) = P i a * (B j a * P j b) * B i b by
      simp only [mul_assoc], lower_mul_raise hBP j j a b]
    by_cases h : a = b
    · subst h
      simp [mul_add, add_mul, mul_assoc]
    · simp [h, mul_assoc]
  simp only [Cas, bilinearLeft, bilinearQuartic, bilinearNumber, Finset.sum_mul_sum, e, Finset.sum_add_distrib]
  congr 1
  simp [Finset.smul_sum]

omit hBP hBB hPP in
lemma sum_sum_sum_sum_comm' {α β : Type*} [Fintype α] [Fintype β] (f : α → α → β → β → A) :
    ∑ x, ∑ y, ∑ i, ∑ j, f i j x y = ∑ i, ∑ j, ∑ x, ∑ y, f i j x y := by
  have h1 : ∀ x, ∑ y, ∑ i, ∑ j, f i j x y = ∑ i, ∑ j, ∑ y, f i j x y := by
    intro x
    calc ∑ y, ∑ i, ∑ j, f i j x y = ∑ i, ∑ y, ∑ j, f i j x y := Finset.sum_comm
      _ = ∑ i, ∑ j, ∑ y, f i j x y := Finset.sum_congr rfl fun i _ => Finset.sum_comm
  have h2 : ∀ i, ∑ x, ∑ j, ∑ y, f i j x y = ∑ j, ∑ x, ∑ y, f i j x y := fun i => Finset.sum_comm
  calc ∑ x, ∑ y, ∑ i, ∑ j, f i j x y = ∑ x, ∑ i, ∑ j, ∑ y, f i j x y :=
        Finset.sum_congr rfl fun x _ => h1 x
    _ = ∑ i, ∑ x, ∑ j, ∑ y, f i j x y := Finset.sum_comm
    _ = ∑ i, ∑ j, ∑ x, ∑ y, f i j x y := Finset.sum_congr rfl fun i _ => h2 i

omit hPP in
lemma casimir_bilinearRight_sum :
    ∑ a, ∑ b, bilinearRight B P a b * bilinearRight B P b a = bilinearQuartic B P + n • bilinearNumber B P := by
  have e : ∀ i j a b, P i b * B i a * (P j a * B j b) =
      P i b * P j a * B j b * B i a + (if i = j then P i b * B j b else 0) := by
    intro i j a b
    rw [show P i b * B i a * (P j a * B j b) = P i b * (B i a * P j a) * B j b by
      simp only [mul_assoc], lower_mul_raise hBP i j a a]
    by_cases h : i = j
    · subst h
      simp [mul_add, add_mul, mul_assoc, hBB i i a b]
    · simp [h, mul_assoc, hBB i j a b]
  have h1 : ∑ a, ∑ b, ∑ i, ∑ j, P i b * P j a * B j b * B i a = bilinearQuartic B P := by
    rw [sum_sum_sum_sum_comm']
    unfold bilinearQuartic
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_comm
  have h2 : ∑ a : Fin n, ∑ b, ∑ i, ∑ j, (if i = j then P i b * B j b else 0) = n • bilinearNumber B P := by
    unfold bilinearNumber
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin]
    congr 1
    exact Finset.sum_comm
  simp only [bilinearRight, Finset.sum_mul_sum, e, Finset.sum_add_distrib]
  rw [h1, h2]

end weyl

theorem fockPairGl_of (h : CCR) : FockPairGl := by
  intro M n' ε ε'
  have hBP : ∀ i j a b, bop ε ε' i a * bpl ε ε' j b - bpl ε ε' j b * bop ε ε' i a =
      if i = j ∧ a = b then 1 else 0 := fun i j a b => (h M n' ε ε' i j a b).1
  have hBB : ∀ i j a b, bop ε ε' i a * bop ε ε' j b = bop ε ε' j b * bop ε ε' i a :=
    fun i j a b => (h M n' ε ε' i j a b).2.1
  have hPP : ∀ i j a b, bpl ε ε' i a * bpl ε ε' j b = bpl ε ε' j b * bpl ε ε' i a :=
    fun i j a b => (h M n' ε ε' i j a b).2.2
  have hEg : Eg ε ε' = bilinearLeft (bop ε ε') (bpl ε ε') := by
    funext i j
    rfl
  have hEg' : Eg' ε ε' = fun a b => -bilinearRight (bop ε ε') (bpl ε ε') a b := by
    funext a b
    rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hEg]
    exact satisfiesGlRelations_bilinearLeft hBP hBB hPP
  · rw [hEg']
    intro a b c d
    simp only [neg_mul_neg]
    rw [bilinearRight_commutator hBP hBB hPP a b c d]
    simp only [eq_comm (a := a) (b := d), eq_comm (a := c) (b := b)]
    split_ifs <;> abel
  · intro i j a b
    rw [hEg, hEg']
    simp only [mul_neg, neg_mul]
    rw [bilinearLeft_mul_bilinearRight hBP hBB hPP]

theorem fockCas_of (h : CCR) : FockCas := by
  intro M n' ε ε'
  have hBP : ∀ i j a b, bop ε ε' i a * bpl ε ε' j b - bpl ε ε' j b * bop ε ε' i a =
      if i = j ∧ a = b then 1 else 0 := fun i j a b => (h M n' ε ε' i j a b).1
  have hBB : ∀ i j a b, bop ε ε' i a * bop ε ε' j b = bop ε ε' j b * bop ε ε' i a :=
    fun i j a b => (h M n' ε ε' i j a b).2.1
  have hEg : Eg ε ε' = bilinearLeft (bop ε ε') (bpl ε ε') := by
    funext i j
    rfl
  have hEg' : Eg' ε ε' = fun a b => -bilinearRight (bop ε ε') (bpl ε ε') a b := by
    funext a b
    rfl
  have hNN : NN ε ε' = bilinearNumber (bop ε ε') (bpl ε ε') := rfl
  refine ⟨?_, ?_⟩
  · simp only [NN, Eg, Eg', Finset.sum_neg_distrib, neg_neg]
    exact Finset.sum_comm
  · have hc : Cas (Eg' ε ε') = ∑ a, ∑ b,
        bilinearRight (bop ε ε') (bpl ε ε') a b * bilinearRight (bop ε ε') (bpl ε ε') b a := by
      rw [hEg']
      simp only [Cas, neg_mul_neg]
    rw [hc, casimir_bilinearRight_sum hBP hBB, hEg, casimir_bilinearLeft hBP, hNN, Nat.cast_smul_eq_nsmul,
      Nat.cast_smul_eq_nsmul]
    abel

end Formalism.REAL
