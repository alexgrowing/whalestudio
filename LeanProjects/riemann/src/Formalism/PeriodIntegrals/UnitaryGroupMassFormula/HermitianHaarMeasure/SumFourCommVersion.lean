import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianHaarMeasure.LowerRightNeZeroOfUpperRightZero

open Matrix Finset

noncomputable section

namespace PI.QnHermHaar

open Formalism.REAL Formalism.FourierDecayAlt.Q

theorem commSumA {A : Type*} [Ring A] {ι : Type*} [Fintype ι] (h : ι → A) (g : A) :
    (∑ i, h i) * g - g * (∑ i, h i) = ∑ i, (h i * g - g * h i) := by
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]

theorem commSumB {A : Type*} [Ring A] {ι : Type*} [Fintype ι] (h : ι → A) (g : A) :
    g * (∑ i, h i) - (∑ i, h i) * g = ∑ i, (g * h i - h i * g) := by
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]

theorem smulComm {A : Type*} [Ring A] [Algebra ℂ A] (α β : ℂ) (X Y : A) :
    (α • X) * (β • Y) - (β • Y) * (α • X) = (α * β) • (X * Y - Y * X) := by
  rw [smul_mul_smul_comm, smul_mul_smul_comm, mul_comm β α, smul_sub]

def vecC {A : Type*} [Ring A] [Algebra ℂ A] {m : ℕ} (Q : Matrix (Fin m) (Fin m) ℂ) (Y : Fin m → A) : Fin m → A :=
  fun c => ∑ k, Q c k • Y k

def covC {A : Type*} [Ring A] [Algebra ℂ A] {m : ℕ} (P : Matrix (Fin m) (Fin m) ℂ) (Yb : Fin m → A) : Fin m → A :=
  fun c => ∑ l, P l c • Yb l

theorem qpApply {m : ℕ} (P Q : Matrix (Fin m) (Fin m) ℂ) (hQP : Q * P = 1) (b c : Fin m) :
    ∑ j, Q b j * P j c = if b = c then 1 else 0 := by
  have h := congrFun (congrFun hQP b) c
  rw [Matrix.mul_apply, Matrix.one_apply] at h
  exact h

theorem glConj {A : Type*} [Ring A] [Algebra ℂ A] {m : ℕ} (E : Fin m → Fin m → A)
    (P Q : Matrix (Fin m) (Fin m) ℂ) (hGl : GlRel E) (hQP : Q * P = 1) : GlRel (Econj E P Q) := by
  intro a b c d
  have hG : ∀ a b c d, E a b * E c d - E c d * E a b = (if b = c then E a d else 0) - (if d = a then E c b else 0) := hGl
  simp only [Econj]
  simp_rw [commSumA]
  simp_rw [commSumB]
  simp only [smulComm, hG, smul_sub, Finset.sum_sub_distrib, smul_ite, smul_zero]
  congr 1
  ·
    simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [Finset.sum_congr rfl (fun i _ => Finset.sum_comm)]
    simp only [← Finset.sum_smul]
    have hc : ∀ i l : Fin m, ∑ j, P i a * Q b j * (P j c * Q d l) = (if b = c then 1 else 0) * (P i a * Q d l) := by
      intro i l
      rw [← qpApply P Q hQP b c, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      ring
    simp only [hc]
    split_ifs <;> simp
  ·
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    have e2 : ∀ i j k : Fin m, P i a * Q b j * (P k c * Q d i) = (P k c * Q b j) * (Q d i * P i a) := by
      intros; ring
    simp only [e2]
    rw [Finset.sum_comm, Finset.sum_congr rfl (fun j _ => Finset.sum_comm)]
    simp only [← Finset.sum_smul, ← Finset.mul_sum, qpApply P Q hQP d a]
    split_ifs with h
    · simp only [mul_one]
      exact Finset.sum_comm
    · simp

theorem leibVec {A : Type*} [Ring A] [Algebra ℂ A] {m : ℕ} (E : Fin m → Fin m → A) (Y : Fin m → A)
    (P Q : Matrix (Fin m) (Fin m) ℂ) (hQP : Q * P = 1)
    (hL : ∀ a b c, E a b * Y c - Y c * E a b = if a = c then -Y b else 0) (a b c : Fin m) :
    Econj E P Q a b * vecC Q Y c - vecC Q Y c * Econj E P Q a b = if a = c then -vecC Q Y b else 0 := by
  simp only [Econj, vecC]
  simp_rw [commSumA]
  simp_rw [commSumB]
  simp only [smulComm, hL, smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Finset.sum_comm]
  have e : ∀ i j : Fin m, P i a * Q b j * Q c i = Q b j * (Q c i * P i a) := by intros; ring
  simp only [e, ← Finset.sum_smul, ← Finset.mul_sum, qpApply P Q hQP c a]
  split_ifs with h1 h2 h2
  · simp [Finset.sum_neg_distrib]
  · exact absurd h1.symm h2
  · exact absurd h2.symm h1
  · simp

theorem leibCov {A : Type*} [Ring A] [Algebra ℂ A] {m : ℕ} (E : Fin m → Fin m → A) (Yb : Fin m → A)
    (P Q : Matrix (Fin m) (Fin m) ℂ) (hQP : Q * P = 1)
    (hL : ∀ a b c, E a b * Yb c - Yb c * E a b = if b = c then Yb a else 0) (a b c : Fin m) :
    Econj E P Q a b * covC P Yb c - covC P Yb c * Econj E P Q a b = if b = c then covC P Yb a else 0 := by
  simp only [Econj, covC]
  simp_rw [commSumA]
  simp_rw [commSumB]
  simp only [smulComm, hL, smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have e : ∀ i j : Fin m, P i a * Q b j * P j c = P i a * (Q b j * P j c) := by intros; ring
  simp only [e, ← Finset.sum_smul, ← Finset.mul_sum, qpApply P Q hQP b c]
  split_ifs <;> simp

theorem commVec {A : Type*} [Ring A] [Algebra ℂ A] {m : ℕ} (Y : Fin m → A) (Q : Matrix (Fin m) (Fin m) ℂ)
    (hYY : ∀ a b, Y a * Y b = Y b * Y a) (a b : Fin m) :
    vecC Q Y a * vecC Q Y b = vecC Q Y b * vecC Q Y a := by
  simp only [vecC, Finset.sum_mul_sum, smul_mul_smul_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun k _ => ?_))
  rw [hYY k l, mul_comm (Q a k)]

theorem commCov {A : Type*} [Ring A] [Algebra ℂ A] {m : ℕ} (Yb : Fin m → A) (P : Matrix (Fin m) (Fin m) ℂ)
    (hYY : ∀ a b, Yb a * Yb b = Yb b * Yb a) (a b : Fin m) :
    covC P Yb a * covC P Yb b = covC P Yb b * covC P Yb a := by
  simp only [covC, Finset.sum_mul_sum, smul_mul_smul_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun k _ => ?_))
  rw [hYY k l, mul_comm (P k a)]

theorem sum_four_comm_version {A : Type*} [AddCommMonoid A] {m : ℕ} (f : Fin m → Fin m → Fin m → Fin m → A) :
    ∑ i, ∑ j, ∑ k, ∑ l, f i j k l = ∑ k, ∑ l, ∑ i, ∑ j, f i j k l := by
  calc _ = ∑ i, ∑ k, ∑ j, ∑ l, f i j k l := Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
    _ = ∑ k, ∑ i, ∑ j, ∑ l, f i j k l := Finset.sum_comm
    _ = ∑ k, ∑ i, ∑ l, ∑ j, f i j k l :=
        Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun i _ => Finset.sum_comm))
    _ = _ := Finset.sum_congr rfl (fun k _ => Finset.sum_comm)

theorem starConj {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] {m : ℕ}
    (E : Fin m → Fin m → A) (Hm P Q : Matrix (Fin m) (Fin m) ℂ) (ε : Fin m → ℤˣ)
    (hstar : ∀ a b, star (E a b) = ∑ c, ∑ d, (Hm c b * Hm a d) • E c d)
    (hP : ∀ i j, star (P i j) = Q j i) (hQ : ∀ i j, star (Q i j) = P j i)
    (hHP : ∀ k b, ∑ j, Hm k j * P j b = P k b * ((ε b : ℤ) : ℂ))
    (hQH : ∀ a l, ∑ i, Q a i * Hm i l = ((ε a : ℤ) : ℂ) * Q a l) (a b : Fin m) :
    star (Econj E P Q a b) = (((ε a * ε b : ℤˣ) : ℤ) : A) * Econj E P Q b a := by
  simp only [Econj, star_sum, star_smul, hstar, Finset.smul_sum, smul_smul, star_mul', hP, hQ]
  rw [sum_four_comm_version]
  simp only [← Finset.sum_smul, intCastMul, Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))
  congr 1
  have h1 : ∑ i, ∑ j, Q a i * P j b * (Hm k j * Hm i l) = (∑ i, Q a i * Hm i l) * (∑ j, Hm k j * P j b) := by
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    ring
  rw [h1, hQH, hHP]
  push_cast
  ring

theorem relCov {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] {m : ℕ}
    (Y Yb : Fin m → A) (Hm P Q : Matrix (Fin m) (Fin m) ℂ) (ε : Fin m → ℤˣ)
    (hYb : ∀ c, Yb c = ∑ l, Hm l c • star (Y l)) (hQ : ∀ i j, star (Q i j) = P j i)
    (hHP : ∀ k b, ∑ j, Hm k j * P j b = P k b * ((ε b : ℤ) : ℂ)) (c : Fin m) :
    covC P Yb c = ((ε c : ℤ) : ℂ) • star (vecC Q Y c) := by
  simp only [covC, vecC, hYb, star_sum, star_smul, hQ, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  congr 1
  rw [Finset.sum_congr rfl (fun j _ => mul_comm (P j c) (Hm k j)), hHP k c]
  ring

theorem relX {m : ℕ} (x xb : Fin m → ℂ) (Hm P Q : Matrix (Fin m) (Fin m) ℂ) (ε : Fin m → ℤˣ)
    (hxb : ∀ c, xb c = ∑ l, Hm l c * star (x l)) (hQ : ∀ i j, star (Q i j) = P j i)
    (hHP : ∀ k b, ∑ j, Hm k j * P j b = P k b * ((ε b : ℤ) : ℂ)) (c : Fin m) :
    (xb ᵥ* P) c = ((ε c : ℤ) : ℂ) * star ((Q *ᵥ x) c) := by
  simp only [Matrix.vecMul, Matrix.mulVec, dotProduct, hxb, star_sum, star_mul', hQ, Finset.sum_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have h := hHP k c
  have h2 : ∑ j, Hm k j * star (x k) * P j c = (∑ j, Hm k j * P j c) * star (x k) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  rw [h2, h]
  ring

theorem diagInvol {m : ℕ} (Hm : Matrix (Fin m) (Fin m) ℂ) (hH : Hmᴴ = Hm) (h2 : Hm * Hm = 1) :
    ∃ (U : Matrix (Fin m) (Fin m) ℂ) (ε : Fin m → ℤˣ), star U * U = 1 ∧ U * star U = 1 ∧
      Hm * U = U * diagonal (fun j => ((ε j : ℤ) : ℂ)) := by
  have hA : Hm.IsHermitian := hH
  have hu1 : star (hA.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ) * (hA.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp hA.eigenvectorUnitary.2
  have hu2 : (hA.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ) * star (hA.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff.mp hA.eigenvectorUnitary.2
  set U : Matrix (Fin m) (Fin m) ℂ := (hA.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ) with hU
  set lam : Fin m → ℂ := fun j => ((hA.eigenvalues j : ℝ) : ℂ) with hlam
  have hHU : Hm * U = U * diagonal lam := by
    ext i j
    rw [Matrix.mul_diagonal, Matrix.mul_apply]
    have h := congrFun (hA.mulVec_eigenvectorBasis j) i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, Complex.real_smul] at h
    simp only [hU, Matrix.IsHermitian.eigenvectorUnitary_apply, hlam]
    rw [h, mul_comm]
  have hD1 : star U * Hm * U = diagonal lam := by
    rw [Matrix.mul_assoc, hHU, ← Matrix.mul_assoc, hu1, Matrix.one_mul]
  have hD : diagonal lam * diagonal lam = 1 := by
    rw [← hD1]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc U (star U), hu2, Matrix.one_mul, ← Matrix.mul_assoc Hm Hm, h2, Matrix.one_mul, hu1]
  have hr : ∀ j, hA.eigenvalues j = 1 ∨ hA.eigenvalues j = -1 := by
    intro j
    have h := congrFun (congrFun hD j) j
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_eq, Matrix.one_apply_eq] at h
    simp only [hlam] at h
    have h' : hA.eigenvalues j * hA.eigenvalues j = 1 := by exact_mod_cast h
    exact mul_self_eq_one_iff.mp h'
  refine ⟨U, fun j => if hA.eigenvalues j = 1 then 1 else -1, hu1, hu2, ?_⟩
  rw [hHU]
  congr 2
  funext j
  rcases hr j with h | h
  · simp [hlam, h]
  · have hn : ¬ hA.eigenvalues j = 1 := by rw [h]; norm_num
    show ((hA.eigenvalues j : ℝ) : ℂ) = (((if hA.eigenvalues j = 1 then (1 : ℤˣ) else -1 : ℤˣ) : ℤ) : ℂ)
    rw [if_neg hn, h]
    simp

end PI.QnHermHaar
