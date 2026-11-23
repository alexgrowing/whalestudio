import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RatBasisLinearIndependentInt

set_option autoImplicit false

noncomputable section

open DividedPowers Polynomial TensorProduct

namespace GlobalTheory.PDA.Model

def xd (n : ℕ) : ℚ[X] := monomial n ((n.factorial : ℚ)⁻¹)

theorem xd_zero : xd 0 = 1 := by simp [xd]

theorem xd_mul (m n : ℕ) : xd m * xd n = ((m + n).choose m : ℚ[X]) * xd (m + n) := by
  have h : (((m + n).choose m : ℕ) : ℚ[X]) = C (((m + n).choose m : ℕ) : ℚ) := by simp
  rw [h, xd, xd, xd, monomial_mul_monomial, C_mul_monomial]
  congr 1
  have hm : (m.factorial : ℚ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
  have hn : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have hmn : ((m + n).factorial : ℚ) ≠ 0 := by exact_mod_cast (m + n).factorial_ne_zero
  have := Nat.add_choose_mul_factorial_mul_factorial m n
  rw [← Nat.choose_symm_add] at this
  have h2 : (((m + n).choose m : ℕ) : ℚ) * m.factorial * n.factorial = (m + n).factorial := by
    exact_mod_cast this
  field_simp
  linarith

theorem xd_li : LinearIndependent ℤ xd := by
  rw [linearIndependent_iff']
  intro s g hg i hi
  have := congrArg (fun p : ℚ[X] ↦ p.coeff i) hg
  simp only [finset_sum_coeff, xd, coeff_zero, coeff_smul, coeff_monomial] at this
  rw [Finset.sum_eq_single i (by intro j _ hj; simp [hj]) (by intro h; exact absurd hi h)] at this
  have hm : (i.factorial : ℚ) ≠ 0 := by exact_mod_cast i.factorial_ne_zero
  simpa [hm] using this

def L : Subalgebra ℤ ℚ[X] :=
  (Submodule.span ℤ (Set.range xd)).toSubalgebra
    (xd_zero ▸ Submodule.subset_span ⟨0, rfl⟩)
    (by
      intro x y hx hy
      refine Submodule.span_induction₂ (p := fun x y _ _ ↦ x * y ∈ Submodule.span ℤ (Set.range xd))
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
      · rintro _ _ ⟨m, rfl⟩ ⟨n, rfl⟩
        rw [xd_mul, ← nsmul_eq_mul]
        exact Submodule.smul_of_tower_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
      · intro y _; simp
      · intro y _; simp
      · intro x y z _ _ _ h1 h2; rw [add_mul]; exact add_mem h1 h2
      · intro x y z _ _ _ h1 h2; rw [mul_add]; exact add_mem h1 h2
      · intro r x y _ _ h; rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ h
      · intro r x y _ _ h; rw [mul_smul_comm]; exact Submodule.smul_mem _ _ h)

def bL : Module.Basis ℕ ℤ L := Module.Basis.span xd_li

theorem bL_coe (n : ℕ) : (bL n : ℚ[X]) = xd n := Module.Basis.span_apply xd_li n ▸ rfl

theorem bL_zero : bL 0 = 1 := Subtype.ext (by rw [bL_coe, xd_zero]; rfl)

theorem bL_mul (m n : ℕ) : bL m * bL n = ((m + n).choose m : L) * bL (m + n) :=
  Subtype.ext (by simp [bL_coe, xd_mul])

def pdPoly (B : Type) [CommRing B] : PDPoly B where
  P := B ⊗[ℤ] L
  e := Algebra.TensorProduct.basis B bL
  e_zero := by simp [bL_zero, Algebra.TensorProduct.one_def]
  e_mul m n := by
    simp only [Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul, bL_mul]
    rw [← nsmul_eq_mul, ← nsmul_eq_mul, tmul_smul]

variable {B : Type} [CommRing B] {J : Ideal B}

theorem e_one_pow (Q : PDPoly B) (n : ℕ) : Q.e 1 ^ n = (n.factorial : Q.P) * Q.e n := by
  induction n with
  | zero => simp [Q.e_zero]
  | succ n ih =>
    rw [pow_succ', ih, mul_left_comm, Q.e_mul, Nat.factorial_succ, add_comm 1 n]
    simp; ring

theorem exists_isStd [Algebra ℚ B] (Q : PDPoly B) (δ : DividedPowers J) :
    ∃ η : DividedPowers (Q.ext J), Q.IsStd δ η := by
  classical
  letI : Algebra ℚ Q.P := ((algebraMap B Q.P).comp (algebraMap ℚ B)).toAlgebra
  have key : ∀ (n : ℕ) (x y : Q.P), (n.factorial : Q.P) * x = n.factorial * y → x = y :=
    fun n x y h ↦ (IsUnit.natCast_factorial_of_algebra (A := Q.P) ℚ n).mul_left_cancel h
  have h1 : Q.e 1 ∈ Q.ext J := Ideal.mem_sup_right (Ideal.subset_span ⟨0, rfl⟩)
  refine ⟨RatAlgebra.dividedPowers _, ⟨le_sup_left, fun {n} a ha ↦ key n _ _ ?_⟩, fun n ↦ key n _ _ ?_⟩
  · have h2 : algebraMap B Q.P a ∈ Q.ext J := Ideal.mem_sup_left (Ideal.mem_map_of_mem _ ha)
    rw [factorial_mul_dpow_eq_pow _ h2, ← map_pow,
      ← factorial_mul_dpow_eq_pow δ ha, map_mul, map_natCast]
  · rw [factorial_mul_dpow_eq_pow _ h1, e_one_pow]

theorem fil_zero (δ : DividedPowers J) : fil δ 0 = ⊤ :=
  (Ideal.eq_top_iff_one _).2 (Ideal.subset_span ⟨[], by simp⟩)

theorem fil_one (δ : DividedPowers J) : fil δ 1 = J := by
  refine le_antisymm (Ideal.span_le.2 ?_) fun x hx ↦
    Ideal.subset_span ⟨[(1, x)], by simpa using hx, by simp, by simp [δ.dpow_one hx]⟩
  rintro _ ⟨l, hl, hs, rfl⟩
  induction l with
  | nil => simp at hs
  | cons p l ih =>
    simp only [List.map_cons, List.prod_cons, SetLike.mem_coe]
    by_cases h : p.1 = 0
    · refine J.mul_mem_left _ (ih (fun q hq ↦ hl q (by simp [hq])) ?_)
      simpa [h] using hs
    · exact J.mul_mem_right _ (δ.dpow_mem h (hl p (by simp)))

theorem isLev_two [DecidablePred (fun x ↦ x ∈ J)] (h2 : J ^ 2 = 0) :
    IsLev (OfSquareZero.dividedPowers h2) 2 := by
  set δ := OfSquareZero.dividedPowers h2 with hδ
  refine le_bot_iff.1 (Ideal.span_le.2 ?_)
  rintro _ ⟨l, hl, hs, rfl⟩
  induction l with
  | nil => simp at hs
  | cons p l ih =>
    simp only [List.map_cons, List.prod_cons, SetLike.mem_coe, Ideal.mem_bot, List.sum_cons] at hs ih ⊢
    have hl' : ∀ q ∈ l, q.2 ∈ J := fun q hq ↦ hl q (by simp [hq])
    have hp : p.2 ∈ J := hl p (by simp)
    rcases Nat.lt_trichotomy p.1 1 with h | h | h
    · rw [ih hl' (by omega), mul_zero]
    · have hm : (l.map fun p ↦ δ.dpow p.1 p.2).prod ∈ J :=
        (fil_one δ).le (Ideal.subset_span ⟨l, hl', by omega, rfl⟩)
      have := Ideal.mul_mem_mul (δ.dpow_mem (n := p.1) (by omega) hp) hm
      rw [← pow_two, h2] at this
      simpa using this
    · have : δ.dpow p.1 p.2 = 0 := OfSquareZero.dpow_of_two_le h2 h p.2
      rw [this, zero_mul]

theorem isLev_one_iff (δ : DividedPowers J) : IsLev δ 1 ↔ J = ⊥ := by rw [IsLev, fil_one]

theorem not_isLev [Nontrivial B] (Q : PDPoly B) (δ : DividedPowers J) (η : DividedPowers (Q.ext J))
    (h : Q.IsStd δ η) (N : ℕ) : ¬ IsLev η N := by
  intro hN
  have h1 : Q.e 1 ∈ Q.ext J := Ideal.mem_sup_right (Ideal.subset_span ⟨0, rfl⟩)
  have : Q.e N ∈ fil η N := Ideal.subset_span ⟨[(N, Q.e 1)], by simpa using h1, by simp, by simp [h.var]⟩
  rw [hN] at this
  exact Q.e.ne_zero N this

end GlobalTheory.PDA.Model
