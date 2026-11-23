import Mathlib
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Formalism.LocalToGlobal.Columns.CoefColLemmas
import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant

open MvPolynomial

noncomputable section

namespace GlobalTheory.BranchFormula

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Col.Br

def IsBlock {R : Type} [Zero R] {N n : ℕ} (hN : N = n + 1) (A' : Matrix (Fin N) (Fin N) R) (A : Matrix (Fin n) (Fin n) R) (t : R) :
    Prop :=
  (∀ a b : Fin n, A' (iC hN a) (iC hN b) = A a b) ∧
    (∀ a : Fin n, A' (iC hN a) (iL hN) = 0 ∧ A' (iL hN) (iC hN a) = 0) ∧ A' (iL hN) (iL hN) = t

theorem IsBlock.transpose {R : Type} [Zero R] {N n : ℕ} {hN : N = n + 1} {A' : Matrix (Fin N) (Fin N) R}
    {A : Matrix (Fin n) (Fin n) R} {t : R} (h : IsBlock hN A' A t) : IsBlock hN A'.transpose A.transpose t :=
  ⟨fun a b => h.1 b a, fun a => ⟨(h.2.1 a).2, (h.2.1 a).1⟩, h.2.2⟩

theorem prod_split {M : Type*} [CommMonoid M] {N n : ℕ} (hN : N = n + 1) (f : Fin N → M) :
    ∏ a, f a = (∏ a : Fin n, f (iC hN a)) * f (iL hN) := by
  subst hN
  exact Fin.prod_univ_castSucc f

theorem sum_split {M : Type*} [AddCommMonoid M] {N n : ℕ} (hN : N = n + 1) (f : Fin N → M) :
    ∑ a, f a = (∑ a : Fin n, f (iC hN a)) + f (iL hN) := by
  subst hN
  exact Fin.sum_univ_castSucc f

theorem IsBlock.det {R : Type} [CommRing R] {N n : ℕ} {hN : N = n + 1} {A' : Matrix (Fin N) (Fin N) R}
    {A : Matrix (Fin n) (Fin n) R} {t : R} (h : IsBlock hN A' A t) : A'.det = A.det * t := by
  subst hN
  rw [Matrix.det_succ_row A' (Fin.last n), Fin.sum_univ_castSucc, Finset.sum_eq_zero, zero_add]
  · have h1 : A'.submatrix (Fin.last n).succAbove (Fin.last n).succAbove = A := by
      ext a b
      simp only [Matrix.submatrix_apply, Fin.succAbove_last]
      exact h.1 a b
    have h2 : A' (Fin.last n) (Fin.last n) = t := h.2.2
    rw [h1, h2, ← two_mul, pow_mul]
    simp [mul_comm]
  · intro a _
    have h2 : A' (Fin.last n) a.castSucc = 0 := (h.2.1 a).2
    rw [h2]
    simp

variable (K : Type) [Field K] (ι : Type) {N n : ℕ} (hN : N = n + 1)

def splitLast (_hN : N = n + 1) : Pol K ι N →ₐ[K] MvPolynomial (ι × Fin n) (Pol K ι n) :=
  aeval fun v : ι × Fin N × Fin N =>
    if h2 : v.2.2.val < n then
      (if h1 : v.2.1.val < n then C (X (v.1, ⟨v.2.1.val, h1⟩, ⟨v.2.2.val, h2⟩)) else X (v.1, ⟨v.2.2.val, h2⟩))
    else 0

@[simp] theorem splitLast_X_up (τ : ι) (a s : Fin n) :
    splitLast K ι hN (X (τ, iC hN a, iC hN s)) = C (X (τ, a, s)) := by
  simp [splitLast, iC]

@[simp] theorem splitLast_X_lastRow (τ : ι) (s : Fin n) :
    splitLast K ι hN (X (τ, iL hN, iC hN s)) = X (τ, s) := by
  simp [splitLast, iC, iL]

@[simp] theorem splitLast_X_lastCol (τ : ι) (a : Fin N) :
    splitLast K ι hN (X (τ, a, iL hN)) = 0 := by
  simp [splitLast, iL]

def expOf {ι : Type} [Fintype ι] {n : ℕ} (b : ι → Fin n → ℕ) : ι × Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun p => b p.1 p.2

@[simp] theorem expOf_apply {ι : Type} [Fintype ι] {n : ℕ} (b : ι → Fin n → ℕ) (p : ι × Fin n) : expOf b p = b p.1 p.2 := rfl

theorem coefLast_eq_coeff [Fintype ι] (b : ι → Fin n → ℕ) (F : Pol K ι N) :
    coefLast hN b F = coeff (expOf b) (splitLast K ι hN F) := by
  classical
  induction F using MvPolynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial m a =>
    have e : (monomial m a : Pol K ι N) = a • monomial m 1 := by simp [smul_monomial]
    rw [e, map_smul, map_smul, coeff_smul]
    congr 1
    rw [coefLast_monomial]
    have hm : splitLast K ι hN (monomial m 1) =
        (∏ τ, ∏ a, (0 : MvPolynomial (ι × Fin n) (Pol K ι n)) ^ m (τ, a, iL hN)) *
          monomial (expOf fun τ s => m (τ, iL hN, iC hN s))
            (monomial (m.comapDomain (upVar hN) (upVar_inj hN).injOn) (1 : K)) := by
      rw [monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (by simp), map_prod, Fintype.prod_prod_type,
        monomial_eq, monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (by simp), Finsupp.prod_fintype _ _ (by simp),
        map_prod, Fintype.prod_prod_type, Fintype.prod_prod_type (f := fun p : ι × Fin n => _), ← Finset.prod_mul_distrib,
        ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun τ _ => ?_
      rw [Fintype.prod_prod_type, Fintype.prod_prod_type]
      simp only [prod_split hN, map_pow, splitLast_X_up, splitLast_X_lastRow, splitLast_X_lastCol, expOf_apply,
        Finsupp.comapDomain_apply, upVar, Finset.prod_mul_distrib]
      ring
    rw [hm]
    by_cases h2 : ∀ τ a, m (τ, a, iL hN) = 0
    · simp only [h2, pow_zero, Finset.prod_const_one, one_mul, coeff_monomial]
      congr 1
      apply propext
      constructor
      · intro h
        ext p
        simp [h.1]
      · intro h
        exact ⟨fun τ s => by simpa using congrArg (fun e => e (τ, s)) h, h2⟩
    · rw [if_neg (fun h => h2 h.2)]
      push Not at h2
      obtain ⟨τ, a, h⟩ := h2
      rw [Finset.prod_eq_zero (Finset.mem_univ τ) (Finset.prod_eq_zero (Finset.mem_univ a) (zero_pow h))]
      simp

section Proj

variable {K ι} [Fintype ι] [CharZero K]

omit [Fintype ι] [CharZero K] in
theorem fockB_comm {σ : Type} (f g : MvPolynomial σ K) : fockB f g = fockB g f :=
  @fockSHerm K _ starRingOfComm _ g f

theorem eq_of_fockB (sg : ι → DomWeight n) {x x' : VV K sg}
    (h : ∀ y ∈ VV K sg, fockB (x : Pol K ι n) y = fockB (x' : Pol K ι n) y) : x = x' := by
  rw [← sub_eq_zero]
  refine (pairingBNondegenerate_holds K ι n sg).1 _ fun y => ?_
  rw [map_sub, LinearMap.sub_apply, pairBK_apply, pairBK_apply, pairB_apply, pairB_apply, h y y.2, sub_self]

theorem isUnit_det_gramB (sg : ι → DomWeight n) [DecidableEq (VVIdx sg)] : IsUnit (gramB (K := K) sg).det := by
  rw [isUnit_iff_ne_zero, Ne, ← Matrix.exists_vecMul_eq_zero_iff]
  rintro ⟨v, hv, h⟩
  apply hv
  have h0 : (∑ i, v i • bVV K sg i : VV K sg) = 0 := by
    refine (pairingBNondegenerate_holds K ι n sg).1 _ fun y => ?_
    have : pairBK sg (∑ i, v i • bVV K sg i : VV K sg) = 0 := by
      refine (bVV K sg).ext fun j => ?_
      have hj := congrFun h j
      simp only [Matrix.vecMul, dotProduct, gramB, Matrix.of_apply, Pi.zero_apply] at hj
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, pairBK_apply, pairB_apply, bVV_coe,
        smul_eq_mul, LinearMap.zero_apply]
      simp only [mul_left_comm (v _), ← Finset.mul_sum, hj, mul_zero]
    rw [this]
    rfl
  funext i
  exact Fintype.linearIndependent_iff.1 (bVV K sg).linearIndependent v h0 i

theorem fockB_projVV (sg : ι → DomWeight n) (F : Pol K ι n) {y : Pol K ι n} (hy : y ∈ VV K sg) :
    fockB (projVV sg F : Pol K ι n) y = fockB F y := by
  classical
  have key : ∀ k, fockB (projVV sg F : Pol K ι n) (bVVfun K sg k) = fockB F (bVVfun K sg k) := by
    intro k
    have hinv := Matrix.mul_nonsing_inv _ (isUnit_det_gramB (K := K) sg)
    rw [← fockBL_apply]
    simp only [projVV, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.smulRight_apply, Submodule.coe_sum,
      Submodule.coe_smul, map_sum, map_smul, bVV_coe, smul_eq_mul, fockBL_apply]
    rw [Finset.sum_comm]
    have h1 : ∀ j, ∑ i, (gramB (K := K) sg)⁻¹ i j * (fockB (bVVfun K sg j) F * fockB (bVVfun K sg i) (bVVfun K sg k)) =
        (1 : Matrix (VVIdx sg) (VVIdx sg) K) k j * fockB (bVVfun K sg j) F := by
      intro j
      rw [← hinv, Matrix.mul_apply, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [fockB_comm (bVVfun K sg i)]
      simp only [gramB, Matrix.of_apply]
      ring
    refine (Finset.sum_congr rfl fun j _ => ?_).trans ((Finset.sum_congr rfl fun j _ => h1 j).trans ?_)
    · congr!
    · simp [Matrix.one_apply, fockB_comm F]
  rw [← (bVVfun_spec K sg).2] at hy
  induction hy using Submodule.span_induction with
  | mem y hy => obtain ⟨k, rfl⟩ := hy; exact key k
  | zero => simp only [← fockBL_apply, map_zero]
  | add y z _ _ hy hz => simp only [← fockBL_apply, map_add] at *; rw [hy, hz]
  | smul a y _ hy => simp only [← fockBL_apply, map_smul] at *; rw [hy]

theorem projVV_coe (sg : ι → DomWeight n) (x : VV K sg) : projVV sg (x : Pol K ι n) = x :=
  eq_of_fockB sg fun _ hy => fockB_projVV sg _ hy

omit [CharZero K] in
theorem fockB_blockAct (U : ι → Matrix (Fin n) (Fin n) K) (F F' : Pol K ι n) :
    fockB (Formalism.GradedWeylDivisibility.blockAct K U F) F' = fockB F (Formalism.GradedWeylDivisibility.blockAct K (fun τ => (U τ).transpose) F') :=
  @fockSAdj K _ starRingOfComm ι _ n U F F'

omit [CharZero K] in
theorem blockAct_mem_VV (sg : ι → DomWeight n) (U : ι → Matrix (Fin n) (Fin n) K) {F : Pol K ι n} (hF : F ∈ VV K sg) :
    Formalism.GradedWeylDivisibility.blockAct K U F ∈ VV K sg :=
  (Formalism.GradedWeylDivisibility.blockActTensor K K ι n n U).2 (fun τ => nablaSq K n (sg τ)) (fun τ => nablaSq K n (sg τ))
    (fun _ f hf => Formalism.GradedWeylDivisibility.dualWeylRowStable K n n _ _ f hf) F hF

theorem projVV_blockAct (sg : ι → DomWeight n) (U : ι → Matrix (Fin n) (Fin n) K) (F : Pol K ι n) :
    (projVV sg (Formalism.GradedWeylDivisibility.blockAct K U F) : Pol K ι n) = Formalism.GradedWeylDivisibility.blockAct K U (projVV sg F : Pol K ι n) := by
  have := eq_of_fockB sg (x := projVV sg (Formalism.GradedWeylDivisibility.blockAct K U F))
    (x' := ⟨_, blockAct_mem_VV sg U (projVV sg F).2⟩) fun y hy => by
      rw [fockB_projVV sg _ hy, fockB_blockAct, fockB_blockAct, fockB_projVV sg _ (blockAct_mem_VV sg _ hy)]
  exact congrArg Subtype.val this

end Proj

theorem coeff_scale {A : Type} [CommRing A] [Fintype ι] (t : ι → A) (e : ι × Fin n →₀ ℕ) (P : MvPolynomial (ι × Fin n) A) :
    coeff e (aeval (fun p : ι × Fin n => C (t p.1) * X p) P : MvPolynomial (ι × Fin n) A) =
      (∏ p : ι × Fin n, t p.1 ^ e p) * coeff e P := by
  classical
  induction P using MvPolynomial.induction_on' with
  | add p q hp hq => simp only [map_add, coeff_add, hp, hq, mul_add]
  | monomial m a =>
    have : (aeval (fun p : ι × Fin n => C (t p.1) * X p) (monomial m a) : MvPolynomial (ι × Fin n) A) =
        C (∏ p : ι × Fin n, t p.1 ^ m p) * monomial m a := by
      rw [aeval_monomial, monomial_eq, Finsupp.prod_fintype _ _ (by simp), Finsupp.prod_fintype _ _ (by simp)]
      simp only [mul_pow, Finset.prod_mul_distrib, map_prod, map_pow, algebraMap_eq]
      ring
    rw [this, coeff_C_mul, coeff_monomial]
    split_ifs with h
    · rw [h]
    · simp

theorem splitLast_C (c : K) : splitLast K ι hN (C c : Pol K ι N) = C (C c) := by
  simp [algHom_C, MvPolynomial.algebraMap_apply]

theorem cases_idx (a : Fin N) : a = iL hN ∨ ∃ a', a = iC hN a' := by
  by_cases h : a.val < n
  · exact Or.inr ⟨⟨a.val, h⟩, rfl⟩
  · exact Or.inl (Fin.ext (by have := a.2; simp only [iL]; omega))

theorem splitLast_blockAct_X (A' : ι → Matrix (Fin N) (Fin N) K)
    (A : ι → Matrix (Fin n) (Fin n) K) (t : ι → K) (h : ∀ τ, IsBlock hN (A' τ) (A τ) (t τ)) (v : ι × Fin N × Fin N) :
    splitLast K ι hN (Formalism.GradedWeylDivisibility.blockAct K A' (X v)) =
      aeval (fun p : ι × Fin n => (C (C (t p.1)) * X p : MvPolynomial (ι × Fin n) (Pol K ι n)))
        (MvPolynomial.map (Formalism.GradedWeylDivisibility.blockAct K (n := n) A).toRingHom (splitLast K ι hN (X v))) := by
  obtain ⟨τ, a, s⟩ := v
  obtain ⟨h1, h2, h3⟩ := h τ
  have hX : ∀ {m : ℕ} (U : ι → Matrix (Fin m) (Fin m) K) (τ : ι) (a s : Fin m),
      Formalism.GradedWeylDivisibility.blockAct K U (X (τ, a, s)) = ∑ b, C (U τ a b) * X (τ, b, s) := fun U τ a s => aeval_X _ _
  rw [hX, map_sum, sum_split hN]
  simp only [map_mul, splitLast_C]
  rcases cases_idx hN s with rfl | ⟨s, rfl⟩
  · simp only [splitLast_X_lastCol, mul_zero, Finset.sum_const_zero, add_zero, map_zero]
  · rcases cases_idx hN a with rfl | ⟨a, rfl⟩
    · simp only [splitLast_X_up, splitLast_X_lastRow, (h2 _).2, h3, map_zero, zero_mul, Finset.sum_const_zero, zero_add,
        map_X, aeval_X]
    · simp only [splitLast_X_up, splitLast_X_lastRow, (h2 _).1, h1, map_zero, zero_mul, add_zero, map_C, algHom_C,
        algebraMap_eq, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hX, map_sum, map_mul]

theorem coefLast_blockAct [Fintype ι] (b : ι → Fin n → ℕ) (A' : ι → Matrix (Fin N) (Fin N) K)
    (A : ι → Matrix (Fin n) (Fin n) K) (t : ι → K) (h : ∀ τ, IsBlock hN (A' τ) (A τ) (t τ)) (F : Pol K ι N) :
    coefLast hN b (Formalism.GradedWeylDivisibility.blockAct K A' F) =
      (∏ τ, t τ ^ ∑ s, b τ s) • Formalism.GradedWeylDivisibility.blockAct K A (coefLast hN b F) := by
  have key : splitLast K ι hN (Formalism.GradedWeylDivisibility.blockAct K A' F) =
      aeval (fun p : ι × Fin n => (C (C (t p.1)) * X p : MvPolynomial (ι × Fin n) (Pol K ι n)))
        (MvPolynomial.map (Formalism.GradedWeylDivisibility.blockAct K (n := n) A).toRingHom (splitLast K ι hN F)) := by
    induction F using MvPolynomial.induction_on with
    | C a =>
      have e : ∀ {m : ℕ} (U : ι → Matrix (Fin m) (Fin m) K), Formalism.GradedWeylDivisibility.blockAct K (n := m) U (C a) = C a := fun U => algHom_C _ _
      rw [e, splitLast_C, map_C, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, e, algHom_C, algebraMap_eq]
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p v hp =>
      rw [map_mul, map_mul, hp, splitLast_blockAct_X K ι hN A' A t h, map_mul, map_mul, map_mul]
  rw [coefLast_eq_coeff, coefLast_eq_coeff, key, coeff_scale ι (fun τ => C (t τ)), coeff_map, smul_eq_C_mul,
    Fintype.prod_prod_type]
  simp only [Finset.prod_pow_eq_pow_sum, expOf_apply, map_prod, map_pow, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]

end GlobalTheory.BranchFormula
