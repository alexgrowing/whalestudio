import Mathlib

namespace GlobalTheory

open Finsupp

section Words

variable {R : Type*} [CommRing R] {Λ : Type*} {B : Type*} [Ring B] [Algebra R B]

def opWord (D : Λ → B) (w : List Λ) : B := (w.map D).prod

@[simp] theorem opWord_nil (D : Λ → B) : opWord D [] = 1 := rfl

@[simp] theorem opWord_cons (D : Λ → B) (l : Λ) (w : List Λ) :
    opWord D (l :: w) = D l * opWord D w := by simp [opWord]

theorem opWord_append (D : Λ → B) (w w' : List Λ) :
    opWord D (w ++ w') = opWord D w * opWord D w' := by simp [opWord]

theorem opWord_perm {D : Λ → B} (hD : ∀ l l', Commute (D l) (D l')) {w w' : List Λ}
    (h : w.Perm w') : opWord D w = opWord D w' := by
  induction h with
  | nil => rfl
  | cons l _ ih => simp [ih]
  | swap l l' w => simp only [opWord_cons, ← mul_assoc, (hD l l').eq]
  | trans _ _ h₁ h₂ => exact h₁.trans h₂

def IsOrderingRule (ord : (Λ →₀ ℕ) → List Λ) : Prop :=
  ∀ α, (ord α : Multiset Λ) = Finsupp.toMultiset α

theorem isOrderingRule_toList :
    IsOrderingRule (fun α : Λ →₀ ℕ => (Finsupp.toMultiset α).toList) :=
  fun _ => Multiset.coe_toList _

theorem IsOrderingRule.length_eq {ord : (Λ →₀ ℕ) → List Λ} (h : IsOrderingRule ord)
    (α : Λ →₀ ℕ) : (ord α).length = degree α := by
  rw [← Multiset.coe_card, h α, Finsupp.card_toMultiset]
  rfl

noncomputable def opPoly (D : Λ → B) (ord : (Λ →₀ ℕ) → List Λ) : MvPolynomial Λ R →ₗ[R] B :=
  (MvPolynomial.basisMonomials Λ R).constr R (fun α => opWord D (ord α))

theorem opPoly_monomial (D : Λ → B) (ord : (Λ →₀ ℕ) → List Λ) (α : Λ →₀ ℕ) (c : R) :
    opPoly D ord (MvPolynomial.monomial α c) = c • opWord D (ord α) := by
  have h : MvPolynomial.monomial α c = c • MvPolynomial.basisMonomials Λ R α := by
    simp [MvPolynomial.smul_monomial]
  rw [h, map_smul, opPoly, Module.Basis.constr_basis]

theorem opPoly_mul_of_commute {D : Λ → B} (hD : ∀ l l', Commute (D l) (D l'))
    {ord : (Λ →₀ ℕ) → List Λ} (h : IsOrderingRule ord) (P Q : MvPolynomial Λ R) :
    opPoly D ord (P * Q) = opPoly D ord P * opPoly D ord Q := by
  induction P using MvPolynomial.induction_on' with
  | add p q hp hq => simp only [add_mul, map_add, hp, hq]
  | monomial α a =>
    induction Q using MvPolynomial.induction_on' with
    | add p q hp hq => simp only [mul_add, map_add, hp, hq]
    | monomial β b =>
      have hp : (ord (α + β)).Perm (ord α ++ ord β) := by
        rw [← Multiset.coe_eq_coe, ← Multiset.coe_add, h, h, h, map_add]
      rw [MvPolynomial.monomial_mul, opPoly_monomial, opPoly_monomial, opPoly_monomial,
        opWord_perm hD hp, opWord_append, smul_mul_smul_comm]

theorem IsOrderingRule.ord_zero {ord : (Λ →₀ ℕ) → List Λ} (h : IsOrderingRule ord) :
    ord 0 = [] := by
  have := h 0
  simpa using this

theorem IsOrderingRule.ord_single {ord : (Λ →₀ ℕ) → List Λ} (h : IsOrderingRule ord) (l : Λ) :
    ord (single l 1) = [l] := by
  have := h (single l 1)
  rw [Finsupp.toMultiset_single, one_smul] at this
  exact List.perm_singleton.mp (Multiset.coe_eq_coe.mp this)

theorem opPoly_C (D : Λ → B) {ord : (Λ →₀ ℕ) → List Λ} (h : IsOrderingRule ord) (c : R) :
    opPoly D ord (MvPolynomial.C c) = algebraMap R B c := by
  rw [MvPolynomial.C_apply, opPoly_monomial, h.ord_zero, opWord_nil, Algebra.algebraMap_eq_smul_one]

theorem opPoly_X (D : Λ → B) {ord : (Λ →₀ ℕ) → List Λ} (h : IsOrderingRule ord) (l : Λ) :
    opPoly D ord (MvPolynomial.X l : MvPolynomial Λ R) = D l := by
  rw [MvPolynomial.X, opPoly_monomial, h.ord_single]
  simp

noncomputable def commEval (D : Λ → B) (hD : ∀ l l', Commute (D l) (D l')) :
    MvPolynomial Λ R →ₐ[R] B :=
  AlgHom.ofLinearMap (opPoly D fun α => (Finsupp.toMultiset α).toList)
    (by rw [← MvPolynomial.C_1, opPoly_C D isOrderingRule_toList, map_one])
    (opPoly_mul_of_commute hD isOrderingRule_toList)

@[simp] theorem commEval_X (D : Λ → B) (hD : ∀ l l', Commute (D l) (D l')) (l : Λ) :
    commEval D hD (MvPolynomial.X l : MvPolynomial Λ R) = D l :=
  opPoly_X D isOrderingRule_toList l

end Words

section General

variable {R A M Λ : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module R M] [Module A M]

end General

section Constant

open MvPolynomial

variable {R σ Λ : Type*} [CommRing R]

noncomputable def constDeriv (v : σ → R) : Derivation R (MvPolynomial σ R) (MvPolynomial σ R) :=
  mkDerivation R fun i => C (v i)

@[simp] theorem constDeriv_X (v : σ → R) (i : σ) : constDeriv v (X i) = C (v i) :=
  mkDerivation_X _ _ _

theorem constDeriv_single [DecidableEq σ] (i : σ) :
    constDeriv (Pi.single i (1 : R)) = pderiv i := by
  refine derivation_ext fun j => ?_
  rw [constDeriv_X, pderiv_X]
  by_cases h : j = i
  · subst h; simp
  · simp [h]

theorem constDeriv_commute (v v' : σ → R) :
    Commute ((constDeriv v).toLinearMap : Module.End R (MvPolynomial σ R))
      (constDeriv v').toLinearMap := by
  have h : ⁅constDeriv v, constDeriv v'⁆ = 0 :=
    derivation_ext fun j => by simp [Derivation.commutator_apply]
  refine LinearMap.ext fun p => ?_
  have := congrArg (fun D : Derivation R (MvPolynomial σ R) (MvPolynomial σ R) => D p) h
  simpa [Derivation.commutator_apply, sub_eq_zero] using this

theorem pderiv_commute (i j : σ) :
    Commute ((pderiv i).toLinearMap : Module.End R (MvPolynomial σ R)) (pderiv j).toLinearMap := by
  classical
  rw [← constDeriv_single, ← constDeriv_single]
  exact constDeriv_commute _ _

noncomputable def pderivEval : MvPolynomial σ R →ₐ[R] Module.End R (MvPolynomial σ R) :=
  commEval (fun i => (pderiv i).toLinearMap) pderiv_commute

@[simp] theorem pderivEval_X (i : σ) :
    pderivEval (X i : MvPolynomial σ R) = (pderiv i).toLinearMap := commEval_X _ _ i

noncomputable def constDerivEval (v : Λ → σ → R) :
    MvPolynomial Λ R →ₐ[R] Module.End R (MvPolynomial σ R) :=
  commEval (fun l => (constDeriv (v l)).toLinearMap) fun _ _ => constDeriv_commute _ _

@[simp] theorem constDerivEval_X (v : Λ → σ → R) (l : Λ) :
    constDerivEval v (X l) = (constDeriv (v l)).toLinearMap := commEval_X _ _ l

def multiFactorial (α : σ →₀ ℕ) : ℕ := α.prod fun _ n => n.factorial

end Constant

section Series

open MvPowerSeries

variable {R σ Λ M : Type*} [CommRing R]

noncomputable abbrev germIdeal (σ R : Type*) [CommRing R] : Ideal (MvPowerSeries σ R) :=
  RingHom.ker (constantCoeff : MvPowerSeries σ R →+* R)

theorem X_mem_germIdeal (i : σ) : (X i : MvPowerSeries σ R) ∈ germIdeal σ R := by
  simp [RingHom.mem_ker]

theorem exists_eq_sum_X_mul [Fintype σ] {n : ℕ} {g : MvPowerSeries σ R}
    (hg : ∀ d : σ →₀ ℕ, degree d < n + 1 → coeff d g = 0) :
    ∃ h : σ → MvPowerSeries σ R, (∀ i (d : σ →₀ ℕ), degree d < n → coeff d (h i) = 0) ∧
      g = ∑ i, X i * h i := by
  classical
  have hidx : ∀ d : σ →₀ ℕ, d ≠ 0 → ∃ i, d i ≠ 0 := fun d hd => by
    by_contra hc
    push Not at hc
    exact hd (Finsupp.ext hc)
  choose idx hidx using hidx
  let part : σ → MvPowerSeries σ R := fun i d =>
    if hd : d ≠ 0 then (if idx d hd = i then coeff d g else 0) else 0
  have hpart : ∀ i d, coeff d (part i) =
      if hd : d ≠ 0 then (if idx d hd = i then coeff d g else 0) else 0 := fun _ _ => rfl
  have hdvd : ∀ i, (X i : MvPowerSeries σ R) ∣ part i := fun i => by
    rw [X_dvd_iff]
    intro d hd
    rw [hpart]
    split_ifs with h₁ h₂
    · exact absurd hd (h₂ ▸ hidx d h₁)
    · rfl
    · rfl
  choose h hh using hdvd
  refine ⟨h, fun i d hd => ?_, ?_⟩
  · have h₁ : coeff (single i 1 + d) (part i) = coeff d (h i) := by
      rw [hh, X_def, coeff_add_monomial_mul, one_mul]
    rw [← h₁, hpart]
    have h₂ : coeff (single i 1 + d) g = 0 := hg _ (by simp; omega)
    simp [h₂]
  · ext d
    simp only [← hh, map_sum, hpart]
    by_cases hd : d = 0
    · subst hd
      simpa using hg 0 (by simp)
    · simp [hd]

theorem germIdeal_eq_span [Finite σ] :
    germIdeal σ R = Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) := by
  cases nonempty_fintype σ
  refine le_antisymm (fun g hg => ?_) (Ideal.span_le.mpr ?_)
  · obtain ⟨h, -, rfl⟩ := exists_eq_sum_X_mul (n := 0) (g := g) fun d hd => by
      obtain rfl : d = 0 := by simpa [degree_eq_zero_iff] using hd
      simpa using hg
    exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, rfl⟩)
  · rintro _ ⟨i, rfl⟩
    exact X_mem_germIdeal i

theorem mem_germIdeal_pow_iff [Finite σ] {n : ℕ} {g : MvPowerSeries σ R} :
    g ∈ germIdeal σ R ^ n ↔ ∀ d : σ →₀ ℕ, degree d < n → coeff d g = 0 := by
  cases nonempty_fintype σ
  constructor
  · intro hg
    suffices h : (n : ℕ∞) ≤ g.order from fun d hd =>
      coeff_of_lt_order (lt_of_lt_of_le (by exact_mod_cast hd) h)
    induction n generalizing g with
    | zero => simp
    | succ n ih =>
      rw [pow_succ] at hg
      refine Submodule.mul_induction_on hg (fun a ha b hb => ?_) (fun a b ha hb => ?_)
      · refine le_trans ?_ le_order_mul
        push_cast
        refine add_le_add (ih ha) ?_
        exact_mod_cast nat_le_order (n := 1) fun d hd => by
          obtain rfl : d = 0 := by simpa [degree_eq_zero_iff] using hd
          simpa using hb
      · exact (le_min ha hb).trans min_order_le_add
  · induction n generalizing g with
    | zero => simp
    | succ n ih =>
      intro hg
      obtain ⟨h, hh, rfl⟩ := exists_eq_sum_X_mul hg
      rw [pow_succ']
      exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_mul (X_mem_germIdeal i) (ih (hh i))

theorem mem_germIdeal_pow_iff_le_order [Finite σ] {n : ℕ} {g : MvPowerSeries σ R} :
    g ∈ germIdeal σ R ^ n ↔ (n : ℕ∞) ≤ g.order := by
  rw [mem_germIdeal_pow_iff]
  exact ⟨nat_le_order, fun h d hd => coeff_of_lt_order (lt_of_lt_of_le (by exact_mod_cast hd) h)⟩

variable [Finite σ]

noncomputable def leadingForm (N : ℕ) : MvPowerSeries σ R →ₗ[R] MvPolynomial σ R :=
  MvPolynomial.homogeneousComponent N ∘ₗ truncTotal (N + 1)

noncomputable def derivAtOrigin (D : Derivation R (MvPowerSeries σ R) (MvPowerSeries σ R)) :
    σ → R := fun i => constantCoeff (D (X i))

end Series

section Symbol

open MvPowerSeries

variable {R σ Λ M : Type*} [CommRing R] [Finite σ] [AddCommGroup M] [Module R M]
  [Module (MvPowerSeries σ R) M]

variable [IsScalarTower R (MvPowerSeries σ R) M]

end Symbol

section Example

open MvPowerSeries

end Example

section Legendre

variable {l : ℕ} [hl : Fact l.Prime]

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

end Legendre

end GlobalTheory
