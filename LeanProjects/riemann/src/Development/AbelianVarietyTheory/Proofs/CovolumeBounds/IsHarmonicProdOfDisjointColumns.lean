import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsWeightedHomogeneousOfMemOrbitSpan

open MvPolynomial Matrix

namespace GlobalTheory.Harm

variable {R : Type*} [CommRing R] {T : Type*} {p q n : ℕ} {κ κ' : Type*}

section Cross

variable [Fintype κ]

noncomputable def cross (t : T) (a : Fin p) (b : Fin q) (P Q : Poly R T p q κ) : Poly R T p q κ :=
  ∑ k : κ, pderiv (xVar t a k) P * pderiv (yVar t b k) Q

theorem laplacian_mul (t : T) (a : Fin p) (b : Fin q) (P Q : Poly R T p q κ) :
    laplacian t a b (P * Q) =
      laplacian t a b P * Q + P * laplacian t a b Q + cross t a b P Q + cross t a b Q P := by
  simp only [laplacian_apply, cross, pderiv_mul, map_add, Finset.sum_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem cross_add_left (t : T) (a : Fin p) (b : Fin q) (P P' Q : Poly R T p q κ) :
    cross t a b (P + P') Q = cross t a b P Q + cross t a b P' Q := by
  simp only [cross, map_add, add_mul, Finset.sum_add_distrib]

theorem cross_add_right (t : T) (a : Fin p) (b : Fin q) (P Q Q' : Poly R T p q κ) :
    cross t a b P (Q + Q') = cross t a b P Q + cross t a b P Q' := by
  simp only [cross, map_add, mul_add, Finset.sum_add_distrib]

theorem cross_mul_left (t : T) (a : Fin p) (b : Fin q) (P P' Q : Poly R T p q κ) :
    cross t a b (P * P') Q = cross t a b P Q * P' + P * cross t a b P' Q := by
  simp only [cross, pderiv_mul, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem cross_mul_right (t : T) (a : Fin p) (b : Fin q) (P Q Q' : Poly R T p q κ) :
    cross t a b P (Q * Q') = cross t a b P Q * Q' + Q * cross t a b P Q' := by
  simp only [cross, pderiv_mul, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

@[simp] theorem cross_C_left (t : T) (a : Fin p) (b : Fin q) (r : R) (Q : Poly R T p q κ) :
    cross t a b (C r) Q = 0 := by simp [cross]

@[simp] theorem cross_C_right (t : T) (a : Fin p) (b : Fin q) (r : R) (P : Poly R T p q κ) :
    cross t a b P (C r) = 0 := by simp [cross]

theorem IsHarmonic.mul_of_cross {P Q : Poly R T p q κ} (hP : IsHarmonic P) (hQ : IsHarmonic Q)
    (h : ∀ t a b, cross t a b P Q = 0) (h' : ∀ t a b, cross t a b Q P = 0) :
    IsHarmonic (P * Q) := fun t a b => by
  rw [laplacian_mul, hP, hQ, h, h']; simp

theorem cross_eq_zero_of_mem_adjoin (t : T) (a : Fin p) (b : Fin q) {s s' : Set (Poly R T p q κ)}
    (h : ∀ u ∈ s, ∀ v ∈ s', cross t a b u v = 0) {P Q : Poly R T p q κ}
    (hP : P ∈ Algebra.adjoin R s) (hQ : Q ∈ Algebra.adjoin R s') : cross t a b P Q = 0 := by
  induction hP using Algebra.adjoin_induction with
  | mem u hu =>
    induction hQ using Algebra.adjoin_induction with
    | mem v hv => exact h u hu v hv
    | algebraMap r => exact cross_C_right _ _ _ _ _
    | add x y _ _ hx hy => rw [cross_add_right, hx, hy, add_zero]
    | mul x y _ _ hx hy => rw [cross_mul_right, hx, hy, zero_mul, mul_zero, add_zero]
  | algebraMap r => exact cross_C_left _ _ _ _ _
  | add x y _ _ hx hy => rw [cross_add_left, hx, hy, add_zero]
  | mul x y _ _ hx hy => rw [cross_mul_left, hx, hy, zero_mul, mul_zero, add_zero]

theorem isHarmonic_of_mem_adjoin {s : Set (Poly R T p q κ)} (hs : ∀ u ∈ s, IsHarmonic u)
    (h : ∀ t a b, ∀ u ∈ s, ∀ v ∈ s, cross t a b u v = 0) {P : Poly R T p q κ}
    (hP : P ∈ Algebra.adjoin R s) : IsHarmonic P := by
  induction hP using Algebra.adjoin_induction with
  | mem u hu => exact hs u hu
  | algebraMap r => exact isHarmonic_C r
  | add x y _ _ hx hy => exact (harmonicSubmodule R T p q κ).add_mem hx hy
  | mul x y hx' hy' hx hy =>
    exact hx.mul_of_cross hy (fun t a b => cross_eq_zero_of_mem_adjoin t a b (h t a b) hx' hy')
      fun t a b => cross_eq_zero_of_mem_adjoin t a b (h t a b) hy' hx'

theorem pderiv_rowForm [DecidableEq T] (t t' : T) (r r' : Fin p ⊕ Fin q) (k : κ) (v : κ → R) :
    pderiv (t, r, k) (rowForm t' r' v : Poly R T p q κ) =
      if t' = t ∧ r' = r then C (v k) else 0 := by
  classical
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h
    simp [rowForm_apply, pderiv_X, Pi.single_apply]
  · rw [rowForm_apply, map_sum]
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [pderiv_C_mul, pderiv_X_of_ne, mul_zero]
    intro e
    simp only [Prod.mk.injEq] at e
    exact h ⟨e.1, e.2.1⟩

theorem isHarmonic_rowForm (t : T) (r : Fin p ⊕ Fin q) (v : κ → R) :
    IsHarmonic (rowForm t r v : Poly R T p q κ) := fun t' a b => by
  classical
  rw [laplacian_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [pderiv_rowForm]; split_ifs <;> simp

theorem cross_rowForm [DecidableEq T] (t t₁ t₂ : T) (a : Fin p) (b : Fin q)
    (r₁ r₂ : Fin p ⊕ Fin q) (v w : κ → R) :
    cross t a b (rowForm t₁ r₁ v) (rowForm t₂ r₂ w : Poly R T p q κ) =
      if (t₁ = t ∧ r₁ = Sum.inl a) ∧ t₂ = t ∧ r₂ = Sum.inr b then C (v ⬝ᵥ w) else 0 := by
  simp only [cross, pderiv_rowForm]
  by_cases h₁ : t₁ = t ∧ r₁ = Sum.inl a <;> by_cases h₂ : t₂ = t ∧ r₂ = Sum.inr b <;>
    simp [h₁, h₂, dotProduct]

end Cross

section Perp

variable [Fintype κ] {ι ι' : Type*}

def formSet (ε : T → ι → κ → R) (φ : T → ι' → κ → R) : Set (Poly R T p q κ) :=
  {u | ∃ t a c, u = xForm t a (ε t c)} ∪ {u | ∃ t b d, u = yForm t b (φ t d)}

theorem isHarmonic_of_mem_adjoin_formSet {ε : T → ι → κ → R} {φ : T → ι' → κ → R}
    (h : ∀ t c d, ε t c ⬝ᵥ φ t d = 0) {P : Poly R T p q κ}
    (hP : P ∈ Algebra.adjoin R (formSet ε φ)) : IsHarmonic P := by
  classical
  refine isHarmonic_of_mem_adjoin ?_ ?_ hP
  · rintro _ (⟨t, a, c, rfl⟩ | ⟨t, a, c, rfl⟩) <;> exact isHarmonic_rowForm _ _ _
  · rintro t a b _ (⟨t₁, a₁, c₁, rfl⟩ | ⟨t₁, a₁, c₁, rfl⟩) _ (⟨t₂, a₂, c₂, rfl⟩ | ⟨t₂, a₂, c₂, rfl⟩)
    · rw [xForm, xForm, cross_rowForm, if_neg (by simp)]
    · rw [xForm, yForm, cross_rowForm]
      split_ifs with e
      · obtain ⟨⟨rfl, -⟩, rfl, -⟩ := e
        rw [h, map_zero]
      · rfl
    · rw [yForm, xForm, cross_rowForm, if_neg (by simp)]
    · rw [yForm, yForm, cross_rowForm, if_neg (by simp)]

theorem det_mem_of_forall_mem {A σ m : Type*} [CommRing A] [SetLike σ A] [SubringClass σ A]
    [Fintype m] [DecidableEq m] (s : σ) (M : Matrix m m A) (h : ∀ i j, M i j ∈ s) : M.det ∈ s := by
  rw [det_apply']
  exact sum_mem fun e _ => mul_mem (intCast_mem _ _) (prod_mem fun i _ => h _ _)

theorem minorProd_mem_closure [Fintype T] (c : T → Fin p → ℕ) (c' : T → Fin q → ℕ)
    (ε : T → Fin p → κ → R) (φ : T → Fin q → κ → R) :
    minorProd c c' ε φ ∈ Subring.closure (formSet ε φ) := by
  refine prod_mem fun t _ => mul_mem (prod_mem fun i _ => pow_mem ?_ _)
    (prod_mem fun i _ => pow_mem ?_ _)
  · exact det_mem_of_forall_mem _ _ fun a b => Subring.subset_closure (Or.inl ⟨_, _, _, rfl⟩)
  · exact det_mem_of_forall_mem _ _ fun a b => Subring.subset_closure (Or.inr ⟨_, _, _, rfl⟩)

theorem isHarmonic_minorProd [Fintype T] (c : T → Fin p → ℕ) (c' : T → Fin q → ℕ)
    {ε : T → Fin p → κ → R} {φ : T → Fin q → κ → R} (h : IsPerp ε φ) :
    IsHarmonic (minorProd c c' ε φ) :=
  isHarmonic_of_mem_adjoin_formSet h
    (Subring.closure_le (t := (Algebra.adjoin R (formSet ε φ)).toSubring).2 Algebra.subset_adjoin
      (minorProd_mem_closure c c' ε φ))

end Perp

section Columns

variable [Fintype κ]

theorem isHarmonic_of_mem_supported {s : Set (Var T p q κ)}
    (h : ∀ t a b k, xVar t a k ∈ s → yVar t b k ∉ s) {P : Poly R T p q κ}
    (hP : P ∈ supported R s) : IsHarmonic P := by
  classical
  refine isHarmonic_of_mem_adjoin ?_ ?_ hP
  · rintro _ ⟨⟨t, r, k⟩, -, rfl⟩
    rw [← rowForm_single]; exact isHarmonic_rowForm _ _ _
  · rintro t a b _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases e : u = xVar t a k
    · have : v ≠ yVar t b k := fun e' => h t a b k (e ▸ hu) (e' ▸ hv)
      rw [pderiv_X_of_ne this, mul_zero]
    · rw [pderiv_X_of_ne e, zero_mul]

end Columns

noncomputable def blockPoly (R : Type*) [CommRing R] [Fintype T] (c : T → Fin p → ℕ)
    (c' : T → Fin q → ℕ) (col : T → (i : Fin p) → Fin (i.val + 1) → κ)
    (col' : T → (i : Fin q) → Fin (i.val + 1) → κ) : Poly R T p q κ :=
  ∏ t : T, ((∏ i : Fin p, (Matrix.of fun a b : Fin (i.val + 1) =>
      (X (xVar t (lead i a) (col t i b)) : Poly R T p q κ)).det ^ c t i) *
    ∏ i : Fin q, (Matrix.of fun a b : Fin (i.val + 1) =>
      (X (yVar t (lead i a) (col' t i b)) : Poly R T p q κ)).det ^ c' t i)

theorem isHarmonic_blockPoly [Fintype κ] [Fintype T] (c : T → Fin p → ℕ) (c' : T → Fin q → ℕ)
    (col : T → (i : Fin p) → Fin (i.val + 1) → κ) (col' : T → (i : Fin q) → Fin (i.val + 1) → κ)
    (h : ∀ t i j a b, c t i ≠ 0 → c' t j ≠ 0 → col t i a ≠ col' t j b) :
    IsHarmonic (blockPoly R c c' col col') := by
  refine isHarmonic_of_mem_supported
    (s := {v | ∃ t r i a, c t i ≠ 0 ∧ v = xVar t r (col t i a)} ∪
      {v | ∃ t r i a, c' t i ≠ 0 ∧ v = yVar t r (col' t i a)}) ?_ ?_
  · rintro t a b k (⟨t₁, r₁, i₁, a₁, h₁, e₁⟩ | ⟨t₁, r₁, i₁, a₁, h₁, e₁⟩)
      (⟨t₂, r₂, i₂, a₂, h₂, e₂⟩ | ⟨t₂, r₂, i₂, a₂, h₂, e₂⟩) <;>
      simp only [Prod.mk.injEq, reduceCtorEq, false_and, and_false] at e₁ e₂
    obtain ⟨rfl, -, e₁⟩ := e₁
    obtain ⟨rfl, -, e₂⟩ := e₂
    exact h _ _ _ _ _ h₁ h₂ (e₁.symm.trans e₂)
  · refine prod_mem fun t _ => mul_mem (prod_mem fun i _ => ?_) (prod_mem fun i _ => ?_)
    · by_cases hc : c t i = 0
      · rw [hc, pow_zero]; exact one_mem _
      · refine pow_mem (det_mem_of_forall_mem _ _ fun a b => ?_) _
        exact Algebra.subset_adjoin (Set.mem_image_of_mem X (Or.inl ⟨_, _, _, _, hc, rfl⟩))
    · by_cases hc : c' t i = 0
      · rw [hc, pow_zero]; exact one_mem _
      · refine pow_mem (det_mem_of_forall_mem _ _ fun a b => ?_) _
        exact Algebra.subset_adjoin (Set.mem_image_of_mem X (Or.inr ⟨_, _, _, _, hc, rfl⟩))

theorem blockPoly_isWeightedHomogeneous [Fintype T] {M : Type*} [AddCommMonoid M]
    (w : T → Fin p ⊕ Fin q → M) (c : T → Fin p → ℕ) (c' : T → Fin q → ℕ)
    (col : T → (i : Fin p) → Fin (i.val + 1) → κ) (col' : T → (i : Fin q) → Fin (i.val + 1) → κ) :
    IsWeightedHomogeneous (rowWeight w) (blockPoly R c c' col col')
      (∑ t, ((∑ a, partOf (c t) a • w t (Sum.inl a)) + ∑ b, partOf (c' t) b • w t (Sum.inr b))) := by
  refine IsWeightedHomogeneous.prod _ _ _ fun t _ => ?_
  rw [← sum_smul_sum_lead, ← sum_smul_sum_lead]
  refine IsWeightedHomogeneous.mul ?_ ?_
  · refine IsWeightedHomogeneous.prod _ _ _ fun i _ => IsWeightedHomogeneous.pow ?_ _
    exact det_isWeightedHomogeneous _ _ _ fun a b => isWeightedHomogeneous_X R (rowWeight w) _
  · refine IsWeightedHomogeneous.prod _ _ _ fun i _ => IsWeightedHomogeneous.pow ?_ _
    exact det_isWeightedHomogeneous _ _ _ fun a b => isWeightedHomogeneous_X R (rowWeight w) _

theorem exists_eval_blockPoly_eq_one [Fintype T] (c : T → Fin p → ℕ) (c' : T → Fin q → ℕ)
    (col : T → (i : Fin p) → Fin (i.val + 1) → κ) (col' : T → (i : Fin q) → Fin (i.val + 1) → κ)
    (h : ∀ t i j a b, c t i ≠ 0 → c t j ≠ 0 → col t i a = col t j b → a.val = b.val)
    (h' : ∀ t i j a b, c' t i ≠ 0 → c' t j ≠ 0 → col' t i a = col' t j b → a.val = b.val) :
    ∃ z : Var T p q κ → R, (∀ v, z v = 0 ∨ z v = 1) ∧ eval z (blockPoly R c c' col col') = 1 := by
  classical
  refine ⟨fun v => match v with
    | (t, Sum.inl r, k) => if ∃ i a, c t i ≠ 0 ∧ col t i a = k ∧ a.val = r.val then 1 else 0
    | (t, Sum.inr r, k) => if ∃ i a, c' t i ≠ 0 ∧ col' t i a = k ∧ a.val = r.val then 1 else 0,
    ?_, ?_⟩
  · rintro ⟨t, r | r, k⟩ <;> dsimp only <;> split_ifs <;> simp
  simp only [blockPoly, map_prod, map_mul, map_pow]
  refine Finset.prod_eq_one fun t _ => ?_
  rw [Finset.prod_eq_one, Finset.prod_eq_one, mul_one]
  · intro i _
    by_cases hc : c' t i = 0
    · rw [hc, pow_zero]
    rw [RingHom.map_det]
    refine (congrArg (fun A => det A ^ c' t i) (?_ : _ = (1 : Matrix _ _ R))).trans (by simp)
    ext a b
    simp only [RingHom.mapMatrix_apply, map_apply, of_apply, eval_X, Matrix.one_apply]
    refine if_congr ⟨?_, ?_⟩ rfl rfl
    · rintro ⟨j, a', hj, e, e'⟩
      exact Fin.ext (e'.symm.trans (h' _ _ _ _ _ hj hc e))
    · rintro rfl; exact ⟨i, a, hc, rfl, rfl⟩
  · intro i _
    by_cases hc : c t i = 0
    · rw [hc, pow_zero]
    rw [RingHom.map_det]
    refine (congrArg (fun A => det A ^ c t i) (?_ : _ = (1 : Matrix _ _ R))).trans (by simp)
    ext a b
    simp only [RingHom.mapMatrix_apply, map_apply, of_apply, eval_X, Matrix.one_apply]
    refine if_congr ⟨?_, ?_⟩ rfl rfl
    · rintro ⟨j, a', hj, e, e'⟩
      exact Fin.ext (e'.symm.trans (h _ _ _ _ _ hj hc e))
    · rintro rfl; exact ⟨i, a, hc, rfl, rfl⟩

theorem blockPoly_ne_zero [Fintype T] [Nontrivial R] (c : T → Fin p → ℕ) (c' : T → Fin q → ℕ)
    (col : T → (i : Fin p) → Fin (i.val + 1) → κ) (col' : T → (i : Fin q) → Fin (i.val + 1) → κ)
    (h : ∀ t i j a b, c t i ≠ 0 → c t j ≠ 0 → col t i a = col t j b → a.val = b.val)
    (h' : ∀ t i j a b, c' t i ≠ 0 → c' t j ≠ 0 → col' t i a = col' t j b → a.val = b.val) :
    blockPoly R c c' col col' ≠ 0 := fun e => by
  obtain ⟨z, -, hz⟩ := exists_eval_blockPoly_eq_one (R := R) c c' col col' h h'
  rw [e, map_zero] at hz
  exact zero_ne_one hz

section Subst

variable [Fintype κ] [Fintype κ']

theorem pderiv_xVar_colSubst (A : T → Matrix κ κ' R) (B : T → Matrix κ' κ R) (t : T) (a : Fin p)
    (l : κ') (P : Poly R T p q κ) :
    pderiv (xVar t a l) (colSubst A B P) =
      ∑ k : κ, A t k l • colSubst A B (pderiv (xVar t a k) P) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C r => simp [algHom_C]
  | add P Q hP hQ => simp only [map_add, hP, hQ, smul_add, Finset.sum_add_distrib]
  | mul_X P v hP =>
    have : pderiv (xVar t a l) (colSubst A B (X v : Poly R T p q κ)) =
        ∑ k : κ, A t k l • colSubst A B (pderiv (xVar t a k) (X v : Poly R T p q κ)) := by
      obtain ⟨t', a' | b', k'⟩ := v
      · rw [colSubst_X_xVar, xForm, pderiv_rowForm]
        split_ifs with e
        · obtain ⟨rfl, e⟩ := e
          obtain rfl := Sum.inl_injective e
          rw [Finset.sum_eq_single k']
          · simp [smul_eq_C_mul]
          · intro k _ hk
            rw [pderiv_X_of_ne (by simp [hk.symm]), map_zero, smul_zero]
          · simp
        · refine (Finset.sum_eq_zero fun k _ => ?_).symm
          rw [pderiv_X_of_ne, map_zero, smul_zero]
          intro e'; simp only [Prod.mk.injEq] at e'; exact e ⟨e'.1, e'.2.1⟩
      · rw [colSubst_X_yVar, yForm, pderiv_rowForm, if_neg (by simp)]
        refine (Finset.sum_eq_zero fun k _ => ?_).symm
        rw [pderiv_X_of_ne (by simp), map_zero, smul_zero]
    simp only [map_mul, pderiv_mul, map_add, hP, this, smul_add, Finset.sum_add_distrib,
      Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm]

theorem pderiv_yVar_colSubst (A : T → Matrix κ κ' R) (B : T → Matrix κ' κ R) (t : T) (b : Fin q)
    (l : κ') (P : Poly R T p q κ) :
    pderiv (yVar t b l) (colSubst A B P) =
      ∑ k : κ, B t l k • colSubst A B (pderiv (yVar t b k) P) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C r => simp [algHom_C]
  | add P Q hP hQ => simp only [map_add, hP, hQ, smul_add, Finset.sum_add_distrib]
  | mul_X P v hP =>
    have : pderiv (yVar t b l) (colSubst A B (X v : Poly R T p q κ)) =
        ∑ k : κ, B t l k • colSubst A B (pderiv (yVar t b k) (X v : Poly R T p q κ)) := by
      obtain ⟨t', a' | b', k'⟩ := v
      · rw [colSubst_X_xVar, xForm, pderiv_rowForm, if_neg (by simp)]
        refine (Finset.sum_eq_zero fun k _ => ?_).symm
        rw [pderiv_X_of_ne (by simp), map_zero, smul_zero]
      · rw [colSubst_X_yVar, yForm, pderiv_rowForm]
        split_ifs with e
        · obtain ⟨rfl, e⟩ := e
          obtain rfl := Sum.inr_injective e
          rw [Finset.sum_eq_single k']
          · simp [smul_eq_C_mul]
          · intro k _ hk
            rw [pderiv_X_of_ne (by simp [hk.symm]), map_zero, smul_zero]
          · simp
        · refine (Finset.sum_eq_zero fun k _ => ?_).symm
          rw [pderiv_X_of_ne, map_zero, smul_zero]
          intro e'; simp only [Prod.mk.injEq] at e'; exact e ⟨e'.1, e'.2.1⟩
    simp only [map_mul, pderiv_mul, map_add, hP, this, smul_add, Finset.sum_add_distrib,
      Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm]

theorem laplacian_colSubst (A : T → Matrix κ κ' R) (B : T → Matrix κ' κ R) (t : T) (a : Fin p)
    (b : Fin q) (P : Poly R T p q κ) :
    laplacian t a b (colSubst A B P) = ∑ k : κ, ∑ k' : κ, (A t * B t) k k' •
      colSubst A B (pderiv (xVar t a k) (pderiv (yVar t b k') P)) := by
  simp only [laplacian_apply, pderiv_yVar_colSubst, map_sum, Derivation.map_smul,
    pderiv_xVar_colSubst, Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k' _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by rw [mul_comm]

theorem laplacian_colSubst_of_mul_eq_one [DecidableEq κ] (A : T → Matrix κ κ' R)
    (B : T → Matrix κ' κ R) {t : T} (h : A t * B t = 1) (a : Fin p) (b : Fin q)
    (P : Poly R T p q κ) :
    laplacian t a b (colSubst A B P) = colSubst A B (laplacian t a b P) := by
  rw [laplacian_colSubst, h, laplacian_apply, map_sum]
  simp [Matrix.one_apply]

theorem IsHarmonic.colSubst [DecidableEq κ] {A : T → Matrix κ κ' R} {B : T → Matrix κ' κ R}
    (h : ∀ t, A t * B t = 1) {P : Poly R T p q κ} (hP : IsHarmonic P) :
    IsHarmonic (colSubst A B P) := fun t a b => by
  rw [laplacian_colSubst_of_mul_eq_one A B (h t), hP, map_zero]

end Subst

section Action

variable [Fintype κ] [DecidableEq κ]

theorem laplacian_colAct (g : T → GL κ R) (t : T) (a : Fin p) (b : Fin q) (P : Poly R T p q κ) :
    laplacian t a b (colAct R T p q κ g P) = colAct R T p q κ g (laplacian t a b P) :=
  laplacian_colSubst_of_mul_eq_one _ _ (Units.inv_mul (g t)) a b P

theorem IsHarmonic.colAct (g : T → GL κ R) {P : Poly R T p q κ} (hP : IsHarmonic P) :
    IsHarmonic (colAct R T p q κ g P) := fun t a b => by
  rw [laplacian_colAct, hP, map_zero]

variable (R T p q κ) in

noncomputable def harmonicSubrep : Subrepresentation (colRep R T p q κ) where
  toSubmodule := harmonicSubmodule R T p q κ
  apply_mem_toSubmodule g _ hP := IsHarmonic.colAct g hP

end Action

example : blockPoly ℤ (fun (_ : Unit) (_ : Fin 1) => 2) (fun _ (_ : Fin 1) => 1)
    (fun _ _ _ => (0 : Fin 2)) (fun _ _ _ => 1) = X (xVar () 0 0) ^ 2 * X (yVar () 0 1) := by
  simp [blockPoly]

end GlobalTheory.Harm
