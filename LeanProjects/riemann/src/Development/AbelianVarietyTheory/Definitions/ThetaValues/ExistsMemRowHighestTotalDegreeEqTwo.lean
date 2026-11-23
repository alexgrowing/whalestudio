import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsWeightedHomogeneousOfMemOrbitSpan
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsHarmonicProdOfDisjointColumns

open MvPolynomial Matrix

namespace GlobalTheory.Harm

variable {R S : Type*} [CommRing R] [CommRing S] {T : Type*} {p q n : ℕ} {κ κ' : Type*}

section RowAdd

variable [Fintype κ]

open Classical in

noncomputable def rowAdd (t : T) (r r' : Fin p ⊕ Fin q) (s : R) :
    Poly R T p q κ →ₐ[R] Poly R T p q κ :=
  bind₁ fun v => X v + ∑ k : κ, if v = (t, r', k) then C s * X (t, r, k) else 0

open Classical in

noncomputable def rowAddX (t : T) (a b : Fin p) (s : R) : Poly R T p q κ →ₐ[R] Poly R T p q κ :=
  bind₁ fun v => X v + ∑ k : κ, if v = xVar t b k then C s * X (xVar t a k) else 0

open Classical in

noncomputable def rowAddY (t : T) (a b : Fin q) (s : R) : Poly R T p q κ →ₐ[R] Poly R T p q κ :=
  bind₁ fun v => X v + ∑ k : κ, if v = yVar t b k then C s * X (yVar t a k) else 0

theorem rowAddX_eq_rowAdd (t : T) (a b : Fin p) (s : R) :
    (rowAddX t a b s : Poly R T p q κ →ₐ[R] _) = rowAdd t (Sum.inl a) (Sum.inl b) s := rfl

theorem rowAddY_eq_rowAdd (t : T) (a b : Fin q) (s : R) :
    (rowAddY t a b s : Poly R T p q κ →ₐ[R] _) = rowAdd t (Sum.inr a) (Sum.inr b) s := rfl

theorem rowAdd_eq_bind₁ [DecidableEq (Var T p q κ)] (t : T) (r r' : Fin p ⊕ Fin q) (s : R) :
    (rowAdd t r r' s : Poly R T p q κ →ₐ[R] _) =
      bind₁ fun v => X v + ∑ k : κ, if v = (t, r', k) then C s * X (t, r, k) else 0 := by
  unfold rowAdd; congr!

theorem rowAddX_eq_bind₁ [DecidableEq (Var T p q κ)] (t : T) (a b : Fin p) (s : R) :
    (rowAddX t a b s : Poly R T p q κ →ₐ[R] _) =
      bind₁ fun v => X v + ∑ k : κ, if v = xVar t b k then C s * X (xVar t a k) else 0 :=
  rowAdd_eq_bind₁ _ _ _ _

theorem rowAddY_eq_bind₁ [DecidableEq (Var T p q κ)] (t : T) (a b : Fin q) (s : R) :
    (rowAddY t a b s : Poly R T p q κ →ₐ[R] _) =
      bind₁ fun v => X v + ∑ k : κ, if v = yVar t b k then C s * X (yVar t a k) else 0 :=
  rowAdd_eq_bind₁ _ _ _ _

@[simp] theorem rowAdd_X_self (t : T) (r r' : Fin p ⊕ Fin q) (s : R) (k : κ) :
    rowAdd t r r' s (X (t, r', k)) = X (t, r', k) + C s * X (t, r, k) := by
  classical
  rw [rowAdd_eq_bind₁, bind₁_X_right, Finset.sum_eq_single k] <;> simp +contextual [eq_comm]

theorem rowAdd_X_of_ne {t t' : T} (r : Fin p ⊕ Fin q) {r' r'' : Fin p ⊕ Fin q} (s : R) (k : κ)
    (h : ¬ (t' = t ∧ r'' = r')) : rowAdd t r r' s (X (t', r'', k)) = X (t', r'', k) := by
  classical
  rw [rowAdd_eq_bind₁, bind₁_X_right, Finset.sum_eq_zero, add_zero]
  intro l _
  rw [if_neg]
  intro e; simp only [Prod.mk.injEq] at e; exact h ⟨e.1, e.2.1⟩

theorem rowAdd_X [DecidableEq T] (t t' : T) (r r' r'' : Fin p ⊕ Fin q) (s : R) (k : κ) :
    rowAdd t r r' s (X (t', r'', k)) =
      X (t', r'', k) + if t' = t ∧ r'' = r' then C s * X (t, r, k) else 0 := by
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h; exact rowAdd_X_self _ _ _ _ _
  · rw [rowAdd_X_of_ne _ _ _ h, add_zero]

@[simp] theorem rowAddX_X_self (t : T) (a b : Fin p) (s : R) (k : κ) :
    rowAddX t a b s (X (xVar t b k) : Poly R T p q κ) = X (xVar t b k) + C s * X (xVar t a k) :=
  rowAdd_X_self _ _ _ _ _

@[simp] theorem rowAddY_X_self (t : T) (a b : Fin q) (s : R) (k : κ) :
    rowAddY t a b s (X (yVar t b k) : Poly R T p q κ) = X (yVar t b k) + C s * X (yVar t a k) :=
  rowAdd_X_self _ _ _ _ _

theorem rowAddX_X_of_ne {t t' : T} (a : Fin p) {b b' : Fin p} (s : R) (k : κ)
    (h : ¬ (t' = t ∧ b' = b)) :
    rowAddX t a b s (X (xVar t' b' k) : Poly R T p q κ) = X (xVar t' b' k) :=
  rowAdd_X_of_ne _ _ _ (by simpa using h)

theorem rowAddY_X_of_ne {t t' : T} (a : Fin q) {b b' : Fin q} (s : R) (k : κ)
    (h : ¬ (t' = t ∧ b' = b)) :
    rowAddY t a b s (X (yVar t' b' k) : Poly R T p q κ) = X (yVar t' b' k) :=
  rowAdd_X_of_ne _ _ _ (by simpa using h)

@[simp] theorem rowAddX_X_yVar (t t' : T) (a b : Fin p) (b' : Fin q) (s : R) (k : κ) :
    rowAddX t a b s (X (yVar t' b' k) : Poly R T p q κ) = X (yVar t' b' k) :=
  rowAdd_X_of_ne _ _ _ (by simp)

@[simp] theorem rowAddY_X_xVar (t t' : T) (a b : Fin q) (b' : Fin p) (s : R) (k : κ) :
    rowAddY t a b s (X (xVar t' b' k) : Poly R T p q κ) = X (xVar t' b' k) :=
  rowAdd_X_of_ne _ _ _ (by simp)

theorem rowAdd_rowForm_self (t : T) (r r' : Fin p ⊕ Fin q) (s : R) (v : κ → R) :
    rowAdd t r r' s (rowForm t r' v) = rowForm t r' v + C s * rowForm t r v := by
  simp only [rowForm_apply, map_sum, map_mul, algHom_C, algebraMap_eq, rowAdd_X_self, mul_add,
    Finset.sum_add_distrib, Finset.mul_sum, mul_left_comm]

theorem rowAdd_rowForm_of_ne {t t' : T} (r : Fin p ⊕ Fin q) {r' r'' : Fin p ⊕ Fin q} (s : R)
    (v : κ → R) (h : ¬ (t' = t ∧ r'' = r')) :
    rowAdd t r r' s (rowForm t' r'' v) = rowForm t' r'' v := by
  simp only [rowForm_apply, map_sum, map_mul, algHom_C, algebraMap_eq, rowAdd_X_of_ne _ _ _ h]

@[simp] theorem rowAdd_zero (t : T) (r r' : Fin p ⊕ Fin q) :
    (rowAdd t r r' (0 : R) : Poly R T p q κ →ₐ[R] _) = AlgHom.id R _ := by
  classical
  refine MvPolynomial.algHom_ext fun ⟨t', r'', k⟩ => ?_
  simp [rowAdd_X]

theorem rowAdd_add (t : T) {r r' : Fin p ⊕ Fin q} (h : r ≠ r') (s s' : R) :
    (rowAdd t r r' (s + s') : Poly R T p q κ →ₐ[R] _) =
      (rowAdd t r r' s).comp (rowAdd t r r' s') := by
  refine MvPolynomial.algHom_ext fun ⟨t', r'', k⟩ => ?_
  by_cases e : t' = t ∧ r'' = r'
  · obtain ⟨rfl, rfl⟩ := e
    rw [AlgHom.comp_apply, rowAdd_X_self, rowAdd_X_self, map_add (rowAdd _ _ _ _), map_mul,
      rowAdd_X_self, rowAdd_X_of_ne _ _ _ (fun e => h e.2), algHom_C, algebraMap_eq, map_add]
    ring
  · rw [AlgHom.comp_apply, rowAdd_X_of_ne _ _ _ e, rowAdd_X_of_ne _ _ _ e, rowAdd_X_of_ne _ _ _ e]

theorem eval_rowAdd [DecidableEq T] (z : Var T p q κ → R) (t : T) (r r' : Fin p ⊕ Fin q) (s : R)
    (P : Poly R T p q κ) :
    eval z (rowAdd t r r' s P) =
      eval (fun v => z v + if v.1 = t ∧ v.2.1 = r' then s * z (t, r, v.2.2) else 0) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [algHom_C]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P v hP =>
    obtain ⟨t', r'', k⟩ := v
    rw [map_mul, map_mul, map_mul, hP, rowAdd_X, eval_X]
    split_ifs <;> simp

theorem map_rowAdd (f : R →+* S) (t : T) (r r' : Fin p ⊕ Fin q) (s : R) (P : Poly R T p q κ) :
    MvPolynomial.map f (rowAdd t r r' s P) = rowAdd t r r' (f s) (MvPolynomial.map f P) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C a => simp [algHom_C]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P v hP =>
    obtain ⟨t', r'', k⟩ := v
    rw [map_mul, map_mul, map_mul, map_mul, hP, map_X, rowAdd_X, rowAdd_X]
    split_ifs <;> simp

theorem rowAdd_colSubst [Fintype κ'] (A : T → Matrix κ κ' R) (B : T → Matrix κ' κ R) (t : T)
    {r r' : Fin p ⊕ Fin q} (h : r.isLeft = r'.isLeft) (s : R) (P : Poly R T p q κ) :
    rowAdd t r r' s (colSubst A B P) = colSubst A B (rowAdd t r r' s P) := by
  refine DFunLike.congr_fun (?_ : (rowAdd t r r' s).comp (colSubst A B) =
    (colSubst A B).comp (rowAdd t r r' s)) P
  refine MvPolynomial.algHom_ext fun ⟨t', r'', k⟩ => ?_
  rw [AlgHom.comp_apply, AlgHom.comp_apply]
  by_cases e : t' = t ∧ r'' = r'
  · obtain ⟨rfl, rfl⟩ := e
    rw [rowAdd_X_self, map_add, map_mul, algHom_C, algebraMap_eq]
    rcases r with a | a <;> rcases r'' with b | b
    · rw [colSubst_X_xVar, colSubst_X_xVar]; exact rowAdd_rowForm_self _ _ _ _ _
    · simp at h
    · simp at h
    · rw [colSubst_X_yVar, colSubst_X_yVar]; exact rowAdd_rowForm_self _ _ _ _ _
  · rw [rowAdd_X_of_ne _ _ _ e]
    rcases r'' with b | b
    · rw [colSubst_X_xVar]; exact rowAdd_rowForm_of_ne _ _ _ e
    · rw [colSubst_X_yVar]; exact rowAdd_rowForm_of_ne _ _ _ e

theorem rowAdd_det_rowForm {ι : Type*} [Fintype ι] [DecidableEq ι] (t t' : T)
    {r r' : Fin p ⊕ Fin q} (hr : r ≠ r') (s : R) {ρ : ι → Fin p ⊕ Fin q}
    (hρ : Function.Injective ρ) (h : r' ∈ Set.range ρ → r ∈ Set.range ρ) (v : ι → κ → R) :
    rowAdd t r r' s (Matrix.of fun a b => rowForm t' (ρ a) (v b)).det =
      (Matrix.of fun a b => rowForm t' (ρ a) (v b)).det := by
  rw [AlgHom.map_det]
  by_cases e : t' = t ∧ r' ∈ Set.range ρ
  · obtain ⟨rfl, j, rfl⟩ := e
    obtain ⟨i, rfl⟩ := h ⟨j, rfl⟩
    rw [← det_updateRow_add_smul_self (Matrix.of fun a b => rowForm t' (ρ a) (v b))
      (i := j) (j := i) (fun e => hr (by rw [e])) (C s)]
    congr 1
    ext1 a b
    by_cases ha : a = j
    · subst ha; simp [rowAdd_rowForm_self]
    · simp [updateRow_ne ha, rowAdd_rowForm_of_ne _ _ _ (fun e => ha (hρ e.2))]
  · congr 1
    ext1 a b
    exact rowAdd_rowForm_of_ne _ _ _ fun e' => e ⟨e'.1, a, e'.2⟩

theorem mem_range_lead_of_lt {m : ℕ} {i a b : Fin m} (h : a < b) (hb : b ∈ Set.range (lead i)) :
    a ∈ Set.range (lead i) := by
  obtain ⟨j, rfl⟩ := hb
  exact ⟨⟨a.val, lt_trans h j.isLt⟩, rfl⟩

def RowLT : Fin p ⊕ Fin q → Fin p ⊕ Fin q → Prop
  | Sum.inl a, Sum.inl b => a < b
  | Sum.inr a, Sum.inr b => a < b
  | _, _ => False

theorem RowLT.ne {r r' : Fin p ⊕ Fin q} (h : RowLT r r') : r ≠ r' := by
  rintro rfl; rcases r with a | a <;> exact lt_irrefl a h

theorem RowLT.isLeft_eq {r r' : Fin p ⊕ Fin q} (h : RowLT r r') : r.isLeft = r'.isLeft := by
  rcases r with a | a <;> rcases r' with b | b <;> first | rfl | exact h.elim

theorem rowAdd_det_xForm (t t' : T) {r r' : Fin p ⊕ Fin q} (h : RowLT r r') (s : R) (i : Fin p)
    (v : Fin (i.val + 1) → κ → R) :
    rowAdd t r r' s (Matrix.of fun a b => xForm t' (lead i a) (v b)).det =
      (Matrix.of fun a b => xForm t' (lead i a) (v b)).det := by
  refine rowAdd_det_rowForm t t' h.ne s (ρ := fun a => Sum.inl (lead i a))
    (Sum.inl_injective.comp (Fin.castLE_injective _)) ?_ v
  rintro ⟨j, rfl⟩
  rcases r with a | a
  · obtain ⟨l, rfl⟩ := mem_range_lead_of_lt (i := i) h ⟨j, rfl⟩
    exact ⟨l, rfl⟩
  · exact h.elim

theorem rowAdd_det_yForm (t t' : T) {r r' : Fin p ⊕ Fin q} (h : RowLT r r') (s : R) (i : Fin q)
    (v : Fin (i.val + 1) → κ → R) :
    rowAdd t r r' s (Matrix.of fun a b => yForm t' (lead i a) (v b)).det =
      (Matrix.of fun a b => yForm t' (lead i a) (v b)).det := by
  refine rowAdd_det_rowForm t t' h.ne s (ρ := fun a => Sum.inr (lead i a))
    (Sum.inr_injective.comp (Fin.castLE_injective _)) ?_ v
  rintro ⟨j, rfl⟩
  rcases r with a | a
  · exact h.elim
  · obtain ⟨l, rfl⟩ := mem_range_lead_of_lt (i := i) h ⟨j, rfl⟩
    exact ⟨l, rfl⟩

theorem rowAdd_minorProd [Fintype T] (t : T) {r r' : Fin p ⊕ Fin q} (h : RowLT r r') (s : R)
    (c : T → Fin p → ℕ) (c' : T → Fin q → ℕ) (ε : T → Fin p → κ → R) (φ : T → Fin q → κ → R) :
    rowAdd t r r' s (minorProd c c' ε φ) = minorProd c c' ε φ := by
  simp only [minorProd, map_prod, map_mul, map_pow, xMinor, yMinor, rowAdd_det_xForm t _ h,
    rowAdd_det_yForm t _ h]

theorem rowAdd_blockPoly [Fintype T] (t : T) {r r' : Fin p ⊕ Fin q} (h : RowLT r r') (s : R)
    (c : T → Fin p → ℕ) (c' : T → Fin q → ℕ) (col : T → (i : Fin p) → Fin (i.val + 1) → κ)
    (col' : T → (i : Fin q) → Fin (i.val + 1) → κ) :
    rowAdd t r r' s (blockPoly R c c' col col') = blockPoly R c c' col col' := by
  classical
  simp only [blockPoly, map_prod, map_mul, map_pow, ← xForm_single, ← yForm_single,
    rowAdd_det_xForm t _ h, rowAdd_det_yForm t _ h]

theorem rowAdd_eq_self_of_forall_int [IsDomain R] [CharZero R] {t : T} {r r' : Fin p ⊕ Fin q}
    {P : Poly R T p q κ} (h : ∀ s : ℤ, rowAdd t r r' (s : R) P = P) (s : R) :
    rowAdd t r r' s P = P := by
  classical
  let Φ : Poly R T p q κ →ₐ[R] Polynomial (Poly R T p q κ) := aeval fun v =>
    Polynomial.C (X v) + if v.1 = t ∧ v.2.1 = r' then
      Polynomial.C (X (t, r, v.2.2)) * Polynomial.X else 0
  have hΦ (s : R) (Q : Poly R T p q κ) : (Φ Q).eval (C s) = rowAdd t r r' s Q := by
    induction Q using MvPolynomial.induction_on with
    | C a => simp [Φ, algHom_C]
    | add P Q hP hQ => simp only [map_add, Polynomial.eval_add, hP, hQ]
    | mul_X P v hP =>
      obtain ⟨t', r'', k⟩ := v
      rw [map_mul, map_mul, Polynomial.eval_mul, hP, rowAdd_X]
      congr 1
      simp only [Φ, aeval_X]
      split_ifs
      · rw [mul_comm (C s)]; simp
      · simp
  have : Φ P = Polynomial.C P := by
    refine Polynomial.eq_of_infinite_eval_eq _ _ (Set.infinite_of_injective_forall_mem
      (f := fun s : ℤ => (C (s : R) : Poly R T p q κ))
      ((C_injective _ _).comp Int.cast_injective) fun s => ?_)
    rw [Set.mem_setOf_eq, hΦ, h, Polynomial.eval_C]
  rw [← hΦ, this, Polynomial.eval_C]

end RowAdd

section RowDegree

open Classical in

noncomputable def rowInd (t : T) (r : Fin p ⊕ Fin q) : Var T p q κ → ℕ :=
  rowWeight fun t' r' => if t' = t ∧ r' = r then 1 else 0

theorem rowInd_apply [DecidableEq T] (t : T) (r : Fin p ⊕ Fin q) (v : Var T p q κ) :
    rowInd t r v = if v.1 = t ∧ v.2.1 = r then 1 else 0 := by
  unfold rowInd rowWeight; congr!

variable [Fintype κ]

theorem weight_rowInd (t : T) (r : Fin p ⊕ Fin q) (m : Var T p q κ →₀ ℕ) :
    Finsupp.weight (rowInd t r) m = ∑ k : κ, m (t, r, k) := by
  classical
  induction m using Finsupp.induction_linear with
  | zero => simp
  | add m m' hm hm' => simp [hm, hm', Finset.sum_add_distrib]
  | single v d =>
    obtain ⟨t', r', k⟩ := v
    rw [Finsupp.weight_single, rowInd_apply]
    split_ifs with e
    · obtain ⟨rfl, rfl⟩ := e
      simp [Finsupp.single_apply]
    · rw [smul_zero, Finset.sum_eq_zero]
      intro l _
      rw [Finsupp.single_eq_of_ne]
      intro e'; simp only [Prod.mk.injEq] at e'; exact e ⟨e'.1.symm, e'.2.1.symm⟩

theorem isWeightedHomogeneous_rowInd_iff (t : T) (r : Fin p ⊕ Fin q) (P : Poly R T p q κ) (d : ℕ) :
    IsWeightedHomogeneous (rowInd t r) P d ↔ ∀ m ∈ P.support, ∑ k : κ, m (t, r, k) = d := by
  simp only [IsWeightedHomogeneous, weight_rowInd, mem_support_iff]

theorem weight_rowWeight [Fintype T] {M : Type*} [AddCommMonoid M] (w : T → Fin p ⊕ Fin q → M)
    (m : Var T p q κ →₀ ℕ) :
    Finsupp.weight (rowWeight w) m = ∑ t, ((∑ a, (∑ k, m (xVar t a k)) • w t (Sum.inl a)) +
      ∑ b, (∑ k, m (yVar t b k)) • w t (Sum.inr b)) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp only [Fintype.sum_prod_type, Fintype.sum_sum_type, rowWeight, Finset.sum_smul]

end RowDegree

section Space

variable [Fintype κ]

variable (R) in

noncomputable def rowHighest (c : T → Fin p → ℕ) (c' : T → Fin q → ℕ) :
    Submodule R (Poly R T p q κ) :=
  harmonicSubmodule R T p q κ ⊓
    ((⨅ (t : T) (a : Fin p),
        weightedHomogeneousSubmodule R (rowInd t (Sum.inl a)) (partOf (c t) a)) ⊓
      ⨅ (t : T) (b : Fin q),
        weightedHomogeneousSubmodule R (rowInd t (Sum.inr b)) (partOf (c' t) b)) ⊓
    ((⨅ (t : T) (a : Fin p) (b : Fin p) (_ : a < b) (s : ℤ),
        LinearMap.ker ((rowAddX t a b (s : R)).toLinearMap - LinearMap.id)) ⊓
      ⨅ (t : T) (a : Fin q) (b : Fin q) (_ : a < b) (s : ℤ),
        LinearMap.ker ((rowAddY t a b (s : R)).toLinearMap - LinearMap.id))

variable {c : T → Fin p → ℕ} {c' : T → Fin q → ℕ} {P : Poly R T p q κ}

theorem mem_rowHighest_iff : P ∈ rowHighest R c c' ↔ IsHarmonic P ∧
    (∀ t a, IsWeightedHomogeneous (rowInd t (Sum.inl a)) P (partOf (c t) a)) ∧
    (∀ t b, IsWeightedHomogeneous (rowInd t (Sum.inr b)) P (partOf (c' t) b)) ∧
    (∀ t a b, a < b → ∀ s : ℤ, rowAddX t a b (s : R) P = P) ∧
    ∀ t a b, a < b → ∀ s : ℤ, rowAddY t a b (s : R) P = P := by
  simp only [rowHighest, Submodule.mem_inf, Submodule.mem_iInf, mem_harmonicSubmodule,
    mem_weightedHomogeneousSubmodule, LinearMap.mem_ker, LinearMap.sub_apply,
    AlgHom.toLinearMap_apply, LinearMap.id_apply, sub_eq_zero, and_assoc]

theorem mem_rowHighest_iff_support : P ∈ rowHighest R c c' ↔ IsHarmonic P ∧
    (∀ t a, ∀ m ∈ P.support, ∑ k, m (xVar t a k) = partOf (c t) a) ∧
    (∀ t b, ∀ m ∈ P.support, ∑ k, m (yVar t b k) = partOf (c' t) b) ∧
    (∀ t a b, a < b → ∀ s : ℤ, rowAddX t a b (s : R) P = P) ∧
    ∀ t a b, a < b → ∀ s : ℤ, rowAddY t a b (s : R) P = P := by
  simp only [mem_rowHighest_iff, isWeightedHomogeneous_rowInd_iff]

theorem mem_rowHighest_iff_of_charZero [IsDomain R] [CharZero R] :
    P ∈ rowHighest R c c' ↔ IsHarmonic P ∧
    (∀ t a, ∀ m ∈ P.support, ∑ k, m (xVar t a k) = partOf (c t) a) ∧
    (∀ t b, ∀ m ∈ P.support, ∑ k, m (yVar t b k) = partOf (c' t) b) ∧
    (∀ t a b, a < b → ∀ s : R, rowAddX t a b s P = P) ∧
    ∀ t a b, a < b → ∀ s : R, rowAddY t a b s P = P := by
  rw [mem_rowHighest_iff_support]
  refine and_congr_right' (and_congr_right' (and_congr_right' (and_congr ?_ ?_)))
  · exact ⟨fun h t a b hab => rowAdd_eq_self_of_forall_int (h t a b hab),
      fun h t a b hab s => h t a b hab s⟩
  · exact ⟨fun h t a b hab => rowAdd_eq_self_of_forall_int (h t a b hab),
      fun h t a b hab s => h t a b hab s⟩

theorem mem_rowHighest_iff_rowAdd : P ∈ rowHighest R c c' ↔ IsHarmonic P ∧
    (∀ t r, IsWeightedHomogeneous (rowInd t r) P (Sum.elim (partOf (c t)) (partOf (c' t)) r)) ∧
    ∀ t r r', RowLT r r' → ∀ s : ℤ, rowAdd t r r' (s : R) P = P := by
  rw [mem_rowHighest_iff]
  refine ⟨fun ⟨h, h₁, h₂, h₃, h₄⟩ => ⟨h, ?_, ?_⟩, fun ⟨h, h₁, h₂⟩ =>
    ⟨h, fun t a => h₁ t _, fun t b => h₁ t _, fun t a b hab => h₂ t _ _ hab,
      fun t a b hab => h₂ t _ _ hab⟩⟩
  · rintro t (a | b)
    · exact h₁ t a
    · exact h₂ t b
  · rintro t (a | a) (b | b) hab
    · exact h₃ t a b hab
    · exact hab.elim
    · exact hab.elim
    · exact h₄ t a b hab

theorem isHarmonic_of_mem_rowHighest (hP : P ∈ rowHighest R c c') : IsHarmonic P :=
  (mem_rowHighest_iff.1 hP).1

theorem rowAddX_eq_self_of_mem_rowHighest [IsDomain R] [CharZero R] (hP : P ∈ rowHighest R c c')
    (t : T) {a b : Fin p} (hab : a < b) (s : R) : rowAddX t a b s P = P :=
  (mem_rowHighest_iff_of_charZero.1 hP).2.2.2.1 t a b hab s

theorem rowAddY_eq_self_of_mem_rowHighest [IsDomain R] [CharZero R] (hP : P ∈ rowHighest R c c')
    (t : T) {a b : Fin q} (hab : a < b) (s : R) : rowAddY t a b s P = P :=
  (mem_rowHighest_iff_of_charZero.1 hP).2.2.2.2 t a b hab s

variable (R c c') in

theorem rowHighest_le_harmonicSubmodule : rowHighest R c c' ≤ harmonicSubmodule R T p q κ :=
  fun _ => isHarmonic_of_mem_rowHighest

theorem isWeightedHomogeneous_of_mem_rowHighest [Fintype T] {M : Type*} [AddCommMonoid M]
    (w : T → Fin p ⊕ Fin q → M) (hP : P ∈ rowHighest R c c') :
    IsWeightedHomogeneous (rowWeight w) P
      (∑ t, ((∑ a, partOf (c t) a • w t (Sum.inl a)) + ∑ b, partOf (c' t) b • w t (Sum.inr b))) := by
  obtain ⟨-, h₁, h₂, -⟩ := mem_rowHighest_iff_support.1 hP
  intro m hm
  rw [weight_rowWeight]
  simp only [fun t a => h₁ t a m (mem_support_iff.2 hm), fun t a => h₂ t a m (mem_support_iff.2 hm)]

theorem isHomogeneous_of_mem_rowHighest [Fintype T] (hP : P ∈ rowHighest R c c') :
    P.IsHomogeneous (typeDegree c c') := by
  have := isWeightedHomogeneous_of_mem_rowHighest (fun _ _ => (1 : ℕ)) hP
  simp only [smul_eq_mul, mul_one, sum_partOf] at this
  exact this

variable (R c c') in

theorem rowHighest_le_homogeneousSubmodule [Fintype T] :
    rowHighest R c c' ≤ homogeneousSubmodule (Var T p q κ) R (typeDegree c c') :=
  fun _ => isHomogeneous_of_mem_rowHighest

instance finite_rowHighest [Finite T] [IsNoetherianRing R] :
    Module.Finite R (rowHighest R c c' : Submodule R (Poly R T p q κ)) := by
  cases nonempty_fintype T
  have : (rowHighest R c c' : Submodule R (Poly R T p q κ)) ≤
      restrictTotalDegree (Var T p q κ) R (typeDegree c c') := fun P hP =>
    (mem_restrictTotalDegree _ _ _).2 (isHomogeneous_of_mem_rowHighest hP).totalDegree_le
  exact Module.Finite.of_injective _ (Submodule.inclusion_injective this)

theorem mem_rowHighest_of_rowWeight [Fintype T] (h : IsHarmonic P)
    (hw : ∀ w : T → Fin p ⊕ Fin q → ℕ, IsWeightedHomogeneous (rowWeight w) P
      (∑ t, ((∑ a, partOf (c t) a • w t (Sum.inl a)) + ∑ b, partOf (c' t) b • w t (Sum.inr b))))
    (hr : ∀ t r r', RowLT r r' → ∀ s : ℤ, rowAdd t r r' (s : R) P = P) :
    P ∈ rowHighest R c c' := by
  classical
  refine mem_rowHighest_iff_rowAdd.2 ⟨h, fun t r => ?_, hr⟩
  have := hw fun t' r' => if t' = t ∧ r' = r then 1 else 0
  rw [Finset.sum_eq_single t (by simp +contextual) (by simp)] at this
  convert this using 1
  · funext v; rw [rowInd_apply]; rfl
  · rcases r with a | b <;> simp

variable (c c') in

theorem minorProd_mem_rowHighest [Fintype T] {ε : T → Fin p → κ → R} {φ : T → Fin q → κ → R}
    (h : IsPerp ε φ) : minorProd c c' ε φ ∈ rowHighest R c c' :=
  mem_rowHighest_of_rowWeight (isHarmonic_minorProd c c' h)
    (fun w => minorProd_isWeightedHomogeneous w c c' ε φ)
    fun t _ _ hr _ => rowAdd_minorProd t hr _ c c' ε φ

variable (c c') in

theorem blockPoly_mem_rowHighest [Fintype T] (col : T → (i : Fin p) → Fin (i.val + 1) → κ)
    (col' : T → (i : Fin q) → Fin (i.val + 1) → κ)
    (h : ∀ t i j a b, c t i ≠ 0 → c' t j ≠ 0 → col t i a ≠ col' t j b) :
    blockPoly R c c' col col' ∈ rowHighest R c c' :=
  mem_rowHighest_of_rowWeight (isHarmonic_blockPoly c c' col col' h)
    (fun w => blockPoly_isWeightedHomogeneous w c c' col col')
    fun t _ _ hr _ => rowAdd_blockPoly t hr _ c c' col col'

theorem colSubst_mem_rowHighest [Fintype κ'] [DecidableEq κ] {A : T → Matrix κ κ' R}
    {B : T → Matrix κ' κ R} (h : ∀ t, A t * B t = 1) (hP : P ∈ rowHighest R c c') :
    colSubst A B P ∈ rowHighest R c c' := by
  obtain ⟨h₁, h₂, h₃⟩ := mem_rowHighest_iff_rowAdd.1 hP
  exact mem_rowHighest_iff_rowAdd.2 ⟨h₁.colSubst h,
    fun t r => colSubst_isWeightedHomogeneous _ A B (h₂ t r),
    fun t r r' hr s => by rw [rowAdd_colSubst A B t hr.isLeft_eq, h₃ t r r' hr]⟩

theorem colAct_mem_rowHighest [DecidableEq κ] (g : T → GL κ R) (hP : P ∈ rowHighest R c c') :
    colAct R T p q κ g P ∈ rowHighest R c c' :=
  colSubst_mem_rowHighest (fun t => Units.inv_mul (g t)) hP

theorem colAct_mem_rowHighest_iff [DecidableEq κ] (g : T → GL κ R) :
    colAct R T p q κ g P ∈ rowHighest R c c' ↔ P ∈ rowHighest R c c' := by
  refine ⟨fun h => ?_, colAct_mem_rowHighest g⟩
  have := colAct_mem_rowHighest g⁻¹ h
  rwa [← AlgEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one, AlgEquiv.one_apply] at this

variable (R κ c c') in

noncomputable def rowHighestSubrep [DecidableEq κ] : Subrepresentation (colRep R T p q κ) where
  toSubmodule := rowHighest R c c'
  apply_mem_toSubmodule g _ hP := colAct_mem_rowHighest g hP

theorem map_mem_rowHighest (f : R →+* S) (hP : P ∈ rowHighest R c c') :
    MvPolynomial.map f P ∈ rowHighest S c c' := by
  obtain ⟨h₁, h₂, h₃⟩ := mem_rowHighest_iff_rowAdd.1 hP
  refine mem_rowHighest_iff_rowAdd.2 ⟨h₁.map f, fun t r m hm => h₂ t r fun e => hm ?_,
    fun t r r' hr s => by rw [← map_intCast f, ← map_rowAdd, h₃ t r r' hr]⟩
  rw [coeff_map, e, map_zero]

theorem map_mem_rowHighest_iff {f : R →+* S} (hf : Function.Injective f) :
    MvPolynomial.map f P ∈ rowHighest S c c' ↔ P ∈ rowHighest R c c' := by
  refine ⟨fun hP => ?_, map_mem_rowHighest f⟩
  obtain ⟨h₁, h₂, h₃⟩ := mem_rowHighest_iff_rowAdd.1 hP
  refine mem_rowHighest_iff_rowAdd.2 ⟨(isHarmonic_map_iff hf).1 h₁,
    fun t r m hm => h₂ t r fun e => hm (hf ?_),
    fun t r r' hr s => map_injective f hf (by rw [map_rowAdd, map_intCast, h₃ t r r' hr])⟩
  rw [← coeff_map, e, map_zero]

end Space

section Base

variable [Fintype T] (h : p + q ≤ n) (c : T → Fin p → ℕ) (c' : T → Fin q → ℕ)

theorem basePoly_mem_rowHighest : basePoly R h c c' ∈ rowHighest R c c' :=
  minorProd_mem_rowHighest c c' (isPerp_base R T h)

theorem orbitSpan_le_rowHighest : orbitSpan R h c c' ≤ rowHighest R c c' := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨g, rfl⟩
  exact colAct_mem_rowHighest g (basePoly_mem_rowHighest h c c')

include h in

theorem rowHighest_ne_bot [Nontrivial R] :
    (rowHighest R c c' : Submodule R (Poly R T p q (Fin n))) ≠ ⊥ := fun e =>
  basePoly_ne_zero h c c' (by simpa [e] using basePoly_mem_rowHighest (R := R) h c c')

end Base

theorem exists_mem_rowHighest_totalDegree_eq_two :
    ∃ P ∈ rowHighest ℤ (fun (_ : Unit) (_ : Fin 1) => 1) (fun _ (_ : Fin 1) => 1),
      P = (X (xVar () 0 0) * X (yVar () 0 1) : Poly ℤ Unit 1 1 (Fin 2)) ∧ P.totalDegree = 2 :=
  ⟨_, basePoly_mem_rowHighest (show 1 + 1 ≤ 2 from le_rfl) _ _,
    by simp [basePoly, minorProd, xMinor, yMinor, baseCovec, baseVec],
    by rw [totalDegree_basePoly]; decide⟩

example : (X (xVar () 0 0) * X (yVar () 0 0) : Poly ℤ Unit 1 1 (Fin 2)) ∉
    rowHighest ℤ (fun _ _ => 1) (fun _ _ => 1) := fun hP => by
  have := isHarmonic_of_mem_rowHighest hP () 0 0
  simp only [← xForm_single, ← yForm_single, laplacian_xForm_mul_yForm] at this
  simp at this

example : (X (xVar () 0 0) * X (xVar () 1 1) - X (xVar () 0 1) * X (xVar () 1 0) :
    Poly ℤ Unit 2 0 (Fin 2)) ∈ rowHighest ℤ (fun _ => ![0, 1]) (fun _ _ => 0) := by
  have : (xMinor () 1 (baseCovec ℤ (show 2 + 0 ≤ 2 from le_rfl)) : Poly ℤ Unit 2 0 (Fin 2)) =
      X (xVar () 0 0) * X (xVar () 1 1) - X (xVar () 0 1) * X (xVar () 1 0) := by
    refine (det_fin_two _).trans ?_
    simp only [baseCovec, of_apply, xForm_single]; rfl
  simpa [basePoly, minorProd, this] using basePoly_mem_rowHighest (R := ℤ)
    (show 2 + 0 ≤ 2 from le_rfl) (fun _ : Unit => ![0, 1]) (fun _ _ => 0)

example : (X (xVar () 0 0) * X (xVar () 1 0) : Poly ℤ Unit 2 0 (Fin 2)) ∉
    rowHighest ℤ (fun _ => ![0, 1]) (fun _ _ => 0) := fun hP => by
  have := (mem_rowHighest_iff.1 hP).2.2.2.1 () 0 1 (by decide) 1
  rw [map_mul, rowAddX_X_self, rowAddX_X_of_ne _ _ _ (by decide), mul_add] at this
  simp at this

example (k : Fin n) : (X (xVar () 0 k) : Poly ℤ Unit 2 0 (Fin n)) ∈
    rowHighest ℤ (fun _ => ![1, 0]) (fun _ _ => 0) := by
  simpa [minorProd, xMinor] using minorProd_mem_rowHighest (R := ℤ) (fun _ : Unit => ![1, 0])
    (fun _ (_ : Fin 0) => 0) (ε := fun _ _ => Pi.single k 1) (φ := fun _ _ => 0)
    fun _ _ b => b.elim0

example : (X (yVar () 0 0) * X (yVar () 1 0) : Poly ℤ Unit 0 2 (Fin 2)) ∉
    rowHighest ℤ (fun _ _ => 0) (fun _ => ![0, 1]) := fun hP => by
  have := (mem_rowHighest_iff.1 hP).2.2.2.2 () 0 1 (by decide) 1
  rw [map_mul, rowAddY_X_self, rowAddY_X_of_ne _ _ _ (by decide), mul_add] at this
  simp at this

example : (X (xVar () 0 0) : Poly ℤ Unit 1 1 (Fin 2)) ∉
    rowHighest ℤ (fun _ _ => 2) (fun _ _ => 0) := fun hP => by
  have := (isHomogeneous_of_mem_rowHighest hP).totalDegree (X_ne_zero _)
  rw [totalDegree_X] at this
  revert this; decide

end GlobalTheory.Harm
