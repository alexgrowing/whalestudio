import Mathlib

open MvPolynomial Matrix

namespace GlobalTheory.Harm

abbrev Var (T : Type*) (p q : ℕ) (κ : Type*) := T × (Fin p ⊕ Fin q) × κ

abbrev Poly (R : Type*) [CommRing R] (T : Type*) (p q : ℕ) (κ : Type*) :=
  MvPolynomial (Var T p q κ) R

variable {R S : Type*} [CommRing R] [CommRing S] {T : Type*} {p q n : ℕ} {κ κ' κ'' : Type*}

abbrev xVar (t : T) (a : Fin p) (k : κ) : Var T p q κ := (t, Sum.inl a, k)

abbrev yVar (t : T) (b : Fin q) (k : κ) : Var T p q κ := (t, Sum.inr b, k)

section Laplacian

variable [Fintype κ]

noncomputable def laplacian (t : T) (a : Fin p) (b : Fin q) : Module.End R (Poly R T p q κ) :=
  ∑ k : κ, (pderiv (xVar t a k)).toLinearMap ∘ₗ (pderiv (yVar t b k)).toLinearMap

theorem laplacian_apply (t : T) (a : Fin p) (b : Fin q) (P : Poly R T p q κ) :
    laplacian t a b P = ∑ k : κ, pderiv (xVar t a k) (pderiv (yVar t b k) P) := by
  simp [laplacian, LinearMap.sum_apply]

def IsHarmonic (P : Poly R T p q κ) : Prop := ∀ t a b, laplacian t a b P = 0

variable (R T p q κ) in

def harmonicSubmodule : Submodule R (Poly R T p q κ) where
  carrier := {P | IsHarmonic P}
  add_mem' hP hQ t a b := by rw [map_add, hP, hQ, add_zero]
  zero_mem' t a b := map_zero _
  smul_mem' r P hP t a b := by rw [map_smul, hP, smul_zero]

@[simp] theorem mem_harmonicSubmodule {P : Poly R T p q κ} :
    P ∈ harmonicSubmodule R T p q κ ↔ IsHarmonic P := Iff.rfl

theorem isHarmonic_C (r : R) : IsHarmonic (C r : Poly R T p q κ) := fun t a b => by
  simp [laplacian_apply]

theorem map_laplacian (f : R →+* S) (t : T) (a : Fin p) (b : Fin q) (P : Poly R T p q κ) :
    MvPolynomial.map f (laplacian t a b P) = laplacian t a b (MvPolynomial.map f P) := by
  simp [laplacian_apply, pderiv_map]

theorem IsHarmonic.map (f : R →+* S) {P : Poly R T p q κ} (hP : IsHarmonic P) :
    IsHarmonic (MvPolynomial.map f P) := fun t a b => by
  rw [← map_laplacian, hP, map_zero]

theorem isHarmonic_map_iff {f : R →+* S} (hf : Function.Injective f) {P : Poly R T p q κ} :
    IsHarmonic (MvPolynomial.map f P) ↔ IsHarmonic P :=
  ⟨fun h t a b => MvPolynomial.map_injective f hf (by rw [map_laplacian, h, map_zero]),
    fun h => h.map f⟩

end Laplacian

section Forms

variable [Fintype κ]

noncomputable def rowForm (t : T) (r : Fin p ⊕ Fin q) : (κ → R) →ₗ[R] Poly R T p q κ where
  toFun v := ∑ k : κ, C (v k) * X (t, r, k)
  map_add' v w := by simp [add_mul, Finset.sum_add_distrib]
  map_smul' c v := by simp [Finset.mul_sum, smul_eq_C_mul, mul_assoc]

noncomputable def xForm (t : T) (a : Fin p) : (κ → R) →ₗ[R] Poly R T p q κ :=
  rowForm t (Sum.inl a)

noncomputable def yForm (t : T) (b : Fin q) : (κ → R) →ₗ[R] Poly R T p q κ :=
  rowForm t (Sum.inr b)

theorem rowForm_apply (t : T) (r : Fin p ⊕ Fin q) (v : κ → R) :
    rowForm t r v = ∑ k : κ, C (v k) * X (t, r, k) := rfl

theorem xForm_apply (t : T) (a : Fin p) (ε : κ → R) :
    (xForm t a ε : Poly R T p q κ) = ∑ k : κ, C (ε k) * X (xVar t a k) := rfl

theorem yForm_apply (t : T) (b : Fin q) (φ : κ → R) :
    (yForm t b φ : Poly R T p q κ) = ∑ k : κ, C (φ k) * X (yVar t b k) := rfl

theorem rowForm_single [DecidableEq κ] (t : T) (r : Fin p ⊕ Fin q) (k : κ) :
    (rowForm t r (Pi.single k 1) : Poly R T p q κ) = X (t, r, k) := by
  rw [rowForm_apply, Finset.sum_eq_single k] <;> simp +contextual [Pi.single_apply]

@[simp] theorem xForm_single [DecidableEq κ] (t : T) (a : Fin p) (k : κ) :
    (xForm t a (Pi.single k 1) : Poly R T p q κ) = X (xVar t a k) := rowForm_single _ _ _

@[simp] theorem yForm_single [DecidableEq κ] (t : T) (b : Fin q) (k : κ) :
    (yForm t b (Pi.single k 1) : Poly R T p q κ) = X (yVar t b k) := rowForm_single _ _ _

theorem eval_xForm (z : Var T p q κ → R) (t : T) (a : Fin p) (ε : κ → R) :
    eval z (xForm t a ε) = ε ⬝ᵥ fun k => z (xVar t a k) := by
  simp [xForm_apply, dotProduct]

theorem eval_yForm (z : Var T p q κ → R) (t : T) (b : Fin q) (φ : κ → R) :
    eval z (yForm t b φ) = φ ⬝ᵥ fun k => z (yVar t b k) := by
  simp [yForm_apply, dotProduct]

abbrev lead {m : ℕ} (i : Fin m) : Fin (i.val + 1) → Fin m := Fin.castLE i.isLt

noncomputable def xMinor (t : T) (i : Fin p) (ε : Fin p → κ → R) : Poly R T p q κ :=
  (Matrix.of fun a b : Fin (i.val + 1) => xForm t (lead i a) (ε (lead i b))).det

noncomputable def yMinor (t : T) (i : Fin q) (φ : Fin q → κ → R) : Poly R T p q κ :=
  (Matrix.of fun a b : Fin (i.val + 1) => yForm t (lead i a) (φ (lead i b))).det

noncomputable def minorProd [Fintype T] (c : T → Fin p → ℕ) (c' : T → Fin q → ℕ)
    (ε : T → Fin p → κ → R) (φ : T → Fin q → κ → R) : Poly R T p q κ :=
  ∏ t : T, ((∏ i : Fin p, xMinor t i (ε t) ^ c t i) * ∏ i : Fin q, yMinor t i (φ t) ^ c' t i)

def IsPerp (ε : T → Fin p → κ → R) (φ : T → Fin q → κ → R) : Prop :=
  ∀ t a b, ε t a ⬝ᵥ φ t b = 0

theorem laplacian_xForm_mul_yForm (t : T) (a : Fin p) (b : Fin q) (ε φ : κ → R) :
    laplacian t a b (xForm t a ε * yForm t b φ : Poly R T p q κ) = C (ε ⬝ᵥ φ) := by
  classical
  have h1 (k : κ) : pderiv (yVar t b k) (xForm t a ε : Poly R T p q κ) = 0 := by
    simp [xForm_apply, pderiv_X, Pi.single_apply]
  have h2 (k : κ) : pderiv (yVar t b k) (yForm t b φ : Poly R T p q κ) = C (φ k) := by
    simp [yForm_apply, pderiv_X, Pi.single_apply]
  have h3 (k : κ) : pderiv (xVar t a k) (xForm t a ε : Poly R T p q κ) = C (ε k) := by
    simp [xForm_apply, pderiv_X, Pi.single_apply]
  simp [laplacian_apply, h1, h2, h3, dotProduct, mul_comm]

theorem map_rowForm (f : R →+* S) (t : T) (r : Fin p ⊕ Fin q) (v : κ → R) :
    MvPolynomial.map f (rowForm t r v) = rowForm t r (f ∘ v) := by
  simp [rowForm_apply]

theorem map_xForm (f : R →+* S) (t : T) (a : Fin p) (ε : κ → R) :
    MvPolynomial.map f (xForm t a ε : Poly R T p q κ) = xForm t a (f ∘ ε) := map_rowForm _ _ _ _

theorem map_yForm (f : R →+* S) (t : T) (b : Fin q) (φ : κ → R) :
    MvPolynomial.map f (yForm t b φ : Poly R T p q κ) = yForm t b (f ∘ φ) := map_rowForm _ _ _ _

theorem ringHom_xMinor [Fintype κ'] (F : Poly R T p q κ →+* Poly S T p q κ') (t : T) (i : Fin p)
    (ε : Fin p → κ → R) (ε' : Fin p → κ' → S)
    (h : ∀ a b, F (xForm t a (ε b)) = xForm t a (ε' b)) : F (xMinor t i ε) = xMinor t i ε' := by
  rw [xMinor, RingHom.map_det]; congr 1; ext1 a b; exact h _ _

theorem ringHom_yMinor [Fintype κ'] (F : Poly R T p q κ →+* Poly S T p q κ') (t : T) (i : Fin q)
    (φ : Fin q → κ → R) (φ' : Fin q → κ' → S)
    (h : ∀ a b, F (yForm t a (φ b)) = yForm t a (φ' b)) : F (yMinor t i φ) = yMinor t i φ' := by
  rw [yMinor, RingHom.map_det]; congr 1; ext1 a b; exact h _ _

theorem map_minorProd [Fintype T] (f : R →+* S) (c : T → Fin p → ℕ) (c' : T → Fin q → ℕ)
    (ε : T → Fin p → κ → R) (φ : T → Fin q → κ → R) :
    MvPolynomial.map f (minorProd c c' ε φ) =
      minorProd c c' (fun t a => f ∘ ε t a) (fun t b => f ∘ φ t b) := by
  simp only [minorProd, map_prod, map_mul, map_pow]
  refine Finset.prod_congr rfl fun t _ => ?_
  congr 1
  · exact Finset.prod_congr rfl fun i _ => by
      rw [ringHom_xMinor _ t i (ε t) (fun a => f ∘ ε t a) fun a b => map_xForm _ _ _ _]
  · exact Finset.prod_congr rfl fun i _ => by
      rw [ringHom_yMinor _ t i (φ t) (fun a => f ∘ φ t a) fun a b => map_yForm _ _ _ _]

theorem IsPerp.map (f : R →+* S) {ε : T → Fin p → κ → R} {φ : T → Fin q → κ → R}
    (h : IsPerp ε φ) : IsPerp (fun t a => f ∘ ε t a) (fun t b => f ∘ φ t b) := fun t a b => by
  have := congrArg f (h t a b)
  simpa [dotProduct] using this

end Forms

section Degree

def partOf {m : ℕ} (c : Fin m → ℕ) (a : Fin m) : ℕ := ∑ i ∈ Finset.Ici a, c i

def partSize {m : ℕ} (c : Fin m → ℕ) : ℕ := ∑ i : Fin m, (i.val + 1) * c i

def typeDegree [Fintype T] (c : T → Fin p → ℕ) (c' : T → Fin q → ℕ) : ℕ :=
  ∑ t : T, (partSize (c t) + partSize (c' t))

theorem partOf_antitone {m : ℕ} (c : Fin m → ℕ) : Antitone (partOf c) := fun _ _ h =>
  Finset.sum_le_sum_of_subset (Finset.Ici_subset_Ici.mpr h)

theorem sum_smul_sum_lead {M : Type*} [AddCommMonoid M] {m : ℕ} (c : Fin m → ℕ) (w : Fin m → M) :
    ∑ i : Fin m, c i • ∑ a : Fin (i.val + 1), w (lead i a) = ∑ a : Fin m, partOf c a • w a := by
  have h (i : Fin m) : ∑ a : Fin (i.val + 1), w (lead i a) = ∑ a ∈ Finset.Iic i, w a := by
    refine Finset.sum_bij (fun a _ => lead i a) ?_ ?_ ?_ ?_
    · intro a _; simpa [Fin.le_def] using Nat.lt_succ_iff.mp a.isLt
    · intro a _ b _ h; exact Fin.castLE_injective _ h
    · intro b hb
      exact ⟨⟨b.val, Nat.lt_succ_iff.mpr (Fin.le_def.mp (Finset.mem_Iic.mp hb))⟩, Finset.mem_univ _, rfl⟩
    · intros; rfl
  simp only [h, partOf, Finset.smul_sum, Finset.sum_smul]
  exact Finset.sum_comm' (by simp)

theorem sum_partOf {m : ℕ} (c : Fin m → ℕ) : ∑ a, partOf c a = partSize c := by
  have := sum_smul_sum_lead c (fun _ => (1 : ℕ))
  simp only [smul_eq_mul, mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin] at this
  rw [← this, partSize]; exact Finset.sum_congr rfl fun i _ => mul_comm _ _

def diffOf {m : ℕ} (l : Fin m → ℕ) (i : Fin m) : ℕ :=
  l i - if h : i.val + 1 < m then l ⟨i.val + 1, h⟩ else 0

theorem partOf_eq_add {m : ℕ} (c : Fin m → ℕ) (i : Fin m) :
    partOf c i = c i + if h : i.val + 1 < m then partOf c ⟨i.val + 1, h⟩ else 0 := by
  rw [partOf, ← Finset.Ioi_insert, Finset.sum_insert (by simp)]
  congr 1
  split_ifs with h
  · rw [partOf]; congr 1; ext j
    rw [Finset.mem_Ioi, Finset.mem_Ici, Fin.lt_def, Fin.le_def]; exact Iff.rfl
  · rw [Finset.sum_eq_zero]; intro j hj
    have := j.isLt; rw [Finset.mem_Ioi, Fin.lt_def] at hj; omega

theorem partOf_diffOf {m : ℕ} {l : Fin m → ℕ} (hl : Antitone l) : partOf (diffOf l) = l := by
  funext i
  obtain ⟨i, hi⟩ := i
  induction' hd : m - i with d ih generalizing i
  · omega
  · rw [partOf_eq_add, diffOf]
    split_ifs with h
    · rw [ih (i + 1) h (by omega)]
      exact Nat.sub_add_cancel (hl (by simp [Fin.le_def]))
    · simp

variable [Fintype κ] {M : Type*} [AddCommMonoid M]

def rowWeight (w : T → Fin p ⊕ Fin q → M) : Var T p q κ → M := fun v => w v.1 v.2.1

theorem rowForm_isWeightedHomogeneous (w : T → Fin p ⊕ Fin q → M) (t : T) (r : Fin p ⊕ Fin q)
    (v : κ → R) : IsWeightedHomogeneous (rowWeight w) (rowForm t r v) (w t r) :=
  IsWeightedHomogeneous.sum _ _ _ fun k _ =>
    (isWeightedHomogeneous_X R (rowWeight w) (t, r, k)).C_mul _

theorem det_isWeightedHomogeneous {σ ι : Type*} [Fintype ι] [DecidableEq ι] (w : σ → M)
    (A : Matrix ι ι (MvPolynomial σ R)) (u : ι → M)
    (h : ∀ a b, IsWeightedHomogeneous w (A a b) (u a)) :
    IsWeightedHomogeneous w A.det (∑ a, u a) := by
  rw [det_apply]
  refine IsWeightedHomogeneous.sum _ _ _ fun s _ => ?_
  have h1 := IsWeightedHomogeneous.prod Finset.univ (fun i => A (s i) i) (fun i => u (s i))
    fun i _ => h _ _
  rw [Equiv.sum_comp s u] at h1
  rcases Int.units_eq_one_or (Equiv.Perm.sign s) with e | e
  · simpa [e] using h1
  · simpa [e] using h1.neg

theorem minorProd_isWeightedHomogeneous [Fintype T] (w : T → Fin p ⊕ Fin q → M)
    (c : T → Fin p → ℕ) (c' : T → Fin q → ℕ) (ε : T → Fin p → κ → R) (φ : T → Fin q → κ → R) :
    IsWeightedHomogeneous (rowWeight w) (minorProd c c' ε φ)
      (∑ t, ((∑ a, partOf (c t) a • w t (Sum.inl a)) + ∑ b, partOf (c' t) b • w t (Sum.inr b))) := by
  refine IsWeightedHomogeneous.prod _ _ _ fun t _ => ?_
  rw [← sum_smul_sum_lead, ← sum_smul_sum_lead]
  refine IsWeightedHomogeneous.mul ?_ ?_
  · refine IsWeightedHomogeneous.prod _ _ _ fun i _ => IsWeightedHomogeneous.pow ?_ _
    exact det_isWeightedHomogeneous _ _ _ fun a b => rowForm_isWeightedHomogeneous w t _ _
  · refine IsWeightedHomogeneous.prod _ _ _ fun i _ => IsWeightedHomogeneous.pow ?_ _
    exact det_isWeightedHomogeneous _ _ _ fun a b => rowForm_isWeightedHomogeneous w t _ _

theorem minorProd_isHomogeneous [Fintype T] (c : T → Fin p → ℕ) (c' : T → Fin q → ℕ)
    (ε : T → Fin p → κ → R) (φ : T → Fin q → κ → R) :
    (minorProd c c' ε φ).IsHomogeneous (typeDegree c c') := by
  have := minorProd_isWeightedHomogeneous (fun _ _ => (1 : ℕ)) c c' ε φ
  simp only [smul_eq_mul, mul_one, sum_partOf] at this
  exact this

end Degree

section Subst

variable [Fintype κ] [Fintype κ'] [Fintype κ'']

noncomputable def colSubst (A : T → Matrix κ κ' R) (B : T → Matrix κ' κ R) :
    Poly R T p q κ →ₐ[R] Poly R T p q κ' :=
  aeval fun v => match v with
    | (t, Sum.inl a, k) => xForm t a (A t k)
    | (t, Sum.inr b, k) => yForm t b fun l => B t l k

omit [Fintype κ] in

@[simp] theorem colSubst_X_xVar (A : T → Matrix κ κ' R) (B : T → Matrix κ' κ R) (t : T) (a : Fin p)
    (k : κ) : colSubst A B (X (xVar t a k) : Poly R T p q κ) = xForm t a (A t k) := by
  simp [colSubst]

omit [Fintype κ] in

@[simp] theorem colSubst_X_yVar (A : T → Matrix κ κ' R) (B : T → Matrix κ' κ R) (t : T) (b : Fin q)
    (k : κ) : colSubst A B (X (yVar t b k) : Poly R T p q κ) = yForm t b fun l => B t l k := by
  simp [colSubst]

theorem colSubst_xForm (A : T → Matrix κ κ' R) (B : T → Matrix κ' κ R) (t : T) (a : Fin p)
    (ε : κ → R) : colSubst A B (xForm t a ε : Poly R T p q κ) = xForm t a (ε ᵥ* A t) := by
  have : ε ᵥ* A t = ∑ k, ε k • A t k := by ext l; simp [vecMul, dotProduct]
  rw [this, map_sum, xForm_apply, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← smul_eq_C_mul, map_smul, map_smul, colSubst_X_xVar]

theorem colSubst_yForm (A : T → Matrix κ κ' R) (B : T → Matrix κ' κ R) (t : T) (b : Fin q)
    (φ : κ → R) : colSubst A B (yForm t b φ : Poly R T p q κ) = yForm t b (B t *ᵥ φ) := by
  have : B t *ᵥ φ = ∑ k, φ k • fun l => B t l k := by ext l; simp [mulVec, dotProduct, mul_comm]
  rw [this, map_sum, yForm_apply, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← smul_eq_C_mul, map_smul, map_smul, colSubst_X_yVar]

theorem colSubst_comp (A : T → Matrix κ κ' R) (B : T → Matrix κ' κ R) (A' : T → Matrix κ' κ'' R)
    (B' : T → Matrix κ'' κ' R) :
    (colSubst A' B').comp (colSubst (p := p) (q := q) A B) =
      colSubst (fun t => A t * A' t) (fun t => B' t * B t) := by
  refine MvPolynomial.algHom_ext fun ⟨t, r, k⟩ => ?_
  rcases r with a | b
  · rw [AlgHom.comp_apply, colSubst_X_xVar, colSubst_X_xVar, colSubst_xForm]; rfl
  · rw [AlgHom.comp_apply, colSubst_X_yVar, colSubst_X_yVar, colSubst_yForm]; rfl

theorem colSubst_one [DecidableEq κ] :
    colSubst (p := p) (q := q) (fun _ : T => (1 : Matrix κ κ R)) (fun _ => 1) = AlgHom.id R _ := by
  refine MvPolynomial.algHom_ext fun ⟨t, r, k⟩ => ?_
  rcases r with a | b
  · rw [colSubst_X_xVar, AlgHom.id_apply, ← xForm_single]
    congr 1; ext l; simp [Matrix.one_apply, Pi.single_apply, eq_comm]
  · rw [colSubst_X_yVar, AlgHom.id_apply, ← yForm_single]
    congr 1; ext l; simp [Matrix.one_apply, Pi.single_apply]

theorem colSubst_minorProd [Fintype T] (A : T → Matrix κ κ' R) (B : T → Matrix κ' κ R)
    (c : T → Fin p → ℕ) (c' : T → Fin q → ℕ) (ε : T → Fin p → κ → R) (φ : T → Fin q → κ → R) :
    colSubst A B (minorProd c c' ε φ) =
      minorProd c c' (fun t a => ε t a ᵥ* A t) (fun t b => B t *ᵥ φ t b) := by
  simp only [minorProd, map_prod, map_mul, map_pow]
  refine Finset.prod_congr rfl fun t _ => ?_
  congr 1
  · exact Finset.prod_congr rfl fun i _ => congrArg (· ^ c t i)
      (ringHom_xMinor (colSubst A B).toRingHom t i (ε t) (fun a => ε t a ᵥ* A t)
        fun a b => colSubst_xForm _ _ _ _ _)
  · exact Finset.prod_congr rfl fun i _ => congrArg (· ^ c' t i)
      (ringHom_yMinor (colSubst A B).toRingHom t i (φ t) (fun a => B t *ᵥ φ t a)
        fun a b => colSubst_yForm _ _ _ _ _)

omit [Fintype κ] in

theorem eval_colSubst (A : T → Matrix κ κ' R) (B : T → Matrix κ' κ R) (z : Var T p q κ' → R)
    (P : Poly R T p q κ) :
    eval z (colSubst A B P) = eval (fun v => match v with
      | (t, Sum.inl a, k) => (A t *ᵥ fun l => z (xVar t a l)) k
      | (t, Sum.inr b, k) => ((fun l => z (yVar t b l)) ᵥ* B t) k) P := by
  induction P using MvPolynomial.induction_on with
  | C r => simp [algHom_C]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P v hP =>
    obtain ⟨t, a | b, k⟩ := v
    · rw [map_mul, map_mul, map_mul, hP, eval_X, colSubst_X_xVar, eval_xForm]; rfl
    · rw [map_mul, map_mul, map_mul, hP, eval_X, colSubst_X_yVar, eval_yForm, dotProduct_comm]; rfl

omit [Fintype κ] in

theorem colSubst_isWeightedHomogeneous {M : Type*} [AddCommMonoid M] (w : T → Fin p ⊕ Fin q → M)
    (A : T → Matrix κ κ' R) (B : T → Matrix κ' κ R) {P : Poly R T p q κ} {m : M}
    (hP : IsWeightedHomogeneous (rowWeight w) P m) :
    IsWeightedHomogeneous (rowWeight w) (colSubst A B P) m := by
  rw [P.as_sum, map_sum]
  refine IsWeightedHomogeneous.sum _ _ _ fun d hd => ?_
  rw [← hP (mem_support_iff.mp hd), colSubst, aeval_monomial, Finsupp.weight_apply, Finsupp.sum,
    Finsupp.prod]
  refine IsWeightedHomogeneous.C_mul ?_ _
  refine IsWeightedHomogeneous.prod _ _ _ fun v _ => IsWeightedHomogeneous.pow ?_ _
  obtain ⟨t, a | b, k⟩ := v
  · exact rowForm_isWeightedHomogeneous w t _ _
  · exact rowForm_isWeightedHomogeneous w t _ _

end Subst

section Action

variable [Fintype κ] [DecidableEq κ]

def vecAct (g : GL κ R) (φ : κ → R) : κ → R := (g : Matrix κ κ R) *ᵥ φ

def covecAct (g : GL κ R) (ε : κ → R) : κ → R := ε ᵥ* ((g⁻¹ : GL κ R) : Matrix κ κ R)

theorem covecAct_dotProduct_vecAct (g : GL κ R) (ε φ : κ → R) :
    covecAct g ε ⬝ᵥ vecAct g φ = ε ⬝ᵥ φ := by
  rw [covecAct, vecAct, dotProduct_mulVec, vecMul_vecMul, Units.inv_mul, vecMul_one]

theorem IsPerp.act {ε : T → Fin p → κ → R} {φ : T → Fin q → κ → R} (h : IsPerp ε φ)
    (g : T → GL κ R) :
    IsPerp (fun t a => covecAct (g t) (ε t a)) (fun t b => vecAct (g t) (φ t b)) := fun t a b => by
  rw [covecAct_dotProduct_vecAct, h]

noncomputable def colActHom (g : T → GL κ R) : Poly R T p q κ →ₐ[R] Poly R T p q κ :=
  colSubst (fun t => ((g t)⁻¹ : GL κ R)) (fun t => g t)

theorem colActHom_one : colActHom (p := p) (q := q) (1 : T → GL κ R) = AlgHom.id R _ := by
  rw [← colSubst_one, colActHom]; simp

theorem colActHom_mul (g h : T → GL κ R) :
    colActHom (p := p) (q := q) (g * h) = (colActHom g).comp (colActHom h) := by
  rw [colActHom, colActHom, colActHom, colSubst_comp]
  simp only [Pi.mul_apply, _root_.mul_inv_rev, Units.val_mul]

variable (R T p q κ) in

noncomputable def colAct : (T → GL κ R) →* (Poly R T p q κ ≃ₐ[R] Poly R T p q κ) where
  toFun g := AlgEquiv.ofAlgHom (colActHom g) (colActHom g⁻¹)
    (by rw [← colActHom_mul, mul_inv_cancel, colActHom_one])
    (by rw [← colActHom_mul, inv_mul_cancel, colActHom_one])
  map_one' := AlgEquiv.ext fun P => DFunLike.congr_fun colActHom_one P
  map_mul' g h := AlgEquiv.ext fun P => DFunLike.congr_fun (colActHom_mul g h) P

theorem colAct_apply (g : T → GL κ R) (P : Poly R T p q κ) :
    colAct R T p q κ g P = colSubst (fun t => ((g t)⁻¹ : GL κ R)) (fun t => g t) P := rfl

variable (R T p q κ) in

noncomputable def colRep : Representation R (T → GL κ R) (Poly R T p q κ) where
  toFun g := (colAct R T p q κ g).toLinearMap
  map_one' := by rw [map_one]; rfl
  map_mul' g h := by rw [map_mul]; rfl

@[simp] theorem colRep_apply (g : T → GL κ R) (P : Poly R T p q κ) :
    colRep R T p q κ g P = colAct R T p q κ g P := rfl

theorem colAct_xForm (g : T → GL κ R) (t : T) (a : Fin p) (ε : κ → R) :
    colAct R T p q κ g (xForm t a ε) = xForm t a (covecAct (g t) ε) := colSubst_xForm _ _ _ _ _

theorem colAct_yForm (g : T → GL κ R) (t : T) (b : Fin q) (φ : κ → R) :
    colAct R T p q κ g (yForm t b φ) = yForm t b (vecAct (g t) φ) := colSubst_yForm _ _ _ _ _

theorem colAct_minorProd [Fintype T] (g : T → GL κ R) (c : T → Fin p → ℕ) (c' : T → Fin q → ℕ)
    (ε : T → Fin p → κ → R) (φ : T → Fin q → κ → R) :
    colAct R T p q κ g (minorProd c c' ε φ) =
      minorProd c c' (fun t a => covecAct (g t) (ε t a)) (fun t b => vecAct (g t) (φ t b)) :=
  colSubst_minorProd _ _ _ _ _ _

end Action

section Base

variable (R) in

def baseCovec (h : p + q ≤ n) (a : Fin p) : Fin n → R :=
  Pi.single (Fin.castLE (by omega) a) 1

variable (R) in

def baseVec (h : p + q ≤ n) (b : Fin q) : Fin n → R :=
  Pi.single (Fin.rev (Fin.castLE (by omega) b)) 1

variable (R T) in

theorem isPerp_base (h : p + q ≤ n) :
    IsPerp (fun _ : T => baseCovec R h) (fun _ => baseVec R h) := fun t a b => by
  have : Fin.castLE (by omega : p ≤ n) a ≠ Fin.rev (Fin.castLE (by omega : q ≤ n) b) := by
    intro e
    have := congrArg Fin.val e
    have := a.isLt; have := b.isLt
    simp only [Fin.val_castLE, Fin.val_rev] at *; omega
  simp [baseCovec, baseVec, Pi.single_apply, this]

theorem linearIndependent_baseCovec (h : p + q ≤ n) : LinearIndependent R (baseCovec R h) := by
  have := (Pi.basisFun R (Fin n)).linearIndependent.comp _
    (Fin.castLE_injective (by omega : p ≤ n))
  convert this using 1; ext1 a; simp [baseCovec]

theorem linearIndependent_baseVec (h : p + q ≤ n) : LinearIndependent R (baseVec R h) := by
  have := (Pi.basisFun R (Fin n)).linearIndependent.comp _
    (Fin.rev_injective.comp (Fin.castLE_injective (by omega : q ≤ n)))
  convert this using 1; ext1 a; simp [baseVec]

variable [Fintype T]

variable (R) in

noncomputable def basePoly (h : p + q ≤ n) (c : T → Fin p → ℕ) (c' : T → Fin q → ℕ) :
    Poly R T p q (Fin n) :=
  minorProd c c' (fun _ => baseCovec R h) (fun _ => baseVec R h)

variable (R) in

noncomputable def orbitSpan (h : p + q ≤ n) (c : T → Fin p → ℕ) (c' : T → Fin q → ℕ) :
    Submodule R (Poly R T p q (Fin n)) :=
  Submodule.span R (Set.range fun g : T → GL (Fin n) R =>
    colAct R T p q (Fin n) g (basePoly R h c c'))

variable (h : p + q ≤ n) (c : T → Fin p → ℕ) (c' : T → Fin q → ℕ)

theorem colAct_basePoly_mem (g : T → GL (Fin n) R) :
    colAct R T p q (Fin n) g (basePoly R h c c') ∈ orbitSpan R h c c' :=
  Submodule.subset_span ⟨g, rfl⟩

theorem basePoly_mem : basePoly R h c c' ∈ orbitSpan R h c c' := by
  simpa using colAct_basePoly_mem h c c' (1 : T → GL (Fin n) R)

theorem colAct_mem_orbitSpan (g : T → GL (Fin n) R) {P : Poly R T p q (Fin n)}
    (hP : P ∈ orbitSpan R h c c') : colAct R T p q (Fin n) g P ∈ orbitSpan R h c c' := by
  induction hP using Submodule.span_induction with
  | mem P hP =>
    obtain ⟨g', rfl⟩ := hP
    have := colAct_basePoly_mem h c c' (g * g')
    rwa [map_mul] at this
  | zero => simp
  | add P Q _ _ hP hQ => rw [map_add]; exact add_mem hP hQ
  | smul r P _ hP => rw [map_smul]; exact Submodule.smul_mem _ _ hP

variable (R) in

noncomputable def orbitSubrep : Subrepresentation (colRep R T p q (Fin n)) where
  toSubmodule := orbitSpan R h c c'
  apply_mem_toSubmodule g _ hP := colAct_mem_orbitSpan h c c' g hP

theorem map_basePoly (f : R →+* S) : MvPolynomial.map f (basePoly R h c c') = basePoly S h c c' := by
  rw [basePoly, map_minorProd, basePoly]
  congr 1
  · ext t a k; simp [baseCovec, Pi.single_apply, apply_ite f]
  · ext t a k; simp [baseVec, Pi.single_apply, apply_ite f]

theorem eval_basePoly :
    eval (fun v : Var T p q (Fin n) =>
      Sum.elim (baseCovec R h) (baseVec R h) v.2.1 v.2.2) (basePoly R h c c') = 1 := by
  simp only [basePoly, minorProd, map_prod, map_mul, map_pow]
  refine Finset.prod_eq_one fun t _ => ?_
  rw [Finset.prod_eq_one, Finset.prod_eq_one, mul_one]
  · intro i _
    rw [yMinor, RingHom.map_det]
    refine (congrArg (fun A => det A ^ c' t i) (?_ : _ = (1 : Matrix _ _ R))).trans (by simp)
    ext a b
    simp [eval_yForm, baseVec, Pi.single_apply, Matrix.one_apply, eq_comm]
  · intro i _
    rw [xMinor, RingHom.map_det]
    refine (congrArg (fun A => det A ^ c t i) (?_ : _ = (1 : Matrix _ _ R))).trans (by simp)
    ext a b
    simp [eval_xForm, baseCovec, Pi.single_apply, Matrix.one_apply, eq_comm]

theorem basePoly_ne_zero [Nontrivial R] : basePoly R h c c' ≠ 0 := fun e => by
  have := eval_basePoly (R := R) h c c'
  rw [e, map_zero] at this
  exact zero_ne_one this

theorem totalDegree_basePoly [Nontrivial R] :
    (basePoly R h c c').totalDegree = typeDegree c c' :=
  (minorProd_isHomogeneous c c' _ _).totalDegree (basePoly_ne_zero h c c')

end Base

example : IsHarmonic (X (xVar () 0 0) * X (yVar () 0 0) - X (xVar () 0 1) * X (yVar () 0 1) :
    Poly ℤ Unit 1 1 (Fin 2)) := by
  rintro ⟨⟩ a b
  obtain rfl := Subsingleton.elim a 0
  obtain rfl := Subsingleton.elim b 0
  simp only [← xForm_single, ← yForm_single, map_sub, laplacian_xForm_mul_yForm]
  simp

example : laplacian () 0 0 (X (xVar () 0 0) * X (yVar () 0 0) : Poly ℤ Unit 1 1 (Fin 2)) = 1 := by
  simp only [← xForm_single, ← yForm_single, laplacian_xForm_mul_yForm]
  simp

example : basePoly ℤ (show 1 + 1 ≤ 2 from le_rfl) (fun (_ : Unit) _ => 2) (fun _ _ => 1) =
    X (xVar () 0 0) ^ 2 * X (yVar () 0 1) := by
  simp [basePoly, minorProd, xMinor, yMinor, baseCovec, baseVec]

example : basePoly ℤ (show 2 + 0 ≤ 2 from le_rfl) (fun (_ : Unit) => ![0, 1]) (fun _ _ => 0) =
    X (xVar () 0 0) * X (xVar () 1 1) - X (xVar () 0 1) * X (xVar () 1 0) := by
  have : (xMinor () 1 (baseCovec ℤ (show 2 + 0 ≤ 2 from le_rfl)) : Poly ℤ Unit 2 0 (Fin 2)) =
      X (xVar () 0 0) * X (xVar () 1 1) - X (xVar () 0 1) * X (xVar () 1 0) := by
    refine (det_fin_two _).trans ?_
    simp only [baseCovec, of_apply, xForm_single]; rfl
  simp [basePoly, minorProd, this]

example : typeDegree (fun _ : Unit => ![2, 1]) (fun _ => ![2]) = 6 ∧ partOf ![2, 1] = ![3, 1] := by
  decide

example (u : Rˣ) (k : Fin n) :
    colAct R Unit 1 1 (Fin n) (fun _ => Matrix.GeneralLinearGroup.scalar (Fin n) u)
        (X (xVar () 0 k)) = (↑u⁻¹ : R) • X (xVar () 0 k) ∧
    colAct R Unit 1 1 (Fin n) (fun _ => Matrix.GeneralLinearGroup.scalar (Fin n) u)
        (X (yVar () 0 k)) = (u : R) • X (yVar () 0 k) := by
  simp only [← xForm_single, ← yForm_single, colAct_xForm, colAct_yForm, ← map_smul]
  constructor
  · congr 1
    rw [covecAct, ← map_inv]
    ext l; simp [Matrix.GeneralLinearGroup.scalar, Pi.single_apply, diagonal_apply, eq_comm]
  · congr 1
    ext l; simp [vecAct, Matrix.GeneralLinearGroup.scalar, Pi.single_apply, diagonal_apply, eq_comm]

end GlobalTheory.Harm
