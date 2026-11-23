import Formalism.PeriodIntegrals.UnfoldEquiv

open PI.UnfoldEquiv PI.UnfoldEquiv.Loc

noncomputable section

namespace PI.UnfoldEquiv.UnitaryGroupMassFormula

variable {k : Type} [CommRing k]

theorem eN_apply (N i : ℕ) (l : Fin N) : eN k N i l = if l.1 = i then 1 else 0 := rfl

theorem mem_Ufl {n c i : ℕ} {v : Fin (n + c) → k} :
    v ∈ Ufl k n c i ↔ ∀ l : Fin (n + c), ¬ (l.1 < n + i) → v l = 0 := Iff.rfl

theorem inX_apply {n c : ℕ} (x : Fin n → k) (l : Fin (n + c)) :
    inX k n c x l = if h : l.1 < n then x ⟨l.1, h⟩ else 0 := by
  simp only [inX, LinearMap.pi_apply]
  split_ifs with h
  · rfl
  · rfl

theorem atN_add {N : ℕ} (v w : Fin N → k) (i : ℕ) : atN (v + w) i = atN v i + atN w i := by
  simp only [atN]
  split_ifs <;> simp

theorem atN_smul {N : ℕ} (a : k) (v : Fin N → k) (i : ℕ) : atN (a • v) i = a * atN v i := by
  simp only [atN]
  split_ifs <;> simp

theorem atN_of_mem {n c i : ℕ} {v : Fin (n + c) → k} (hv : v ∈ Ufl k n c i) : atN v (n + i) = 0 := by
  unfold atN
  split_ifs with h
  · exact (mem_Ufl.1 hv) ⟨n + i, h⟩ (lt_irrefl _)
  · rfl

theorem atN_eN {N i : ℕ} (h : i < N) : atN (eN k N i) i = 1 := by
  rw [atN, dif_pos h, eN_apply]
  exact if_pos rfl

theorem atN_eN_ne {N i j : ℕ} (h : j ≠ i) : atN (eN k N j) i = 0 := by
  unfold atN
  split_ifs with hi
  · rw [eN_apply]
    exact if_neg fun e => h e.symm
  · rfl

def base {n' n c : ℕ} (xj : (Fin n' → k) →ₗ[k] (Fin n → k)) (l : Fin (n + c)) (s : Fin (n' + (c + 1))) : k :=
  if hs : s.1 < n' then (if hl : l.1 < n then LinearMap.toMatrix' xj ⟨l.1, hl⟩ ⟨s.1, hs⟩ else 0)
    else if l.1 = n + (s.1 - n') then 1 else 0

def Q {n' n c : ℕ} (xj : (Fin n' → k) →ₗ[k] (Fin n → k)) (x : (Fin (n' + (c + 1)) → k) →ₗ[k] (Fin (n + c) → k)) : Prop :=
  (∀ v, x (inX k n' (c + 1) v) = inX k n c (xj v)) ∧ (0 < c → x (eN k (n' + (c + 1)) n') = eN k (n + c) n) ∧
    ∀ j, 1 ≤ j → j < c → x (eN k (n' + (c + 1)) (n' + j)) - eN k (n + c) (n + j) ∈ Ufl k n c j

def fe {n' n c : ℕ} (x : (Fin (n' + (c + 1)) → k) →ₗ[k] (Fin (n + c) → k)) : FC n' (c + 1) n c → k :=
  fun p => x (Pi.single p.1.2 1) p.1.1

theorem fillMatrix_single {n' n c : ℕ} (xj : (Fin n' → k) →ₗ[k] (Fin n → k)) (t : FC n' (c + 1) n c → k)
    (l : Fin (n + c)) (s : Fin (n' + (c + 1))) :
    xx1 xj t (Pi.single s 1) l = if hf : IsFree n' n c l.1 s.1 then t ⟨(l, s), hf⟩ else base xj l s := by
  simp only [xx1, Matrix.toLin'_apply, Matrix.mulVec_single, MulOpposite.op_one, one_smul, Matrix.col_apply,
    Matrix.of_apply, base]

theorem extractFree_fillMatrix {n' n c : ℕ} (xj : (Fin n' → k) →ₗ[k] (Fin n → k)) (t : FC n' (c + 1) n c → k) :
    fe (xx1 xj t) = t := by
  funext p
  show xx1 xj t (Pi.single p.1.2 1) p.1.1 = t p
  rw [fillMatrix_single, dif_pos p.2]

end PI.UnfoldEquiv.UnitaryGroupMassFormula
