import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.OrderedConst
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LeadingPrincipalMinorMulModConductorStatement

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType Matrix

noncomputable section

namespace GlobalTheory.PsType.BlockTheta

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem ev_mul_char (χ η : kˣ →* ℂˣ) (x : k) : ev (χ * η) x = ev χ x * ev η x := by
  unfold ev
  split_ifs with h
  · simp
  · simp

theorem ev_one_char (x : k) : ev (1 : kˣ →* ℂˣ) x = 1 := by
  unfold ev; split_ifs <;> simp

theorem ev_at_one (χ : kˣ →* ℂˣ) : ev χ (1 : k) = 1 := by
  unfold ev
  rw [dif_pos (by simp)]
  have : Units.mk0 (1 : k) one_ne_zero = 1 := by ext; simp
  simp [this]

theorem ev_mul_of_val (χ : kˣ →* ℂˣ) {x y : k} (hx : valuation k x = 1) (hy : valuation k y = 1) :
    ev χ (x * y) = ev χ x * ev χ y := by
  have hxy : valuation k (x * y) = 1 := by rw [map_mul, hx, hy, one_mul]
  unfold ev
  rw [dif_pos hxy, dif_pos hx, dif_pos hy, ← Units.val_mul, ← map_mul]
  congr 3
  ext; simp

theorem ev_of_triv_one (χ : kˣ →* ℂˣ) (h : Triv χ 1) (x : k) : ev χ x = 1 := by
  unfold ev
  split_ifs with hx
  · have hu : χ (Units.mk0 x fun h0 => by simp [h0] at hx) = 1 := by
      refine h _ (by simpa using hx) ?_
      calc valuation k ((Units.mk0 x fun h0 => by simp [h0] at hx : kˣ) - 1 : k)
          ≤ max (valuation k x) (valuation k 1) := by rw [Units.val_mk0]; exact Valuation.map_sub _ _ _
        _ = valuation k 1 := by rw [hx, map_one, max_self]
    simp [hu]
  · rfl

theorem val_det_of_mem_KO {n : Type} [Fintype n] [DecidableEq n] {g : GL n k} (hg : g ∈ KO k n) :
    valuation k g.val.det = 1 := by
  obtain ⟨A, rfl⟩ := hg
  have h1 : ((Matrix.GeneralLinearGroup.map (n := n) (algebraMap 𝒪[k] k)) A).val.det
      = algebraMap 𝒪[k] k A.val.det := by
    simp [RingHom.map_det]
  rw [h1]
  exact (Valuation.integer.integers (valuation k)).one_of_isUnit (Matrix.isUnits_det_units A)

def head {n : ℕ} (ψ : Fin n → kˣ →* ℂˣ) : kˣ →* ℂˣ := if h : 0 < n then ψ ⟨0, h⟩ else 1

theorem prod_ev_nxt : ∀ (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ) (x : k),
    ∏ m, ev (ψ m / nxt ψ m) x = ev (head ψ) x
  | 0, ψ, x => by simp [head, ev_one_char]
  | n + 1, ψ, x => by
    rw [Fin.prod_univ_succ]
    have h1 : ∀ j : Fin n, nxt ψ j.succ = nxt (fun i => ψ i.succ) j := by
      intro j; unfold nxt
      by_cases h : (j : ℕ) + 1 < n
      · rw [dif_pos (by simp [Fin.val_succ]; omega), dif_pos h]; congr 1
      · rw [dif_neg (by simp [Fin.val_succ]; omega), dif_neg h]
    have h2 : nxt ψ 0 = head (fun i : Fin n => ψ i.succ) := by
      unfold nxt head
      by_cases h : 0 < n
      · rw [dif_pos (by simp; omega), dif_pos h]; congr 1
      · rw [dif_neg (by simp; omega), dif_neg h]
    simp_rw [h1]
    rw [prod_ev_nxt n, ← h2, ← ev_mul_char, div_mul_cancel]
    simp [head]

variable {r t : ℕ}

theorem castAdd_eq (i : Fin r) : Fin.castAdd t i = stdSum (rfl : r + t = r + t) (Sum.inl i) := by ext; simp
theorem natAdd_eq (j : Fin t) : Fin.natAdd r j = stdSum (rfl : r + t = r + t) (Sum.inr j) := by ext; simp

theorem emb_ll (a : GL (Fin r) k) (b : GL (Fin t) k) (i j : Fin r) :
    (emb₂ k (stdSum (rfl : r + t = r + t)) (a, b)).val (Fin.castAdd t i) (Fin.castAdd t j) = a.val i j := by
  rw [castAdd_eq, castAdd_eq]
  exact (congrFun (congrFun (val_emb₂ k (stdSum (rfl : r + t = r + t)) (a, b)) _) _).trans (by simp)

theorem emb_lr (a : GL (Fin r) k) (b : GL (Fin t) k) (i : Fin r) (j : Fin t) :
    (emb₂ k (stdSum (rfl : r + t = r + t)) (a, b)).val (Fin.castAdd t i) (Fin.natAdd r j) = 0 := by
  rw [castAdd_eq, natAdd_eq]
  exact (congrFun (congrFun (val_emb₂ k (stdSum (rfl : r + t = r + t)) (a, b)) _) _).trans (by simp)

theorem emb_rl (a : GL (Fin r) k) (b : GL (Fin t) k) (i : Fin t) (j : Fin r) :
    (emb₂ k (stdSum (rfl : r + t = r + t)) (a, b)).val (Fin.natAdd r i) (Fin.castAdd t j) = 0 := by
  rw [castAdd_eq, natAdd_eq]
  exact (congrFun (congrFun (val_emb₂ k (stdSum (rfl : r + t = r + t)) (a, b)) _) _).trans (by simp)

theorem emb_rr (a : GL (Fin r) k) (b : GL (Fin t) k) (i j : Fin t) :
    (emb₂ k (stdSum (rfl : r + t = r + t)) (a, b)).val (Fin.natAdd r i) (Fin.natAdd r j) = b.val i j := by
  rw [natAdd_eq, natAdd_eq]
  exact (congrFun (congrFun (val_emb₂ k (stdSum (rfl : r + t = r + t)) (a, b)) _) _).trans (by simp)

def eqvL (i : Fin r) : {y : Fin r // y ≤ i} ≃ {x : Fin (r + t) // x ≤ Fin.castAdd t i} :=
  Equiv.ofBijective (fun y : {y : Fin r // y ≤ i} => (⟨Fin.castAdd t y.1, by
      have := y.2; simp only [Fin.le_def, Fin.coe_castAdd] at this ⊢; omega⟩ :
        {x : Fin (r + t) // x ≤ Fin.castAdd t i})) (by
    constructor
    · rintro ⟨y, hy⟩ ⟨z, hz⟩ h
      simp only [Subtype.mk.injEq, Fin.ext_iff, Fin.coe_castAdd] at h
      exact Subtype.ext (Fin.ext h)
    · rintro ⟨x, hx⟩
      have hx' : (x : ℕ) ≤ i := by simpa [Fin.le_def] using hx
      exact ⟨⟨⟨x, by omega⟩, by simp [Fin.le_def]; omega⟩, by ext; simp⟩)

theorem eqvL_val (i : Fin r) (y : {y : Fin r // y ≤ i}) : ((eqvL (t := t) i y) : Fin (r + t)) = Fin.castAdd t y.1 := rfl

def eqvR (j : Fin t) : Fin r ⊕ {y : Fin t // y ≤ j} ≃ {x : Fin (r + t) // x ≤ Fin.natAdd r j} :=
  Equiv.ofBijective (Sum.elim (fun i : Fin r => (⟨Fin.castAdd t i, by
        simp only [Fin.le_def, Fin.coe_castAdd, Fin.coe_natAdd]; omega⟩ : {x : Fin (r + t) // x ≤ Fin.natAdd r j}))
      (fun y : {y : Fin t // y ≤ j} => (⟨Fin.natAdd r y.1, by
        have := y.2; simp only [Fin.le_def, Fin.coe_natAdd] at this ⊢; omega⟩ : {x : Fin (r + t) // x ≤ Fin.natAdd r j}))) (by
    constructor
    · intro u v h
      rcases u with y | y <;> rcases v with z | z <;>
        simp only [Sum.elim_inl, Sum.elim_inr, Subtype.mk.injEq, Fin.ext_iff, Fin.coe_castAdd,
          Fin.coe_natAdd] at h
      · exact congrArg Sum.inl (Fin.ext h)
      · have := y.2; omega
      · have := z.2; omega
      · exact congrArg Sum.inr (Subtype.ext (Fin.ext (by omega)))
    · rintro ⟨x, hx⟩
      have hx' : (x : ℕ) ≤ r + j := by simpa [Fin.le_def] using hx
      by_cases h : (x : ℕ) < r
      · exact ⟨Sum.inl ⟨x, h⟩, by ext; simp⟩
      · exact ⟨Sum.inr ⟨⟨x - r, by omega⟩, by simp [Fin.le_def]; omega⟩, by ext; simp; omega⟩)

theorem eqvR_inl (j : Fin t) (i : Fin r) : ((eqvR j (Sum.inl i)) : Fin (r + t)) = Fin.castAdd t i := rfl
theorem eqvR_inr (j : Fin t) (y : {y : Fin t // y ≤ j}) : ((eqvR (r := r) j (Sum.inr y)) : Fin (r + t)) = Fin.natAdd r y.1 := rfl

theorem minor_castAdd (a : GL (Fin r) k) (b : GL (Fin t) k) (i : Fin r) :
    minor (emb₂ k (stdSum (rfl : r + t = r + t)) (a, b)) (Fin.castAdd t i) = minor a i := by
  unfold minor
  rw [← Matrix.det_submatrix_equiv_self (eqvL i)]
  congr 1
  ext y z
  simp only [toSquareBlockProp, toBlock, submatrix_apply, eqvL_val, emb_ll]

theorem minor_natAdd (a : GL (Fin r) k) (b : GL (Fin t) k) (j : Fin t) :
    minor (emb₂ k (stdSum (rfl : r + t = r + t)) (a, b)) (Fin.natAdd r j) = a.val.det * minor b j := by
  unfold minor
  rw [← Matrix.det_submatrix_equiv_self (eqvR j)]
  rw [show ((emb₂ k (stdSum (rfl : r + t = r + t)) (a, b)).val.toSquareBlockProp fun x => x ≤ Fin.natAdd r j).submatrix (eqvR j) (eqvR j)
      = fromBlocks a.val 0 0 (b.val.toSquareBlockProp fun x => x ≤ j) by
    ext (y | y) (z | z) <;> simp only [toSquareBlockProp, toBlock, submatrix_apply, eqvR_inl, eqvR_inr,
      emb_ll, emb_lr, emb_rl, emb_rr, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
      fromBlocks_apply₂₂, Matrix.zero_apply]]
  rw [det_fromBlocks_zero₂₁]

theorem minor_last {r : ℕ} (a : GL (Fin (r + 1)) k) : minor a (Fin.last r) = a.val.det := by
  unfold minor
  rw [← Matrix.det_submatrix_equiv_self (Equiv.subtypeUnivEquiv (fun x => Fin.le_last x)).symm]
  congr 1

theorem nxt_natAdd (ψ : Fin (r + t) → kˣ →* ℂˣ) (j : Fin t) :
    nxt ψ (Fin.natAdd r j) = nxt (fun i => ψ (Fin.natAdd r i)) j := by
  unfold nxt
  by_cases h : (j : ℕ) + 1 < t
  · rw [dif_pos (by simp; omega), dif_pos h]; congr 1
  · rw [dif_neg (by simp; omega), dif_neg h]

theorem nxt_castAdd_castSucc {r : ℕ} (ψ : Fin (r + 1 + t) → kˣ →* ℂˣ) (i : Fin r) :
    nxt ψ (Fin.castAdd t i.castSucc) = nxt (fun i => ψ (Fin.castAdd t i)) i.castSucc := by
  unfold nxt
  rw [dif_pos (by simp; omega), dif_pos (by simp)]
  congr 1

theorem nxt_castAdd_last {r : ℕ} (ψ : Fin (r + 1 + t) → kˣ →* ℂˣ) :
    nxt ψ (Fin.castAdd t (Fin.last r)) = head (fun j : Fin t => ψ (Fin.natAdd (r + 1) j)) := by
  unfold nxt head
  by_cases h : 0 < t
  · rw [dif_pos (by simp; omega), dif_pos h]; congr 1
  · rw [dif_neg (by simp; omega), dif_neg h]

theorem nxt_last_one {r : ℕ} (φ : Fin (r + 1) → kˣ →* ℂˣ) : nxt φ (Fin.last r) = 1 := by
  unfold nxt; rw [dif_neg (by simp)]

theorem first_part : ∀ (r t : ℕ) (ψ : Fin (r + t) → kˣ →* ℂˣ) (a : GL (Fin r) k),
    (∏ i : Fin r, ev (ψ (Fin.castAdd t i) / nxt ψ (Fin.castAdd t i)) (minor a i)) *
      ev (head fun j : Fin t => ψ (Fin.natAdd r j)) a.val.det = theta (fun i => ψ (Fin.castAdd t i)) a
  | 0, t, ψ, a => by simp [theta, Matrix.det_isEmpty, ev_at_one]
  | r + 1, t, ψ, a => by
    unfold theta
    rw [Fin.prod_univ_castSucc, Fin.prod_univ_castSucc, mul_assoc, minor_last, nxt_castAdd_last,
      nxt_last_one, ← ev_mul_char, div_mul_cancel, div_one]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [nxt_castAdd_castSucc]

end GlobalTheory.PsType.BlockTheta

open GlobalTheory.PsType.BlockTheta in

theorem GlobalTheory.PsType.theta_emb₂_std : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (ψ : Fin (r + t) → kˣ →* ℂˣ), Ordered ψ → ∀ a ∈ grp (fun i => ψ (Fin.castAdd t i)), ∀ b ∈ grp (fun i => ψ (Fin.natAdd r i)), theta ψ (emb₂ k (stdSum (rfl : r + t = r + t)) (a, b)) = theta (fun i => ψ (Fin.castAdd t i)) a * theta (fun i => ψ (Fin.natAdd r i)) b := by
  intro k _ _ _ _ r t ψ hord a ha b hb
  have hord₂ : Ordered (fun i => ψ (Fin.natAdd r i)) := by
    intro i a' b' j h1 h2 h3 x hx
    exact hord (Fin.natAdd r i) (Fin.natAdd r a') (Fin.natAdd r b') (Fin.natAdd r j) (by rw [Fin.le_def] at h1 ⊢; simp only [Fin.coe_natAdd]; omega) (by rw [Fin.le_def] at h2 ⊢; simp only [Fin.coe_natAdd]; omega)
      (by rw [Fin.le_def] at h3 ⊢; simp only [Fin.coe_natAdd]; omega) x hx
  have hda : valuation k a.val.det = 1 := val_det_of_mem_KO ha.1
  have hsplit : theta ψ (emb₂ k (stdSum (rfl : r + t = r + t)) (a, b)) =
      (∏ i : Fin r, ev (ψ (Fin.castAdd t i) / nxt ψ (Fin.castAdd t i)) (minor a i)) *
        ((∏ j : Fin t, ev ((fun i => ψ (Fin.natAdd r i)) j / nxt (fun i => ψ (Fin.natAdd r i)) j) a.val.det) *
          theta (fun i => ψ (Fin.natAdd r i)) b) := by
    unfold theta
    rw [Fin.prod_univ_add]
    congr 1
    · exact Finset.prod_congr rfl fun i _ => by rw [minor_castAdd]
    · rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [minor_natAdd, nxt_natAdd]
      by_cases hT : Triv ((fun i => ψ (Fin.natAdd r i)) j / nxt (fun i => ψ (Fin.natAdd r i)) j) 1
      · rw [ev_of_triv_one _ hT, ev_of_triv_one _ hT, ev_of_triv_one _ hT, one_mul]
      · exact ev_mul_of_val _ hda ((GlobalTheory.T.leadingPrincipalMinor_mul_mod_conductor k t _ hord₂ j hT).1 b hb)
  rw [hsplit, prod_ev_nxt, ← mul_assoc, first_part]
