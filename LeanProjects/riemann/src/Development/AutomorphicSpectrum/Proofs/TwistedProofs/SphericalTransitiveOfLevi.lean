import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen

noncomputable section

open Formalism.UG Matrix GlobalTheory.SatakeWeyl GlobalTheory.InertZeta

namespace GlobalTheory.CompanionTheory.InertTrans

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {N : ℕ}

theorem conj_mem_radU {n : ℕ} {β : Fin n → ℕ} {m u : GU σ n} (hm : m ∈ leviU σ β) (hu : u ∈ radU σ β) :
    m * u * m⁻¹ ∈ radU σ β := by
  have hA : ∀ i j, β i ≠ β j → mat m i j = 0 := hm
  have hC : ∀ i j, β i ≠ β j → mat m⁻¹ i j = 0 := inv_mem hm
  have hB : ∀ i j, β j ≤ β i → mat u i j = (1 : Matrix (Fin n) (Fin n) L) i j := hu
  show ∀ i j, β j ≤ β i → mat (m * u * m⁻¹) i j = (1 : Matrix (Fin n) (Fin n) L) i j
  intro i j h
  have e : (mat m * mat u * mat m⁻¹) i j = (mat m * mat m⁻¹) i j := by
    rw [Matrix.mul_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun p _ => ?_
    by_cases hp : β p = β j
    · congr 1
      rw [Matrix.mul_apply]
      calc _ = ∑ l, mat m i l * (1 : Matrix (Fin n) (Fin n) L) l p := Finset.sum_congr rfl fun l _ => by
              by_cases hl : β i = β l
              · rw [hB l p (by omega)]
              · rw [hA i l hl, zero_mul, zero_mul]
        _ = _ := by rw [← Matrix.mul_apply, Matrix.mul_one]
    · rw [hC p j hp, mul_zero, mul_zero]
  rw [mat_mul, mat_mul, e, mat_mul_inv]

theorem blk_mono {i j : Fin (N + 2)} (h : j < i) : blk N j ≤ blk N i := by
  rcases idx_cases i with rfl | ⟨i, rfl⟩ | rfl <;> rcases idx_cases j with rfl | ⟨j, rfl⟩ | rfl
  · simp at h
  · simp at h
  · simp at h
  · simp
  · simp
  · exact absurd h (not_lt.2 (Fin.le_last _))
  · simp
  · simp
  · simp

theorem isUnipU_of_radQ {u : GU σ (N + 2)} (hu : u ∈ radQ σ N) : IsUnipU u := by
  have hB : ∀ i j, blk N j ≤ blk N i → mat u i j = (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) i j := hu
  refine ⟨fun i j h => ?_, fun i => ?_⟩
  · exact (hB i j (blk_mono h)).trans (Matrix.one_apply_ne (ne_of_gt h))
  · exact (hB i i le_rfl).trans (Matrix.one_apply_eq i)

theorem levi_off {ϖ : L} {a : ℤ} {g : GU σ N} {m : GU σ (N + 2)} (h : IsLeviElt ϖ a g m) :
    (∀ l, mat m 0 (mid l) = 0) ∧ (∀ l, mat m (mid l) 0 = 0) ∧ mat m 0 (Fin.last (N + 1)) = 0 ∧
      mat m (Fin.last (N + 1)) 0 = 0 ∧ (∀ l, mat m (mid l) (Fin.last (N + 1)) = 0) ∧
      ∀ l, mat m (Fin.last (N + 1)) (mid l) = 0 := by
  have hA : ∀ i j, blk N i ≠ blk N j → mat m i j = 0 := h.1
  exact ⟨fun l => hA _ _ (by simp), fun l => hA _ _ (by simp), hA _ _ (by simp), hA _ _ (by simp),
    fun l => hA _ _ (by simp), fun l => hA _ _ (by simp)⟩

theorem levi_borel {ϖ : L} {a : ℤ} {g : GU σ N} {m : GU σ (N + 2)} (h : IsLeviElt ϖ a g m) (hg : IsBorelU g) :
    IsBorelU m := by
  obtain ⟨o1, o2, o3, o4, o5, o6⟩ := levi_off h
  intro i j hij
  rcases idx_cases i with rfl | ⟨i, rfl⟩ | rfl <;> rcases idx_cases j with rfl | ⟨j, rfl⟩ | rfl
  · simp at hij
  · simp at hij
  · simp at hij
  · exact o2 _
  · exact (h.2.2.2 i j).trans (hg i j (by
      have h' : j.val + 1 < i.val + 1 := hij
      exact Fin.lt_def.2 (by omega)))
  · exact absurd hij (not_lt.2 (Fin.le_last _))
  · exact o4
  · exact o6 _
  · exact absurd hij (lt_irrefl _)

theorem levi_mem_K {ϖ : L} {g : GU σ N} {m : GU σ (N + 2)} (hσ : ∀ x, Valued.v (σ x) = Valued.v x)
    (h : IsLeviElt ϖ 0 g m) (hg : g ∈ KU σ N) : m ∈ KU σ (N + 2) := by
  obtain ⟨o1, o2, o3, o4, o5, o6⟩ := levi_off h
  rw [mem_KU_iff hσ]
  intro i j
  rcases idx_cases i with rfl | ⟨i, rfl⟩ | rfl <;> rcases idx_cases j with rfl | ⟨j, rfl⟩ | rfl
  · rw [h.2.1, zpow_zero]; exact one_mem _
  · rw [o1]; exact zero_mem _
  · rw [o3]; exact zero_mem _
  · rw [o2]; exact zero_mem _
  · rw [h.2.2.2]; exact P.fSatake_K_int hg i j
  · rw [o5]; exact zero_mem _
  · rw [o4]; exact zero_mem _
  · rw [o6]; exact zero_mem _
  · rw [h.2.2.1, neg_zero, zpow_zero]; exact one_mem _

theorem levi_eq_mul {ϖ : L} {a : ℤ} {b k : GU σ N} {mb mk m : GU σ (N + 2)} (hb : IsLeviElt ϖ a b mb)
    (hk : IsLeviElt ϖ 0 k mk) (hm : IsLeviElt ϖ a (b * k) m) : m = mb * mk := by
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := levi_off hb
  obtain ⟨k1, k2, k3, k4, k5, k6⟩ := levi_off hk
  obtain ⟨m1, m2, m3, m4, m5, m6⟩ := levi_off hm
  apply mat_injective
  ext i j
  rw [mat_mul, Matrix.mul_apply, sum_idx]
  rcases idx_cases i with rfl | ⟨i, rfl⟩ | rfl <;> rcases idx_cases j with rfl | ⟨j, rfl⟩ | rfl <;>
    simp only [b1, b2, b3, b4, b5, b6, k1, k2, k3, k4, k5, k6, m1, m2, m3, m4, m5, m6, hb.2.1, hb.2.2.1, hb.2.2.2,
      hk.2.1, hk.2.2.1, hk.2.2.2, hm.2.1, hm.2.2.1, hm.2.2.2, zero_mul, mul_zero, Finset.sum_const_zero, add_zero,
      zero_add, zpow_zero, neg_zero, mul_one, mat_mul, Matrix.mul_apply]

theorem sphTrans_of_leviExists : LeviExists → SphTrans := by
  intro hL L _ _ ϖ σ q N r hU hr α φ φ₀ hα hφ h1 hφ₀ h01 a g₀ m hm u hu
  obtain ⟨b₀, k₀, hb₀, hk₀, rfl⟩ := P.fIwasawa_iwasawa σ hU.1 hU.2.1 g₀
  obtain ⟨mb, hmb⟩ := hL L ϖ σ q N hU a b₀
  obtain ⟨mk, hmk⟩ := hL L ϖ σ q N hU 0 k₀
  have e := levi_eq_mul hmb hmk hm
  have hkK : mk ∈ KU σ (N + 2) := levi_mem_K hU.2.1 hmk hk₀
  have hmbB : IsBorelU mb := levi_borel hmb hb₀
  have hu' : mk * u * mk⁻¹ ∈ radQ σ N := conj_mem_radU hmk.1 hu
  have hu'B := isUnipU_of_radQ hu'
  have e2 : m * u = (mb * (mk * u * mk⁻¹)) * 1 * mk := by rw [e]; group
  have d : ∀ (i : Fin (N + 2)) (x : L), mat mb i i = x →
      (((mb * (mk * u * mk⁻¹) : GU σ (N + 2)) : GL (Fin (N + 2)) L) : Matrix (Fin (N + 2)) (Fin (N + 2)) L) i i = x := by
    intro i x hx
    have := P.fSatake_borel_diag_mul hmbB hu'B.1 i
    rw [hu'B.2, mul_one] at this
    exact this.trans hx
  have e3 : φ₀ (b₀ * k₀) = chiDeltaU q (Fin.tail α) b₀ := by
    have := hφ₀ b₀ 1 k₀ hb₀ hk₀
    rwa [mul_one, h01, mul_one] at this
  rw [e2, hφ _ _ _ (P.fSatake_borel_mul hmbB hu'B.1) hkK, h1, mul_one, e3]
  unfold chiDeltaU
  rw [Fin.prod_univ_succ]
  congr 1
  · have h0 : ((0 : Fin (r + 1)) : ℕ) < N + 2 := by simp
    rw [dif_pos h0]
    have e0 : (⟨((0 : Fin (r + 1)) : ℕ), h0⟩ : Fin (N + 2)) = 0 := rfl
    rw [e0, d _ _ hmb.2.1, P.fSatake_ord_zpow hU.2.2.2.1]
    push_cast
    simp only [Fin.val_zero]
    congr 3
    push_cast
    ring
  · refine Finset.prod_congr rfl fun i _ => ?_
    have hi : i.val < N := by have := i.2; omega
    have hi' : (i.succ : Fin (r + 1)).val < N + 2 := by simp; omega
    rw [dif_pos hi, dif_pos hi']
    have ei : (⟨(i.succ : Fin (r + 1)).val, hi'⟩ : Fin (N + 2)) = mid ⟨i.val, hi⟩ := by
      ext; simp
    rw [ei, d _ _ (hmb.2.2.2 ⟨i.val, hi⟩ ⟨i.val, hi⟩)]
    have ex : ((N + 2 : ℕ) : ℤ) - 1 - 2 * ((i.succ : Fin (r + 1)).val : ℤ) = (N : ℤ) - 1 - 2 * (i.val : ℤ) := by
      simp; ring
    rw [ex]
    rfl

end GlobalTheory.CompanionTheory.InertTrans

end
