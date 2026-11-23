import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaUniqueness.Skeleton
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaUniqueness.Lemmas

noncomputable section

open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

namespace PI.UnitaryGroupMassFormula.BetaLUniq

namespace GN

section Mat

variable {E : Type} [Field E] [StarRing E]

theorem adj_last {r : ℕ} (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    adjugate Z (Fin.last r) (Fin.last r) = det (Z.submatrix Fin.castSucc Fin.castSucc) := by
  rw [adjugate_fin_succ_eq_det_submatrix, Fin.succAbove_last, Fin.val_last, ← two_mul, pow_mul, neg_one_sq,
    one_pow, one_mul]

theorem last_eq {r : ℕ} (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (v : Fin (r + 1) → E) (x : E)
    (h : Z *ᵥ v = Pi.single (Fin.last r) x) :
    det Z * v (Fin.last r) = det (Z.submatrix Fin.castSucc Fin.castSucc) * x := by
  have h2 : (adjugate Z * Z) *ᵥ v = adjugate Z *ᵥ Pi.single (Fin.last r) x := by
    rw [← mulVec_mulVec, h]
  rw [adjugate_mul] at h2
  first
    | rw [smul_mulVec, one_mulVec] at h2
    | rw [Matrix.smul_mulVec_assoc, one_mulVec] at h2
  have h3 := congrFun h2 (Fin.last r)
  rw [Pi.smul_apply, smul_eq_mul, mulVec_single] at h3
  rw [h3]
  first
    | (simp only [Pi.smul_apply, op_smul_eq_mul, col_apply]; rw [adj_last])
    | (simp [adj_last]; done)
    | (simp [adj_last, mul_comm])

theorem vec_zero {r : ℕ} (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (v : Fin (r + 1) → E)
    (h : Z *ᵥ v = 0) (hl : v (Fin.last r) = 0)
    (hd : det Z ≠ 0 ∨ det (Z.submatrix Fin.castSucc Fin.castSucc) ≠ 0) : v = 0 := by
  rcases hd with hd | hd
  · exact eq_zero_of_mulVec_eq_zero hd h
  · have hs : (Z.submatrix Fin.castSucc Fin.castSucc) *ᵥ (v ∘ Fin.castSucc) = 0 := by
      funext i
      have h4 := congrFun h (Fin.castSucc i)
      simp only [mulVec, dotProduct, Fin.sum_univ_castSucc, hl, mul_zero, add_zero, Pi.zero_apply] at h4
      simpa [mulVec, dotProduct] using h4
    have h0 := eq_zero_of_mulVec_eq_zero hd hs
    funext i
    induction i using Fin.lastCases with
    | last => simpa using hl
    | cast j => simpa using congrFun h0 j

theorem key {r : ℕ} (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : E) (c c' : Fin (r + 1) → E)
    (h1 : Z *ᵥ c' = Pi.single (Fin.last r) (T * c (Fin.last r)))
    (h2 : Zᴴ *ᵥ c = Pi.single (Fin.last r) (T' * c' (Fin.last r)))
    (hG : det Z * star (det Z) - T * T' * (det (Z.submatrix Fin.castSucc Fin.castSucc) *
      star (det (Z.submatrix Fin.castSucc Fin.castSucc))) ≠ 0) : c = 0 ∧ c' = 0 := by
  set d := det (Z.submatrix Fin.castSucc Fin.castSucc) with hd
  have e1 := last_eq Z c' _ h1
  have hsub : det (Zᴴ.submatrix Fin.castSucc Fin.castSucc) = star d := by
    rw [hd, ← det_conjTranspose, conjTranspose_submatrix]
  have e2 := last_eq Zᴴ c _ h2
  rw [det_conjTranspose, hsub] at e2
  have hcl : c (Fin.last r) = 0 := by
    have h5 : (det Z * star (det Z) - T * T' * (d * star d)) * c (Fin.last r) = 0 := by
      linear_combination (det Z) * e2 + (star d * T') * e1
    exact (mul_eq_zero.mp h5).resolve_left hG
  have hcl' : c' (Fin.last r) = 0 := by
    have h5 : (det Z * star (det Z) - T * T' * (d * star d)) * c' (Fin.last r) = 0 := by
      linear_combination (star (det Z)) * e1 + (d * T) * e2
    exact (mul_eq_zero.mp h5).resolve_left hG
  have hnd : det Z ≠ 0 ∨ d ≠ 0 := by
    by_contra hc
    push_neg at hc
    apply hG
    rw [hc.1, hc.2]
    simp
  refine ⟨?_, ?_⟩
  · refine vec_zero Zᴴ c ?_ hcl ?_
    · rw [h2, hcl', mul_zero, Pi.single_zero]
    · rw [det_conjTranspose, hsub]
      rcases hnd with h6 | h6
      · exact Or.inl (star_ne_zero.mpr h6)
      · exact Or.inr (star_ne_zero.mpr h6)
  · exact vec_zero Z c' (by rw [h1, hcl, mul_zero, Pi.single_zero]) hcl' hnd

end Mat

section Flag

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

theorem fvec_castSucc {T : E} (F : FlagG S r T) (i : Fin r) : F.fvec i.castSucc = F.e i := by
  simp only [FlagG.fvec, Fin.snoc_castSucc]

theorem fvec_last {T : E} (F : FlagG S r T) : F.fvec (Fin.last r) = F.z := by
  simp only [FlagG.fvec, Fin.snoc_last]

theorem hT_z_e {T : E} (F : FlagG S r T) (i : Fin r) : S.hT F.z (F.e i) = 0 := by
  rw [← S.herm.eq (F.e i) F.z, F.z_orth i, map_zero]

theorem self_sum {T : E} (F : FlagG S r T) (c : Fin (r + 1) → E) (a : Fin (r + 1)) :
    ∑ a', c a' * S.hT (F.fvec a) (F.fvec a') =
      (Pi.single (Fin.last r) (-T * c (Fin.last r)) : Fin (r + 1) → E) a := by
  have hv : ∀ b : Fin (r + 1), S.hT (F.fvec a) (F.fvec b) =
      if a = Fin.last r ∧ b = Fin.last r then -T else 0 := by
    intro b
    induction a using Fin.lastCases with
    | last =>
      induction b using Fin.lastCases with
      | last => simp [fvec_last, F.z_norm]
      | cast j => simp [fvec_last, fvec_castSucc, hT_z_e, Fin.castSucc_ne_last]
    | cast i =>
      induction b using Fin.lastCases with
      | last => simp [fvec_last, fvec_castSucc, F.z_orth, Fin.castSucc_ne_last]
      | cast j => simp [fvec_castSucc, F.e_iso, Fin.castSucc_ne_last]
  simp only [hv]
  by_cases ha : a = Fin.last r
  · subst ha
    simp <;> ring
  · simp [ha]

theorem Dl_succ {T T' : E} (F : FlagG S r T) (F' : FlagG S r T') :
    Dl F F' (r + 1) = det (Zhat F F') := by
  unfold Dl leadMinorE
  rw [dif_pos le_rfl]
  rfl

theorem Dl_r {T T' : E} (F : FlagG S r T) (F' : FlagG S r T') :
    Dl F F' r = det ((Zhat F F').submatrix Fin.castSucc Fin.castSucc) := by
  unfold Dl leadMinorE
  rw [dif_pos (Nat.le_succ r)]
  rfl

theorem coeffs_zero {T T' : E} (F : FlagG S r T) (F' : FlagG S r T') (c c' : Fin (r + 1) → E)
    (w : S.V) (hw : w = ∑ a, c a • F.fvec a + ∑ b, c' b • F'.fvec b)
    (h1 : ∀ a, S.hT (F.fvec a) w = 0) (h2 : ∀ b, S.hT (F'.fvec b) w = 0)
    (hG : Gflag F F' ≠ 0) : c = 0 ∧ c' = 0 := by
  have hl1 : ∀ a, S.hT (F.fvec a) w = (Pi.single (Fin.last r) (-T * c (Fin.last r)) : Fin (r + 1) → E) a +
      (Zhat F F' *ᵥ c') a := by
    intro a
    rw [hw, map_add, map_sum, map_sum, ← self_sum F c a]
    simp only [map_smul, smul_eq_mul]
    congr 1
    simp only [mulVec, dotProduct, Zhat, brS]
    exact Finset.sum_congr rfl (fun b _ => mul_comm _ _)
  have hl2 : ∀ b, S.hT (F'.fvec b) w = ((Zhat F F')ᴴ *ᵥ c) b +
      (Pi.single (Fin.last r) (-T' * c' (Fin.last r)) : Fin (r + 1) → E) b := by
    intro b
    rw [hw, map_add, map_sum, map_sum, ← self_sum F' c' b]
    simp only [map_smul, smul_eq_mul]
    congr 1
    simp only [mulVec, dotProduct, conjTranspose_apply, Zhat, brS]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [← S.herm.eq (F.fvec a) (F'.fvec b), starRingEnd_apply, mul_comm]
  have k1 : Zhat F F' *ᵥ c' = Pi.single (Fin.last r) (T * c (Fin.last r)) := by
    funext a
    have h7 := hl1 a
    rw [h1 a] at h7
    have e : (Pi.single (Fin.last r) (T * c (Fin.last r)) : Fin (r + 1) → E) a =
        -((Pi.single (Fin.last r) (-T * c (Fin.last r)) : Fin (r + 1) → E) a) := by
      rw [neg_mul, Pi.single_neg, Pi.neg_apply, neg_neg]
    rw [e]
    linear_combination -h7
  have k2 : (Zhat F F')ᴴ *ᵥ c = Pi.single (Fin.last r) (T' * c' (Fin.last r)) := by
    funext b
    have h7 := hl2 b
    rw [h2 b] at h7
    have e : (Pi.single (Fin.last r) (T' * c' (Fin.last r)) : Fin (r + 1) → E) b =
        -((Pi.single (Fin.last r) (-T' * c' (Fin.last r)) : Fin (r + 1) → E) b) := by
      rw [neg_mul, Pi.single_neg, Pi.neg_apply, neg_neg]
    rw [e]
    linear_combination -h7
  have hG' : det (Zhat F F') * star (det (Zhat F F')) - T * T' *
      (det ((Zhat F F').submatrix Fin.castSucc Fin.castSucc) *
        star (det ((Zhat F F').submatrix Fin.castSucc Fin.castSucc))) ≠ 0 := by
    rw [← Dl_succ, ← Dl_r]
    exact hG
  exact key (Zhat F F') T T' c c' k1 k2 hG'

end Flag

end GN

open GN in
theorem gram_matrix_nondegenerate : GramNondeg := by
  intro E _ _ _ S Λ r T T' F F' hΛ hL hL' hG
  let v : Fin (r + 1) ⊕ Fin (r + 1) → S.V := Sum.elim F.fl.fvec F'.fl.fvec
  have hsp : UUE Λ F F' = Submodule.span E (Set.range v) := by
    have hX : ∀ {T₀ : E} (F₀ : LFlag S r T₀), (∀ a, v (Sum.inl a) = F₀.fl.fvec a) ∨
        (∀ b, v (Sum.inr b) = F₀.fl.fvec b) → Xsp F₀ ≤ Submodule.span E (Set.range v) := by
      intro T₀ F₀ h
      apply Submodule.span_mono
      rintro _ ⟨i, rfl⟩
      rcases h with h | h
      · exact ⟨Sum.inl i.castSucc, by rw [h, fvec_castSucc]⟩
      · exact ⟨Sum.inr i.castSucc, by rw [h, fvec_castSucc]⟩
    apply le_antisymm
    · unfold UUE spanE
      rw [Submodule.span_le]
      have hU : UU Λ F F' ≤ (Submodule.span E (Set.range v)).restrictScalars (𝓞 E) := by
        unfold UU
        refine sup_le (sup_le (sup_le ?_ ?_) ?_) ?_
        · intro y hy
          exact hX F (Or.inl fun _ => rfl) hy.2
        · rw [Submodule.span_le, hL.2]
          rintro _ rfl
          exact Submodule.subset_span ⟨Sum.inl (Fin.last r), by simp [v, fvec_last]⟩
        · intro y hy
          exact hX F' (Or.inr fun _ => rfl) hy.2
        · rw [Submodule.span_le, hL'.2]
          rintro _ rfl
          exact Submodule.subset_span ⟨Sum.inr (Fin.last r), by simp [v, fvec_last]⟩
      exact hU
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      rcases i with a | b
      · refine Fin.lastCases ?_ (fun i => ?_) a
        · show F.fl.fvec (Fin.last r) ∈ UUE Λ F F'
          rw [fvec_last, ← hL.2]
          apply Submodule.subset_span
          unfold UU
          exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_right
            (Submodule.mem_span_singleton_self _)))
        · show F.fl.fvec i.castSucc ∈ UUE Λ F F'
          rw [fvec_castSucc]
          exact Xsp_le_UUE S Λ hΛ F F' (Submodule.subset_span ⟨i, rfl⟩)
      · refine Fin.lastCases ?_ (fun i => ?_) b
        · show F'.fl.fvec (Fin.last r) ∈ UUE Λ F F'
          rw [fvec_last, ← hL'.2]
          apply Submodule.subset_span
          unfold UU
          exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
        · show F'.fl.fvec i.castSucc ∈ UUE Λ F F'
          rw [fvec_castSucc]
          exact Xsp_le_UUE' S Λ hΛ F F' (Submodule.subset_span ⟨i, rfl⟩)
  have hcoef : ∀ g : Fin (r + 1) ⊕ Fin (r + 1) → E,
      (∀ a, S.hT (F.fl.fvec a) (∑ i, g i • v i) = 0) →
      (∀ b, S.hT (F'.fl.fvec b) (∑ i, g i • v i) = 0) → g = 0 := by
    intro g h1 h2
    have hw : ∑ i, g i • v i =
        ∑ a, g (Sum.inl a) • F.fl.fvec a + ∑ b, g (Sum.inr b) • F'.fl.fvec b := by
      simp [v, Fintype.sum_sum_type]
    obtain ⟨hc, hc'⟩ := coeffs_zero F.fl F'.fl _ _ _ hw h1 h2 hG
    funext i
    rcases i with a | b
    · exact congrFun hc a
    · exact congrFun hc' b
  have hli : LinearIndependent E v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have := hcoef g (by simp [hg]) (by simp [hg])
    intro i
    simp [this]
  constructor
  · rw [hsp, finrank_span_eq_card hli]
    simp
    ring
  · rw [eq_bot_iff]
    intro w hw
    rw [Submodule.mem_inf, hsp] at hw
    obtain ⟨hw1, hw2⟩ := hw
    obtain ⟨g, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hw1
    rw [mem_orth] at hw2
    have hg := hcoef g (fun a => hw2 _ (Submodule.subset_span ⟨Sum.inl a, rfl⟩))
      (fun b => hw2 _ (Submodule.subset_span ⟨Sum.inr b, rfl⟩))
    simp [hg]

end PI.UnitaryGroupMassFormula.BetaLUniq
