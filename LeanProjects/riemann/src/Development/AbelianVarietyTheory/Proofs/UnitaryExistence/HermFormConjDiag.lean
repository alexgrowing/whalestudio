import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ProdCastLESucc
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.EqTopOfForallEmbAllMem

open NumberField Matrix
open scoped nonZeroDivisors ComplexConjugate
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.FramePeriod

noncomputable section

lemma exists_upper_diag {n : ℕ} (q : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian)
    (hm : ∀ i : Fin (n + 1), 0 < FD.psgn q i * (FD.lminor A i).re) :
    ∃ (U : Matrix (Fin n) (Fin n) ℂ) (d : Fin n → ℝ), U.BlockTriangular id ∧ U.det = 1 ∧
      Uᵀ * A * U.map (starRingEnd ℂ) = Matrix.diagonal (fun a => (d a : ℂ)) ∧
      ∀ a : Fin n, 0 < FD.sgn q a * d a := by
  have hdet : ∀ c : Fin n, (FD.FrameDegreeData.blk A c).det ≠ 0 := by
    intro c h0
    have h := hm ⟨c, Nat.lt_succ_of_lt c.isLt⟩
    have : FD.lminor A ⟨c, Nat.lt_succ_of_lt c.isLt⟩ = 0 := h0
    rw [this] at h
    simp at h
  set U := FD.FrameDegreeData.uMat A with hU
  set B := Uᵀ * A * U.map (starRingEnd ℂ) with hB
  have hH : B.IsHermitian := by
    have := Matrix.isHermitian_mul_mul_conjTranspose Uᵀ hA
    exact this
  have hre : ∀ k, B k k = (((B k k).re : ℝ) : ℂ) := by
    intro k
    have h1 := congrFun (congrFun hH k) k
    rw [Matrix.conjTranspose_apply] at h1
    exact (Complex.conj_eq_iff_re.1 h1).symm
  have hBd : B = Matrix.diagonal (fun a => (((B a a).re : ℝ) : ℂ)) := by
    ext a c
    rcases lt_trichotomy a c with hac | hac | hac
    · rw [Matrix.diagonal_apply_ne _ (ne_of_lt hac)]
      have h1 := congrFun (congrFun hH a) c
      rw [Matrix.conjTranspose_apply] at h1
      rw [← h1, hB, hU, FD.FrameDegreeData.uGu_lower _ hdet hac, star_zero]
    · subst hac
      rw [Matrix.diagonal_apply_eq]; exact hre a
    · rw [Matrix.diagonal_apply_ne _ (ne_of_gt hac), hB, hU, FD.FrameDegreeData.uGu_lower _ hdet hac]
  have hprod : ∀ i : Fin (n + 1), FD.lminor A i =
      ∏ j : Fin i, (((B (Fin.castLE (Nat.le_of_lt_succ i.isLt) j)
        (Fin.castLE (Nat.le_of_lt_succ i.isLt) j)).re : ℝ) : ℂ) := by
    intro i
    have h1 : FD.lminor B i = FD.lminor A i := by
      rw [hB, hU, FD.FrameDegreeData.lminor_conj (FD.FrameDegreeData.uMat_upper _) i]
      simp only [FD.FrameDegreeData.uMat_diag, Finset.prod_const_one, one_mul, map_one, mul_one]
    rw [← h1]
    conv_lhs => rw [hBd]
    rw [FD.FrameDegreeData.lminor_diagonal]
  refine ⟨U, fun a => (B a a).re, FD.FrameDegreeData.uMat_upper _, ?_, hBd, fun k => ?_⟩
  · rw [hU, Matrix.det_of_isUpperTriangular (FD.FrameDegreeData.uMat_upper _)]
    simp only [FD.FrameDegreeData.uMat_diag, Finset.prod_const_one]
  · have hs : FD.lminor A k.succ = FD.lminor A k.castSucc * (((B k k).re : ℝ) : ℂ) := by
      rw [hprod k.succ, hprod k.castSucc]
      exact FD.FrameDegreeData.prod_castLE_succ (f := fun a => (((B a a).re : ℝ) : ℂ)) k.isLt
    have h1 := hm k.succ
    have h0 := hm k.castSucc
    rw [hs, Complex.re_mul_ofReal, Fin.val_succ, FD.FrameDegreeData.psgn_succ] at h1
    rw [Fin.val_castSucc] at h0
    refine (mul_pos_iff_of_pos_left h0).1 ?_
    simpa only [mul_assoc, mul_left_comm] using h1

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def locPer (τ : E →+* ℂ) (Gm : Matrix (Fin r) (Fin r) E) (q : ℕ) (M : Matrix (Fin r) (Fin r) ℂ) :
    (Fin r → ℂ) →ₗ[ℝ] (Fin r → ℂ) where
  toFun u a := if (a : ℕ) < q then FD.hermC τ Gm (FD.col M a) u else (M⁻¹ *ᵥ u) a
  map_add' u w := by
    funext a
    simp only [Pi.add_apply, FD.hermC_add_right, mulVec_add]
    split_ifs <;> rfl
  map_smul' t u := by
    funext a
    have : t • u = (t : ℂ) • u := by funext k; simp
    rw [this]
    simp only [FD.hermC_smul_right, mulVec_smul, Pi.smul_apply, RingHom.id_apply, Complex.conj_ofReal,
      smul_eq_mul, Complex.real_smul]
    split_ifs <;> rfl

lemma locPer_apply (τ : E →+* ℂ) (Gm : Matrix (Fin r) (Fin r) E) (q : ℕ) (M : Matrix (Fin r) (Fin r) ℂ)
    (u : Fin r → ℂ) (a : Fin r) : locPer τ Gm q M u a =
      if (a : ℕ) < q then FD.hermC τ Gm (FD.col M a) u else (M⁻¹ *ᵥ u) a := rfl

lemma hermForm_conj_diag {n : ℕ} (S : Matrix (Fin n) (Fin n) ℂ) (e : Fin n → ℝ) (z w : Fin n → ℂ) :
    hermForm (Sᵀ * Matrix.diagonal (fun a => (e a : ℂ)) * S.map (starRingEnd ℂ)) z w =
      ∑ a, (e a : ℂ) * ((S *ᵥ z) a * conj ((S *ᵥ w) a)) := by
  unfold hermForm
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
  simp only [dotProduct, mulVec_diagonal]
  refine Finset.sum_congr rfl fun a _ => ?_
  have : (S.map (starRingEnd ℂ) *ᵥ star w) a = conj ((S *ᵥ w) a) := by
    simp [mulVec, dotProduct]
  rw [this]; ring

lemma exists_loc (τ : E →+* ℂ) (Gm : Matrix (Fin r) (Fin r) E) (hG : ∀ a b, FD.cc (Gm a b) = Gm b a)
    (q : ℕ) (M : Matrix (Fin r) (Fin r) ℂ) (hM : M.det ≠ 0)
    (hm : ∀ i : Fin (r + 1), 0 < FD.psgn q i * (FD.lminor (FD.gram τ Gm M) i).re) :
    Function.Bijective (locPer τ Gm q M) ∧ ∃ Hl : Matrix (Fin r) (Fin r) ℂ, Hl.IsHermitian ∧
      (∀ z, z ≠ 0 → 0 < (hermForm Hl z z).re) ∧
      ∀ u w, (hermForm Hl (locPer τ Gm q M u) (locPer τ Gm q M w)).im = -(FD.hermC τ Gm u w).im := by
  obtain ⟨U, d, hU, hUd, hdiag, hd⟩ := exists_upper_diag q _ (FD.gram_isHermitian τ hG M) hm
  rw [← FD.FrameDegreeData.gram_mul] at hdiag
  have hUu : IsUnit U.det := by rw [hUd]; exact isUnit_one
  have hMu : IsUnit M.det := isUnit_iff_ne_zero.2 hM
  have hV : (U⁻¹).BlockTriangular id := by
    have := Matrix.invertibleOfIsUnitDet _ hUu
    exact Matrix.blockTriangular_inv_of_blockTriangular hU
  have hd0 : ∀ a, (d a : ℂ) ≠ 0 := fun a h => by
    have h1 := hd a
    rw [Complex.ofReal_eq_zero.1 h] at h1; simp at h1
  let c : (Fin r → ℂ) → Fin r → ℂ := fun u => U⁻¹ *ᵥ (M⁻¹ *ᵥ u)
  have hc : ∀ u, ∑ a, c u a • FD.col (M * U) a = u := by
    intro u
    rw [← FD.Data.mulVec_eq_sum_col]
    simp only [c, mulVec_mulVec]
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hUu, Matrix.mul_nonsing_inv _ hMu,
      one_mulVec]
  have hy : ∀ a b, FD.hermC τ Gm (FD.col (M * U) a) (FD.col (M * U) b) =
      if a = b then (d a : ℂ) else 0 := by
    intro a b
    have := congrFun (congrFun hdiag a) b
    simpa [FD.gram, diagonal_apply] using this
  have hyu : ∀ a u, FD.hermC τ Gm (FD.col (M * U) a) u = d a * conj (c u a) := by
    intro a u
    conv_lhs => rw [← hc u]
    rw [FD.hermC_sum_right]
    simp only [FD.hermC_smul_right, hy]
    simp [mul_comm]
  have huw : ∀ u w, FD.hermC τ Gm u w = ∑ a, (d a : ℂ) * (c u a * conj (c w a)) := by
    intro u w
    conv_lhs => rw [← hc u]
    rw [FD.hermC_sum_left]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [FD.hermC_smul_left, hyu]; ring
  let S : Matrix (Fin r) (Fin r) ℂ := Matrix.of fun a b => if (a : ℕ) < q then U b a / d a else U⁻¹ a b
  have hS : ∀ u a, (S *ᵥ locPer τ Gm q M u) a = if (a : ℕ) < q then conj (c u a) else c u a := by
    intro u a
    split_ifs with ha
    · have h1 : FD.col (M * U) a = ∑ b, U b a • FD.col M b := by
        funext k; simp [FD.col, Matrix.mul_apply, Finset.sum_apply, mul_comm]
      have h2 := hyu a u
      rw [h1, FD.hermC_sum_left] at h2
      rw [← mul_right_inj' (hd0 a), ← h2]
      simp only [mulVec, dotProduct, S, of_apply, if_pos ha, Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [FD.hermC_smul_left, locPer_apply]
      by_cases hb : (b : ℕ) < q
      · rw [if_pos hb]; field_simp [hd0 a]
      · have : U b a = 0 := hU (show a < b by rw [Fin.lt_def]; omega)
        simp [this]
    · simp only [c]
      rw [mulVec, mulVec, dotProduct, dotProduct]
      refine Finset.sum_congr rfl fun b _ => ?_
      simp only [S, of_apply, if_neg ha, locPer_apply]
      by_cases hb : (b : ℕ) < q
      · have : U⁻¹ a b = 0 := hV (show b < a by rw [Fin.lt_def]; omega)
        simp [this]
      · rw [if_neg hb]
  have hS0 : ∀ u, S *ᵥ locPer τ Gm q M u = 0 → u = 0 := by
    intro u hu
    have : c u = 0 := by
      funext a
      have := hS u a
      rw [hu] at this
      split_ifs at this
      · simpa using this.symm
      · exact this.symm
    rw [← hc u, this]; simp
  have hinj : Function.Injective (locPer τ Gm q M) := by
    rw [injective_iff_map_eq_zero]
    intro u hu
    apply hS0; rw [hu, mulVec_zero]
  have hsurj := LinearMap.injective_iff_surjective.1 hinj
  refine ⟨⟨hinj, hsurj⟩, Sᵀ * Matrix.diagonal (fun a : Fin r => ((FD.sgn q a * d a : ℝ) : ℂ)) *
    S.map (starRingEnd ℂ), ?_, ?_, ?_⟩
  · have h1 : (Matrix.diagonal (fun a : Fin r => ((FD.sgn q a * d a : ℝ) : ℂ))).IsHermitian := by
      rw [Matrix.isHermitian_diagonal_iff]
      intro a; exact Complex.conj_ofReal _
    have := Matrix.isHermitian_mul_mul_conjTranspose Sᵀ h1
    exact this
  · intro z hz
    obtain ⟨u, rfl⟩ := hsurj z
    have h1 : S *ᵥ locPer τ Gm q M u ≠ 0 := fun h => hz (by rw [hS0 u h, map_zero])
    obtain ⟨i, hi⟩ := Function.ne_iff.1 h1
    rw [hermForm_conj_diag S (fun a : Fin r => FD.sgn q a * d a), Complex.re_sum]
    simp only [Complex.mul_conj, ← Complex.ofReal_mul, Complex.ofReal_re]
    exact Finset.sum_pos' (fun j _ => mul_nonneg (hd j).le (Complex.normSq_nonneg _))
      ⟨i, Finset.mem_univ _, mul_pos (hd i) (Complex.normSq_pos.2 hi)⟩
  · intro u w
    rw [hermForm_conj_diag S (fun a : Fin r => FD.sgn q a * d a), huw, Complex.im_sum, Complex.im_sum,
      ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hS, hS, Complex.im_ofReal_mul, Complex.im_ofReal_mul, FD.sgn]
    split_ifs
    · simp; ring
    · ring

omit [IsCMField E] in

lemma trace_re (Ψ : Finset (E →+* ℂ))
    (h : ∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) (z : E) :
    ((Algebra.trace ℚ E z : ℚ) : ℝ) = ∑ τ : Ψ, 2 * (τ.1 z).re := by
  classical
  have h1 : algebraMap ℚ ℂ (Algebra.trace ℚ E z) = ∑ σ : E →ₐ[ℚ] ℂ, σ z :=
    trace_eq_sum_embeddings (K := ℚ) (E := ℂ) (x := z)
  have h2 : ∑ σ : E →ₐ[ℚ] ℂ, σ z = ∑ σ : E →+* ℂ, σ z :=
    (Fintype.sum_equiv (RingHom.equivRatAlgHom (R := E) (S := ℂ)) (fun σ : E →+* ℂ => σ z)
      (fun σ => σ z) (fun σ => rfl)).symm
  have h3 : ∑ σ ∈ Ψᶜ, σ z = ∑ σ ∈ Ψ, conj (σ z) := by
    refine Finset.sum_nbij' (fun σ => ComplexEmbedding.conjugate σ)
      (fun σ => ComplexEmbedding.conjugate σ) ?_ ?_ ?_ ?_ ?_
    · intro σ hσ
      have := h (ComplexEmbedding.conjugate σ)
      rw [ComplexEmbedding.involutive_conjugate E σ] at this
      simp only [Finset.mem_compl] at hσ
      exact this.mpr hσ
    · intro σ hσ
      simp only [Finset.mem_compl]
      exact (h σ).mp hσ
    · intro σ _; exact ComplexEmbedding.involutive_conjugate E σ
    · intro σ _; exact ComplexEmbedding.involutive_conjugate E σ
    · intro σ _; simp [ComplexEmbedding.conjugate_coe_eq]
  have h4 : ((Algebra.trace ℚ E z : ℚ) : ℂ) = ∑ σ ∈ Ψ, (σ z + conj (σ z)) := by
    rw [← eq_ratCast (algebraMap ℚ ℂ) (Algebra.trace ℚ E z), h1, h2,
      ← Finset.sum_add_sum_compl Ψ, h3, Finset.sum_add_distrib]
  apply Complex.ofReal_injective
  rw [Complex.ofReal_ratCast, h4, ← Finset.sum_coe_sort Ψ]
  push_cast
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Complex.add_conj]; push_cast; rfl

lemma cmType (H : Host E) (Ψ : Finset (E →+* ℂ)) (hΨ : ∀ τ, τ ∈ Ψ ↔ τ (H.rt : E) = H.rt0)
    (τ : E →+* ℂ) : τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ := by
  rw [hΨ, hΨ, ComplexEmbedding.conjugate_coe_eq]
  set z := τ (H.rt : E) with hz
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have h1 : z ^ 2 = -(H.d : ℂ) := by
    have := congrArg (fun a : 𝓞 E => τ (a : E)) H.rt_sq
    simpa using this
  have hc : conj z = -z := by
    have h2 : (conj z) ^ 2 = z ^ 2 := by rw [← map_pow, h1]; simp
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h2 with h | h
    · exfalso
      have h3 := Complex.conj_eq_iff_re.1 h
      rw [← h3] at h1
      have h4 : z.re ^ 2 = -(H.d : ℝ) := by exact_mod_cast h1
      nlinarith [sq_nonneg z.re]
    · exact h
  have hz0 : z ≠ 0 := by
    intro h
    rw [h] at h1
    have : (H.d : ℂ) = 0 := by simpa using h1
    exact hd.ne' (by exact_mod_cast this)
  rw [hc]
  constructor
  · intro h h'
    apply hz0
    linear_combination (h - h') / 2
  · intro h
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 (h1.trans H.sqrt_neg_disc_sq.symm) with h' | h'
    · exact h'
    · exact absurd (by rw [h', neg_neg]) h

omit [NumberField E] [IsCMField E] in
lemma card_fibre {Ψ : Finset (E →+* ℂ)} {g : ℕ} (idx : Fin g ≃ Ψ × Fin r) (σ : Ψ) (p : Fin g → Prop)
    (s : Fin r → Prop) (h : ∀ k, p k ↔ (idx k).1 = σ ∧ s (idx k).2) :
    Nat.card {k // p k} = Nat.card {a // s a} := by
  refine Nat.card_congr
    { toFun := fun k => ⟨(idx k.1).2, ((h k.1).1 k.2).2⟩
      invFun := fun a => ⟨idx.symm (σ, a.1), (h _).2 (by simpa using a.2)⟩
      left_inv := fun k => ?_
      right_inv := fun a => by simp }
  ext1
  simp only
  rw [← ((h k.1).1 k.2).1]; simp

lemma isTypeFn (H : Host E) (p q : ℕ) (Ψ : Finset (E →+* ℂ)) (hΨ : ∀ τ, τ ∈ Ψ ↔ τ (H.rt : E) = H.rt0)
    (g : ℕ) (idx : Fin g ≃ Ψ × Fin r) (ty : Fin g → (E →+* ℂ))
    (hty : ∀ k, ty k = if ((idx k).2 : ℕ) < q then ComplexEmbedding.conjugate (idx k).1.1
      else (idx k).1.1) (hr : r = p + q) : IsTypeFn H p q ty := by
  have hcm := cmType H Ψ hΨ
  have hq : Fintype.card {a : Fin r // (a : ℕ) < q} = q := by
    rw [Fintype.card_subtype, Fin.card_filter_val_lt]; omega
  intro τ
  rw [ne_eq, ← hΨ]
  constructor
  · intro hτ
    rw [card_fibre idx ⟨τ, hτ⟩ _ (fun a => ¬ (a : ℕ) < q), Nat.card_eq_fintype_card,
      Fintype.card_subtype_compl, hq, Fintype.card_fin]
    · omega
    · intro k
      rw [hty]
      split_ifs with hk
      · simp only [hk, not_true, and_false, iff_false]
        intro h
        exact (hcm _).1 (idx k).1.2 (h ▸ hτ)
      · simp [hk, Subtype.ext_iff]
  · intro hτ
    have hτ' : ComplexEmbedding.conjugate τ ∈ Ψ := by
      by_contra h; exact hτ ((hcm τ).2 h)
    rw [card_fibre idx ⟨_, hτ'⟩ _ (fun a => (a : ℕ) < q), Nat.card_eq_fintype_card, hq]
    intro k
    rw [hty]
    split_ifs with hk
    · simp only [hk, and_true, Subtype.ext_iff]
      constructor
      · rintro rfl; exact (ComplexEmbedding.involutive_conjugate E _).symm
      · intro h; rw [h]; exact ComplexEmbedding.involutive_conjugate E _
    · simp only [hk, and_false, iff_false]
      intro h
      exact hτ (h ▸ (idx k).1.2)

def allPer {Ψ : Finset (E →+* ℂ)} (Gm : Matrix (Fin r) (Fin r) E) (q : ℕ) (x : FD.Frame Ψ r) {g : ℕ}
    (idx : Fin g ≃ Ψ × Fin r) : (Ψ → Fin r → ℂ) →ₗ[ℝ] (Fin g → ℂ) where
  toFun y k := locPer (idx k).1.1 Gm q (FD.mat x (idx k).1) (y (idx k).1) (idx k).2
  map_add' u w := by funext k; simp
  map_smul' t u := by funext k; simp

lemma allPer_apply {Ψ : Finset (E →+* ℂ)} (Gm : Matrix (Fin r) (Fin r) E) (q : ℕ) (x : FD.Frame Ψ r)
    {g : ℕ} (idx : Fin g ≃ Ψ × Fin r) (y : Ψ → Fin r → ℂ) (k : Fin g) : allPer Gm q x idx y k =
      locPer (idx k).1.1 Gm q (FD.mat x (idx k).1) (y (idx k).1) (idx k).2 := rfl

lemma allPer_symm {Ψ : Finset (E →+* ℂ)} (Gm : Matrix (Fin r) (Fin r) E) (q : ℕ) (x : FD.Frame Ψ r)
    {g : ℕ} (idx : Fin g ≃ Ψ × Fin r) (y : Ψ → Fin r → ℂ) (τ : Ψ) :
    (fun a => allPer Gm q x idx y (idx.symm (τ, a))) = locPer τ.1 Gm q (FD.mat x τ) (y τ) := by
  funext a
  rw [allPer_apply, idx.apply_symm_apply]

lemma allPer_bijective {Ψ : Finset (E →+* ℂ)} (Gm : Matrix (Fin r) (Fin r) E) (q : ℕ)
    (x : FD.Frame Ψ r) {g : ℕ} (idx : Fin g ≃ Ψ × Fin r)
    (h : ∀ τ : Ψ, Function.Bijective (locPer τ.1 Gm q (FD.mat x τ))) :
    Function.Bijective (allPer Gm q x idx) := by
  constructor
  · intro y y' hy
    funext τ
    apply (h τ).1
    rw [← allPer_symm Gm q x idx, ← allPer_symm Gm q x idx, hy]
  · intro z
    choose y hy using fun τ : Ψ => (h τ).2 (fun a => z (idx.symm (τ, a)))
    refine ⟨y, funext fun k => ?_⟩
    rw [allPer_apply, hy]; simp

lemma hermForm_block {ι : Type} [Fintype ι] [DecidableEq ι] {g : ℕ} (idx : Fin g ≃ ι × Fin r)
    (s : ι → ℝ) (Hl : ι → Matrix (Fin r) (Fin r) ℂ) (z w : Fin g → ℂ) :
    hermForm (Matrix.of fun k l => if (idx k).1 = (idx l).1 then
      (s (idx k).1 : ℂ) * Hl (idx k).1 (idx k).2 (idx l).2 else 0) z w =
      ∑ τ, (s τ : ℂ) * hermForm (Hl τ) (fun a => z (idx.symm (τ, a))) (fun a => w (idx.symm (τ, a))) := by
  simp only [hermForm, dotProduct, mulVec, of_apply, Finset.mul_sum]
  rw [← idx.symm.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun a _ => ?_
  rw [← idx.symm.sum_comp, Fintype.sum_prod_type, Finset.sum_eq_single τ]
  · refine Finset.sum_congr rfl fun b _ => ?_
    simp only [Equiv.apply_symm_apply, if_true, Pi.star_apply]
    ring
  · intro σ _ hσ
    simp [hσ.symm]
  · simp

theorem isPeriod_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (r : ℕ) (ξ : E) (Gm : Matrix (Fin r) (Fin r) E) (φ : D.La →ₗ[𝓞 E] (Fin r → E)) (Ψ : Finset (E →+* ℂ)) (hΨ : ∀ τ, τ ∈ Ψ ↔ τ (H.rt : E) = H.rt0) (g : ℕ) (idx : Fin g ≃ Ψ × Fin r) (ty : Fin g → (E →+* ℂ)) (hty : ∀ k, ty k = if ((idx k).2 : ℕ) < D.q then ComplexEmbedding.conjugate (idx k).1.1 else (idx k).1.1), FD.cc ξ = -ξ → (∀ τ ∈ Ψ, 0 < (τ ξ).im) → (Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧ (∀ a b, FD.cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, ((D.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * FD.herm Gm (φ x) (φ y))) → r = D.p + D.q → IsTypeFn H D.p D.q ty ∧ ∀ x ∈ FD.GG Ψ Gm D.q, (∃ P : D.La →+ (Fin g → ℂ), (∀ v k, P v k = if ((idx k).2 : ℕ) < D.q then FD.hermC (idx k).1.1 Gm (FD.col (FD.mat x (idx k).1) (idx k).2) (FD.Data.emb (idx k).1.1 (φ v)) else ((FD.mat x (idx k).1)⁻¹ *ᵥ FD.Data.emb (idx k).1.1 (φ v)) (idx k).2)) ∧ ∀ P : D.La →+ (Fin g → ℂ), (∀ v k, P v k = if ((idx k).2 : ℕ) < D.q then FD.hermC (idx k).1.1 Gm (FD.col (FD.mat x (idx k).1) (idx k).2) (FD.Data.emb (idx k).1.1 (φ v)) else ((FD.mat x (idx k).1)⁻¹ *ᵥ FD.Data.emb (idx k).1.1 (φ v)) (idx k).2) → IsPeriod D ty P := by
  classical
  intro E _ _ _ H D r ξ Gm φ Ψ hΨ g idx ty hty hξ hpos ⟨hφ, hspan, hG, _, hEF⟩ hr
  refine ⟨isTypeFn H _ _ Ψ hΨ g idx ty hty hr, fun x hx => ?_⟩
  have hcm := cmType H Ψ hΨ
  have hloc := fun τ : Ψ => exists_loc τ.1 Gm hG D.q (FD.mat x τ) (hx τ).1 (hx τ).2
  refine ⟨⟨((allPer Gm D.q x idx).toAddMonoidHom.comp
    (CMLattice.embAll Ψ r).toAddMonoidHom).comp φ.toAddMonoidHom, fun v k => rfl⟩, fun P hP => ?_⟩
  have hP' : ∀ v, P v = allPer Gm D.q x idx (CMLattice.embAll Ψ r (φ v)) := fun v =>
    funext fun k => hP v k
  let L := LinearEquiv.ofBijective _ (allPer_bijective Gm D.q x idx fun τ => (hloc τ).1)
  have hL : ∀ y, L y = allPer Gm D.q x idx y := fun _ => rfl
  have := D.fin
  obtain ⟨b, hb⟩ := CMLattice.exists_basis_of_cmType Ψ hcm r (LinearMap.range φ)
    (Module.Finite.iff_fg.1 inferInstance) (by rw [LinearMap.coe_range]; exact hspan)
  have hrange : ∀ z, z ∈ Set.range P ↔ z ∈ Submodule.span ℤ (Set.range (b.map L)) := by
    intro z
    have h1 : Set.range (b.map L) = (L.toLinearMap.restrictScalars ℤ) '' Set.range b := by
      rw [← Set.range_comp]; congr 1
    rw [h1, ← Submodule.map_span, Submodule.mem_map]
    constructor
    · rintro ⟨v, rfl⟩
      exact ⟨_, (hb _).2 ⟨φ v, ⟨v, rfl⟩, rfl⟩, (hP' v).symm⟩
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨_, ⟨v, rfl⟩, rfl⟩ := (hb _).1 hy
      exact ⟨v, hP' v⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a v k
    have h1 : FD.Data.emb (idx k).1.1 (φ (a • v)) =
        (idx k).1.1 (a : E) • FD.Data.emb (idx k).1.1 (φ v) := by
      funext j
      simp [FD.Data.emb, Algebra.smul_def]
    rw [hP, hP, hty, h1]
    split_ifs
    · rw [FD.hermC_smul_right, ComplexEmbedding.conjugate_coe_eq]
    · rw [mulVec_smul]; rfl
  · intro v w hvw
    rw [hP', hP', ← hL, ← hL] at hvw
    have h1 := L.injective hvw
    obtain ⟨σ⟩ : Nonempty (E →+* ℂ) := inferInstance
    obtain ⟨τ, hτ⟩ : ∃ τ, τ ∈ Ψ := by
      by_cases h : ComplexEmbedding.conjugate σ ∈ Ψ
      · exact ⟨_, h⟩
      · exact ⟨σ, (hcm σ).2 h⟩
    apply hφ
    funext a
    exact τ.injective (congrFun (congrFun h1 ⟨τ, hτ⟩) a)
  · have h1 : P.range = (Submodule.span ℤ (Set.range (b.map L))).toAddSubgroup := by
      ext z; exact hrange z
    rw [h1]
    exact inferInstanceAs (DiscreteTopology (Submodule.span ℤ (Set.range (b.map L))))
  · rw [eq_top_iff, ← (b.map L).span_eq]
    exact Submodule.span_mono fun z hz => (hrange z).2 (Submodule.subset_span hz)
  · choose Hl hH hp hI using fun τ => (hloc τ).2
    refine ⟨Matrix.of fun k l => if (idx k).1 = (idx l).1 then
      ((2 * ((idx k).1.1 ξ).im : ℝ) : ℂ) * Hl (idx k).1 (idx k).2 (idx l).2 else 0, ?_, ?_, ?_⟩
    · ext k l
      simp only [conjTranspose_apply, of_apply]
      by_cases h : (idx k).1 = (idx l).1
      · rw [if_pos h, if_pos h.symm, star_mul', ← h, (hH _).apply]
        congr 1
        exact Complex.conj_ofReal _
      · rw [if_neg h, if_neg (Ne.symm h), star_zero]
    · intro z hz
      rw [hermForm_block idx (fun τ : Ψ => 2 * (τ.1 ξ).im) Hl, Complex.re_sum]
      simp only [Complex.re_ofReal_mul]
      obtain ⟨k, hk⟩ := Function.ne_iff.1 hz
      refine Finset.sum_pos' (fun τ _ => mul_nonneg (by linarith [hpos τ.1 τ.2]) ?_)
        ⟨(idx k).1, Finset.mem_univ _, mul_pos (by linarith [hpos _ (idx k).1.2]) (hp _ _ ?_)⟩
      · by_cases h : (fun a => z (idx.symm (τ, a))) = 0
        · rw [h]; simp [hermForm]
        · exact (hp _ _ h).le
      · intro h
        apply hk
        simpa using congrFun h (idx k).2
    · intro v w
      rw [hermForm_block idx (fun τ : Ψ => 2 * (τ.1 ξ).im) Hl, Complex.im_sum, hP', hP']
      have h1 : ((D.EF v w : ℤ) : ℝ) =
          ((Algebra.trace ℚ E (ξ * FD.herm Gm (φ v) (φ w)) : ℚ) : ℝ) := by
        rw [← hEF]; simp
      rw [h1, trace_re Ψ hcm]
      refine Finset.sum_congr rfl fun τ _ => ?_
      rw [allPer_symm, allPer_symm, Complex.im_ofReal_mul, hI, map_mul, ← FD.hermC_emb]
      have h2 : (τ.1 ξ).re = 0 := by
        have h3 := congrArg Complex.re (FD.emb_cc τ.1 ξ)
        rw [hξ, map_neg, Complex.neg_re, Complex.conj_re] at h3
        linarith
      rw [Complex.mul_re, h2]
      change _ * -(FD.hermC τ.1 Gm (FD.Data.emb τ.1 (φ v)) (FD.Data.emb τ.1 (φ w))).im = _
      ring

end

end GlobalTheory.FramePeriod
