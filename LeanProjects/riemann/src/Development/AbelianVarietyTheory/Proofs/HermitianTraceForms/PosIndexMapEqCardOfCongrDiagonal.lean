import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.ExistsOrthogonalBasisDotProductApplyEq

namespace GlobalTheory.Inertia

open Module Matrix ReciprocityTheory.ChartRestriction.G
open scoped ComplexConjugate

section Complex

variable {n m : Type*} [Fintype n] [Fintype m]

def posDims (G : Matrix n n ℂ) : Set ℕ :=
  {d | ∃ W : Submodule ℂ (n → ℂ), finrank ℂ W = d ∧
    ∀ x ∈ W, x ≠ 0 → 0 < (x ⬝ᵥ G *ᵥ star x).re}

noncomputable def posIndex (G : Matrix n n ℂ) : ℕ := sSup (posDims G)

noncomputable def negIndex (G : Matrix n n ℂ) : ℕ := posIndex (-G)

theorem zero_mem_posDims (G : Matrix n n ℂ) : 0 ∈ posDims G :=
  ⟨⊥, finrank_bot ℂ _, fun x hx hx0 => (hx0 (by simpa using hx)).elim⟩

theorem le_card_of_mem_posDims {G : Matrix n n ℂ} {d : ℕ} (hd : d ∈ posDims G) :
    d ≤ Fintype.card n := by
  obtain ⟨W, rfl, -⟩ := hd
  simpa using W.finrank_le

theorem isGreatest_posIndex (G : Matrix n n ℂ) : IsGreatest (posDims G) (posIndex G) := by
  have hb : BddAbove (posDims G) := ⟨_, fun _ hd => le_card_of_mem_posDims hd⟩
  exact ⟨Nat.sSup_mem ⟨0, zero_mem_posDims G⟩ hb, fun _ hd => le_csSup hb hd⟩

theorem isGreatest_negIndex (G : Matrix n n ℂ) :
    IsGreatest {d | ∃ W : Submodule ℂ (n → ℂ), finrank ℂ W = d ∧
      ∀ x ∈ W, x ≠ 0 → (x ⬝ᵥ G *ᵥ star x).re < 0} (negIndex G) := by
  have h := isGreatest_posIndex (-G)
  simpa only [negIndex, posDims, neg_mulVec, dotProduct_neg, Complex.neg_re, Left.neg_pos_iff] using h

theorem posIndex_le_card (G : Matrix n n ℂ) : posIndex G ≤ Fintype.card n :=
  le_card_of_mem_posDims (isGreatest_posIndex G).1

theorem negIndex_le_card (G : Matrix n n ℂ) : negIndex G ≤ Fintype.card n :=
  posIndex_le_card _

@[simp] theorem posIndex_neg (G : Matrix n n ℂ) : posIndex (-G) = negIndex G := rfl

@[simp] theorem negIndex_neg (G : Matrix n n ℂ) : negIndex (-G) = posIndex G := by
  rw [negIndex, neg_neg]

theorem dotProduct_congr_mulVec_star (G : Matrix n n ℂ) (P : Matrix n m ℂ) (x y : m → ℂ) :
    x ⬝ᵥ (Pᵀ * G * P.map conj) *ᵥ star y = (P *ᵥ x) ⬝ᵥ G *ᵥ star (P *ᵥ y) := by
  have h : star (P *ᵥ y) = P.map conj *ᵥ star y := by
    ext k
    simp [mulVec, dotProduct]
  rw [h, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec x, vecMul_transpose]

theorem posIndex_congr_le (G : Matrix n n ℂ) {P : Matrix n m ℂ}
    (hP : Function.Injective P.mulVec) : posIndex (Pᵀ * G * P.map conj) ≤ posIndex G := by
  obtain ⟨W, hW, hpos⟩ := (isGreatest_posIndex (Pᵀ * G * P.map conj)).1
  refine (isGreatest_posIndex G).2 ⟨W.map P.mulVecLin, ?_, ?_⟩
  · rw [← hW]
    exact (Submodule.equivMapOfInjective P.mulVecLin hP W).finrank_eq.symm
  · rintro _ ⟨x, hx, rfl⟩ hx0
    have := hpos x hx (by rintro rfl; simp at hx0)
    rwa [dotProduct_congr_mulVec_star] at this

theorem congr_mul {l : Type*} (G : Matrix n n ℂ) (P : Matrix n m ℂ) (Q : Matrix m l ℂ) :
    (P * Q)ᵀ * G * (P * Q).map conj = Qᵀ * (Pᵀ * G * P.map conj) * Q.map conj := by
  rw [transpose_mul, Matrix.map_mul]
  simp only [Matrix.mul_assoc]

theorem posIndex_submatrix_equiv (G : Matrix n n ℂ) (e : m ≃ n) :
    posIndex (G.submatrix e e) = posIndex G := by
  have h : ∀ x : n → ℂ, (x ∘ e) ⬝ᵥ G.submatrix e e *ᵥ star (x ∘ e) = x ⬝ᵥ G *ᵥ star x := by
    intro x
    have h1 : star (x ∘ e) ∘ e.symm = star x := by
      ext k
      simp
    rw [submatrix_mulVec_equiv, h1]
    exact comp_equiv_dotProduct_comp_equiv x (G *ᵥ star x) e
  let L : (n → ℂ) ≃ₗ[ℂ] (m → ℂ) := LinearEquiv.funCongrLeft ℂ ℂ e
  have hL : ∀ x, L x = x ∘ e := fun _ => rfl
  refine (isGreatest_posIndex _).unique ?_
  have hs : posDims (G.submatrix e e) = posDims G := by
    ext d
    constructor
    · rintro ⟨W, rfl, hW⟩
      refine ⟨W.map L.symm.toLinearMap, LinearEquiv.finrank_map_eq _ _, ?_⟩
      rintro _ ⟨y, hy, rfl⟩ h0
      rw [← h, ← hL]
      simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
      exact hW y hy (by rintro rfl; simp at h0)
    · rintro ⟨W, rfl, hW⟩
      refine ⟨W.map L.toLinearMap, LinearEquiv.finrank_map_eq _ _, ?_⟩
      rintro _ ⟨y, hy, rfl⟩ h0
      simp only [LinearEquiv.coe_coe, hL, h]
      exact hW y hy (by rintro rfl; simp at h0)
  rw [hs]
  exact isGreatest_posIndex G

theorem negIndex_submatrix_equiv (G : Matrix n n ℂ) (e : m ≃ n) :
    negIndex (G.submatrix e e) = negIndex G :=
  posIndex_submatrix_equiv (-G) e

variable [DecidableEq n]

theorem posIndex_congr (G : Matrix n n ℂ) {P : Matrix n n ℂ} (hP : P.det ≠ 0) :
    posIndex (Pᵀ * G * P.map conj) = posIndex G := by
  have hu : IsUnit P.det := hP.isUnit
  refine le_antisymm (posIndex_congr_le G (mulVec_injective_iff_isUnit.2
    ((isUnit_iff_isUnit_det P).2 hu))) ?_
  have h := posIndex_congr_le (Pᵀ * G * P.map conj) (P := P⁻¹)
    (mulVec_injective_iff_isUnit.2 ((isUnit_iff_isUnit_det _).2 (isUnit_nonsing_inv_det P hu)))
  rw [← congr_mul, mul_nonsing_inv P hu] at h
  simpa using h

theorem negIndex_congr (G : Matrix n n ℂ) {P : Matrix n n ℂ} (hP : P.det ≠ 0) :
    negIndex (Pᵀ * G * P.map conj) = negIndex G := by
  rw [negIndex, negIndex, ← posIndex_congr (-G) hP, Matrix.mul_neg, Matrix.neg_mul]

theorem re_dotProduct_diagonal_mulVec_star (d x : n → ℂ) :
    (x ⬝ᵥ diagonal d *ᵥ star x).re = ∑ k, (d k).re * Complex.normSq (x k) := by
  simp only [dotProduct, mulVec_diagonal, Complex.re_sum, Pi.star_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_left_comm, Complex.star_def, Complex.mul_conj, Complex.re_mul_ofReal]

theorem posIndex_diagonal (d : n → ℂ) :
    posIndex (diagonal d) = (Finset.univ.filter fun k => 0 < (d k).re).card := by
  refine (isGreatest_posIndex _).unique
    ⟨⟨Pi.spanSubset ℂ {k | 0 < (d k).re}, ?_, fun x hx hx0 => ?_⟩, ?_⟩
  · rw [Pi.dim_spanSubset, Set.ncard_eq_toFinset_card']
    simp
  · rw [re_dotProduct_diagonal_mulVec_star]
    have hx' := Pi.mem_spanSubset_iff.1 hx
    obtain ⟨k, hk⟩ := Function.ne_iff.1 hx0
    refine Finset.sum_pos' (fun j _ => ?_) ⟨k, Finset.mem_univ _, ?_⟩
    · by_cases hj : 0 < (d j).re
      · exact mul_nonneg hj.le (Complex.normSq_nonneg _)
      · simp [hx' j hj]
    · have hk' : 0 < (d k).re := by
        by_contra h
        exact hk (hx' k h)
      exact mul_pos hk' (Complex.normSq_pos.2 hk)
  · rintro _ ⟨W, rfl, hW⟩
    set S := Finset.univ.filter fun k => 0 < (d k).re with hS
    let f : W →ₗ[ℂ] (S → ℂ) := (LinearMap.funLeft ℂ ℂ (Subtype.val : S → n)).comp W.subtype
    have hf : Function.Injective f := by
      rw [injective_iff_map_eq_zero]
      intro x hx
      refine Subtype.ext ?_
      by_contra hx0
      refine (hW x x.2 hx0).not_ge ?_
      rw [re_dotProduct_diagonal_mulVec_star]
      refine Finset.sum_nonpos fun k _ => ?_
      by_cases hk : 0 < (d k).re
      · have : (x : n → ℂ) k = 0 := congrFun hx ⟨k, by simpa [hS] using hk⟩
        simp [this]
      · exact mul_nonpos_of_nonpos_of_nonneg (not_lt.1 hk) (Complex.normSq_nonneg _)
    simpa using LinearMap.finrank_le_finrank_of_injective hf

theorem negIndex_diagonal (d : n → ℂ) :
    negIndex (diagonal d) = (Finset.univ.filter fun k => (d k).re < 0).card := by
  rw [negIndex, diagonal_neg, posIndex_diagonal]
  simp

theorem posIndex_eq_card_of_congr_diagonal {G P : Matrix n n ℂ} {d : n → ℂ} (hP : P.det ≠ 0)
    (hd : Pᵀ * G * P.map conj = diagonal d) :
    posIndex G = (Finset.univ.filter fun k => 0 < (d k).re).card := by
  rw [← posIndex_congr G hP, hd, posIndex_diagonal]

theorem negIndex_eq_card_of_congr_diagonal {G P : Matrix n n ℂ} {d : n → ℂ} (hP : P.det ≠ 0)
    (hd : Pᵀ * G * P.map conj = diagonal d) :
    negIndex G = (Finset.univ.filter fun k => (d k).re < 0).card := by
  rw [← negIndex_congr G hP, hd, negIndex_diagonal]

theorem exists_congr_diagonal_real {G : Matrix n n ℂ} (hG : G.IsHermitian) :
    ∃ (P : Matrix n n ℂ) (d : n → ℝ), P.det ≠ 0 ∧
      Pᵀ * G * P.map conj = diagonal (fun k => (d k : ℂ)) ∧ (G.det ≠ 0 → ∀ k, d k ≠ 0) := by
  obtain ⟨P, d, hP, hd, hre, hne⟩ := HermDiag.exists_congr_diagonal (c := starRingEnd ℂ)
    two_ne_zero Complex.conj_conj (G := G) (fun a b => hG.apply b a)
  have h : ∀ k, (((d k).re : ℝ) : ℂ) = d k := fun k => Complex.conj_eq_iff_re.1 (hre k)
  refine ⟨P, fun k => (d k).re, hP, by simpa only [h] using hd, fun hG0 k hk => hne hG0 k ?_⟩
  rw [← h k, show (d k).re = 0 from hk, Complex.ofReal_zero]

theorem posIndex_add_negIndex_eq_rank {G : Matrix n n ℂ} (hG : G.IsHermitian) :
    posIndex G + negIndex G = G.rank := by
  obtain ⟨P, d, hP, hd, -⟩ := exists_congr_diagonal_real hG
  have hr : (Pᵀ * G * P.map conj).rank = G.rank := by
    rw [rank_mul_eq_left_of_isUnit_det, rank_mul_eq_right_of_isUnit_det]
    · rw [det_transpose]
      exact hP.isUnit
    · have hm : (P.map conj).det = conj P.det := (RingHom.map_det (starRingEnd ℂ) P).symm
      rw [hm]
      exact ((map_ne_zero _).2 hP).isUnit
  rw [posIndex_eq_card_of_congr_diagonal hP hd, negIndex_eq_card_of_congr_diagonal hP hd, ← hr, hd,
    rank_diagonal, Fintype.card_subtype, ← Finset.card_union_of_disjoint, ← Finset.filter_or]
  · congr 1
    ext k
    simp [lt_or_lt_iff_ne, eq_comm]
  · rw [Finset.disjoint_filter]
    exact fun k _ h1 h2 => lt_asymm h1 h2

theorem posIndex_add_negIndex {G : Matrix n n ℂ} (hG : G.IsHermitian) (hG0 : G.det ≠ 0) :
    posIndex G + negIndex G = Fintype.card n := by
  rw [posIndex_add_negIndex_eq_rank hG,
    rank_of_isUnit G ((isUnit_iff_isUnit_det G).2 hG0.isUnit)]

theorem posIndex_neg_eq_sub {G : Matrix n n ℂ} (hG : G.IsHermitian) (hG0 : G.det ≠ 0) :
    posIndex (-G) = Fintype.card n - posIndex G := by
  have := posIndex_add_negIndex hG hG0
  rw [posIndex_neg]
  omega

theorem exists_congr_diagonal_eigenvalues {G : Matrix n n ℂ} (hG : G.IsHermitian) :
    ∃ P : Matrix n n ℂ, P.det ≠ 0 ∧
      Pᵀ * G * P.map conj = diagonal fun k => (hG.eigenvalues k : ℂ) := by
  have h := hG.conjStarAlgAut_star_eigenvectorUnitary
  rw [Unitary.conjStarAlgAut_star_apply] at h
  set U : Matrix n n ℂ := (hG.eigenvectorUnitary : Matrix n n ℂ) with hU
  have hdet : U.det ≠ 0 := by
    have h1 : star U * U = 1 := Unitary.coe_star_mul_self _
    have h2 := congrArg det h1
    rw [det_mul, det_one] at h2
    exact right_ne_zero_of_mul_eq_one h2
  have hm : (U.map conj).det = conj U.det := (RingHom.map_det (starRingEnd ℂ) U).symm
  refine ⟨U.map conj, hm ▸ (map_ne_zero _).2 hdet, ?_⟩
  have h3 : (U.map conj).map conj = U := by
    ext a b
    simp
  rw [h3]
  exact h

theorem posIndex_eq_card_eigenvalues {G : Matrix n n ℂ} (hG : G.IsHermitian) :
    posIndex G = (Finset.univ.filter fun k => 0 < hG.eigenvalues k).card := by
  obtain ⟨P, hP, hd⟩ := exists_congr_diagonal_eigenvalues hG
  rw [posIndex_eq_card_of_congr_diagonal hP hd]
  simp

theorem negIndex_eq_card_eigenvalues {G : Matrix n n ℂ} (hG : G.IsHermitian) :
    negIndex G = (Finset.univ.filter fun k => hG.eigenvalues k < 0).card := by
  obtain ⟨P, hP, hd⟩ := exists_congr_diagonal_eigenvalues hG
  rw [negIndex_eq_card_of_congr_diagonal hP hd]
  simp

open scoped ComplexOrder in

theorem posDef_iff_posIndex_eq_card {G : Matrix n n ℂ} (hG : G.IsHermitian) :
    G.PosDef ↔ posIndex G = Fintype.card n := by
  rw [hG.posDef_iff_eigenvalues_pos, posIndex_eq_card_eigenvalues hG, ← Finset.card_univ,
    Finset.card_filter_eq_iff]
  simp

theorem posIndex_map_conj {G : Matrix n n ℂ} (hG : G.IsHermitian) :
    posIndex (G.map conj) = posIndex G := by
  obtain ⟨P, d, hP, hd, -⟩ := exists_congr_diagonal_real hG
  have hm : (P.map conj).det = conj P.det := (RingHom.map_det (starRingEnd ℂ) P).symm
  have hd' : (P.map conj)ᵀ * G.map conj * (P.map conj).map conj =
      diagonal (fun k => (d k : ℂ)) := by
    rw [← transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, hd, diagonal_map (map_zero _)]
    simp
  rw [posIndex_eq_card_of_congr_diagonal hP hd,
    posIndex_eq_card_of_congr_diagonal (hm ▸ (map_ne_zero _).2 hP) hd']

theorem negIndex_map_conj {G : Matrix n n ℂ} (hG : G.IsHermitian) :
    negIndex (G.map conj) = negIndex G := by
  rw [negIndex, negIndex, ← posIndex_map_conj hG.neg, Matrix.map_neg _ (map_neg _)]

theorem posIndex_fromBlocks [DecidableEq m] {G : Matrix n n ℂ} {H : Matrix m m ℂ}
    (hG : G.IsHermitian) (hH : H.IsHermitian) :
    posIndex (fromBlocks G 0 0 H) = posIndex G + posIndex H := by
  obtain ⟨P, d, hP, hd, -⟩ := exists_congr_diagonal_real hG
  obtain ⟨Q, e, hQ, he, -⟩ := exists_congr_diagonal_real hH
  have h : (fromBlocks P 0 0 Q)ᵀ * fromBlocks G 0 0 H * (fromBlocks P 0 0 Q).map conj =
      diagonal (Sum.elim (fun k => (d k : ℂ)) (fun k => (e k : ℂ))) := by
    rw [← fromBlocks_diagonal, ← hd, ← he, fromBlocks_transpose, fromBlocks_map,
      fromBlocks_multiply, fromBlocks_multiply]
    simp
  have hdet : (fromBlocks P 0 0 Q).det ≠ 0 := by
    rw [det_fromBlocks_zero₂₁]
    exact mul_ne_zero hP hQ
  rw [posIndex_eq_card_of_congr_diagonal hdet h, posIndex_eq_card_of_congr_diagonal hP hd,
    posIndex_eq_card_of_congr_diagonal hQ he]
  simp only [Finset.card_filter, Fintype.sum_sum_type]
  rfl

theorem negIndex_fromBlocks [DecidableEq m] {G : Matrix n n ℂ} {H : Matrix m m ℂ}
    (hG : G.IsHermitian) (hH : H.IsHermitian) :
    negIndex (fromBlocks G 0 0 H) = negIndex G + negIndex H := by
  rw [negIndex, negIndex, negIndex, ← posIndex_fromBlocks hG.neg hH.neg, fromBlocks_neg]
  simp

theorem exists_congr_diagonal_of_card_eq {G : Matrix n n ℂ} (hG : G.IsHermitian)
    (hG0 : G.det ≠ 0) {e : n → ℝ} (he : ∀ k, e k ≠ 0)
    (hcard : (Finset.univ.filter fun k => 0 < e k).card = posIndex G) :
    ∃ P : Matrix n n ℂ, P.det ≠ 0 ∧ Pᵀ * G * P.map conj = diagonal fun k => (e k : ℂ) := by
  obtain ⟨P, d, hP, hd, hne⟩ := exists_congr_diagonal_real hG
  replace hne := hne hG0
  rw [posIndex_eq_card_of_congr_diagonal hP hd] at hcard
  simp only [Complex.ofReal_re] at hcard
  rw [← Fintype.card_subtype, ← Fintype.card_subtype] at hcard
  let f : {k // 0 < e k} ≃ {k // 0 < d k} := Fintype.equivOfCardEq hcard
  let σ : Equiv.Perm n := f.extendSubtype
  have hσ : ∀ k, 0 < e k / d (σ k) := by
    intro k
    by_cases hk : 0 < e k
    · exact div_pos hk (f.extendSubtype_mem k hk)
    · exact div_pos_of_neg_of_neg ((not_lt.1 hk).lt_of_ne (he k))
        ((not_lt.1 (f.extendSubtype_not_mem k hk)).lt_of_ne (hne _))
  have h1 : (P.submatrix id σ)ᵀ * G * (P.submatrix id σ).map conj =
      diagonal fun k => (d (σ k) : ℂ) := by
    have : (P.submatrix id σ)ᵀ * G * (P.submatrix id σ).map conj =
        (Pᵀ * G * P.map conj).submatrix σ σ := rfl
    rw [this, hd, submatrix_diagonal_equiv]
    rfl
  refine ⟨P.submatrix id σ * diagonal fun k => (√(e k / d (σ k)) : ℂ), ?_, ?_⟩
  · rw [det_mul, det_permute', det_diagonal]
    refine mul_ne_zero (mul_ne_zero ?_ hP) (Finset.prod_ne_zero_iff.2 fun k _ => ?_)
    · rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
    · exact Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 (hσ k)).ne'
  · rw [congr_mul, h1, diagonal_transpose, diagonal_map (map_zero _), diagonal_mul_diagonal,
      diagonal_mul_diagonal]
    congr 1
    ext k
    rw [Complex.conj_ofReal, ← Complex.ofReal_mul, ← Complex.ofReal_mul, mul_right_comm,
      Real.mul_self_sqrt (hσ k).le, div_mul_cancel₀ _ (hne _)]

theorem exists_congr_iff_posIndex_eq {G H : Matrix n n ℂ} (hG : G.IsHermitian) (hG0 : G.det ≠ 0)
    (hH : H.IsHermitian) (hH0 : H.det ≠ 0) :
    (∃ P : Matrix n n ℂ, P.det ≠ 0 ∧ Pᵀ * G * P.map conj = H) ↔ posIndex G = posIndex H := by
  constructor
  · rintro ⟨P, hP, rfl⟩
    exact (posIndex_congr G hP).symm
  · intro h
    obtain ⟨Q, d, hQ, hd, hne⟩ := exists_congr_diagonal_real hH
    obtain ⟨P, hP, hPd⟩ := exists_congr_diagonal_of_card_eq hG hG0 (hne hH0) (by
      rw [h, posIndex_eq_card_of_congr_diagonal hQ hd]
      simp)
    have hu : IsUnit Q.det := hQ.isUnit
    refine ⟨P * Q⁻¹, ?_, ?_⟩
    · rw [det_mul]
      exact mul_ne_zero hP (isUnit_nonsing_inv_det Q hu).ne_zero
    · rw [congr_mul, hPd, ← hd, ← congr_mul, mul_nonsing_inv Q hu]
      simp

end Complex

section NormalForm

variable {r s : ℕ}

theorem sgn_pos_iff (p a : ℕ) : 0 < FD.sgn p a ↔ a < p := by
  unfold FD.sgn
  split_ifs with h <;> simp [h]

theorem sgn_ne_zero (p a : ℕ) : FD.sgn p a ≠ 0 := by
  unfold FD.sgn
  split_ifs <;> simp

theorem card_filter_sgn_pos {p : ℕ} (hp : p ≤ r) :
    (Finset.univ.filter fun a : Fin r => 0 < FD.sgn p a).card = p := by
  simp only [sgn_pos_iff]
  rw [Fin.card_filter_val_lt, min_eq_right hp]

theorem posIndex_diagonal_sgn {p : ℕ} (hp : p ≤ r) :
    posIndex (diagonal fun a : Fin r => ((FD.sgn p a : ℝ) : ℂ)) = p := by
  rw [posIndex_diagonal]
  simpa only [Complex.ofReal_re] using card_filter_sgn_pos hp

theorem posIndex_le (G : Matrix (Fin r) (Fin r) ℂ) : posIndex G ≤ r := by
  simpa using posIndex_le_card G

theorem posIndex_eq_of_congr_sgn {G P : Matrix (Fin r) (Fin r) ℂ} {p : ℕ} (hp : p ≤ r)
    (hP : P.det ≠ 0)
    (h : Pᵀ * G * P.map conj = diagonal fun a : Fin r => ((FD.sgn p a : ℝ) : ℂ)) :
    posIndex G = p := by
  rw [← posIndex_congr G hP, h, posIndex_diagonal_sgn hp]

theorem exists_congr_sgn {G : Matrix (Fin r) (Fin r) ℂ} (hG : G.IsHermitian) (hG0 : G.det ≠ 0) :
    ∃ P : Matrix (Fin r) (Fin r) ℂ, P.det ≠ 0 ∧
      Pᵀ * G * P.map conj = diagonal fun a : Fin r => ((FD.sgn (posIndex G) a : ℝ) : ℂ) :=
  exists_congr_diagonal_of_card_eq hG hG0 (fun _ => sgn_ne_zero _ _)
    (card_filter_sgn_pos (posIndex_le G))

theorem congr_sgn_iff {G : Matrix (Fin r) (Fin r) ℂ} (hG : G.IsHermitian) (hG0 : G.det ≠ 0)
    (p : ℕ) :
    (p ≤ r ∧ ∃ P : Matrix (Fin r) (Fin r) ℂ, P.det ≠ 0 ∧
      Pᵀ * G * P.map conj = diagonal fun a : Fin r => ((FD.sgn p a : ℝ) : ℂ)) ↔
      p = posIndex G := by
  constructor
  · rintro ⟨hp, P, hP, h⟩
    exact (posIndex_eq_of_congr_sgn hp hP h).symm
  · rintro rfl
    exact ⟨posIndex_le G, exists_congr_sgn hG hG0⟩

theorem existsUnique_congr_sgn {G : Matrix (Fin r) (Fin r) ℂ} (hG : G.IsHermitian)
    (hG0 : G.det ≠ 0) :
    ∃! p : ℕ, p ≤ r ∧ ∃ P : Matrix (Fin r) (Fin r) ℂ, P.det ≠ 0 ∧
      Pᵀ * G * P.map conj = diagonal fun a : Fin r => ((FD.sgn p a : ℝ) : ℂ) :=
  ⟨posIndex G, (congr_sgn_iff hG hG0 _).2 rfl, fun p hp => (congr_sgn_iff hG hG0 p).1 hp⟩

theorem posIndex_reindex_fromBlocks {G : Matrix (Fin r) (Fin r) ℂ} {H : Matrix (Fin s) (Fin s) ℂ}
    (hG : G.IsHermitian) (hH : H.IsHermitian) :
    posIndex (reindex finSumFinEquiv finSumFinEquiv (fromBlocks G 0 0 H)) =
      posIndex G + posIndex H := by
  rw [reindex_apply, posIndex_submatrix_equiv, posIndex_fromBlocks hG hH]

end NormalForm

section CM

open NumberField

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem embedding_cc (τ : E →+* ℂ) (x : E) : τ (FD.cc x) = conj (τ x) :=
  IsCMField.complexEmbedding_complexConj E τ x

theorem isHermitian_map {n : Type*} (τ : E →+* ℂ) {G : Matrix n n E}
    (hG : ∀ a b, FD.cc (G a b) = G b a) : (G.map τ).IsHermitian := by
  ext a b
  rw [conjTranspose_apply, map_apply, map_apply, ← hG b a, embedding_cc]
  rfl

omit [NumberField E] [IsCMField E] in
theorem det_map_ne_zero {n : Type*} [Fintype n] [DecidableEq n] (τ : E →+* ℂ) {G : Matrix n n E}
    (hG0 : G.det ≠ 0) : (G.map τ).det ≠ 0 := by
  have h : (G.map τ).det = τ G.det := (RingHom.map_det τ G).symm
  rw [h]
  exact (map_ne_zero τ).2 hG0

omit [NumberField E] [IsCMField E] in

theorem hermC_eq_dotProduct (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (u v : Fin r → ℂ) :
    FD.hermC τ G u v = u ⬝ᵥ G.map τ *ᵥ star v :=
  (HermDiag.dotProduct_mulVec_comp_eq_sum conj (G.map τ) u v).symm

omit [NumberField E] [IsCMField E] in

theorem gram_eq (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (P : Matrix (Fin r) (Fin r) ℂ) :
    FD.gram τ G P = Pᵀ * G.map τ * P.map conj := by
  ext a b
  rw [HermDiag.transpose_mul_mul_map_apply]
  exact hermC_eq_dotProduct τ G _ _

omit [NumberField E] [IsCMField E] in

theorem isGreatest_posIndex_map (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) :
    IsGreatest {d | ∃ W : Submodule ℂ (Fin r → ℂ), finrank ℂ W = d ∧
      ∀ x ∈ W, x ≠ 0 → 0 < (FD.hermC τ G x x).re} (posIndex (G.map τ)) := by
  simp only [hermC_eq_dotProduct]
  exact isGreatest_posIndex _

theorem gram_eq_sgn_iff (τ : E →+* ℂ) {G : Matrix (Fin r) (Fin r) E}
    (hG : ∀ a b, FD.cc (G a b) = G b a) (hG0 : G.det ≠ 0) (p : ℕ) :
    (p ≤ r ∧ ∃ P : Matrix (Fin r) (Fin r) ℂ, P.det ≠ 0 ∧
      FD.gram τ G P = diagonal fun a : Fin r => ((FD.sgn p a : ℝ) : ℂ)) ↔
      p = posIndex (G.map τ) := by
  simp only [gram_eq]
  exact congr_sgn_iff (isHermitian_map τ hG) (det_map_ne_zero τ hG0) p

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem posIndex_map_conjugate (τ : E →+* ℂ) {G : Matrix n n E}
    (hG : ∀ a b, FD.cc (G a b) = G b a) :
    posIndex (G.map (ComplexEmbedding.conjugate τ)) = posIndex (G.map τ) :=
  posIndex_map_conj (isHermitian_map τ hG)

theorem negIndex_map_conjugate (τ : E →+* ℂ) {G : Matrix n n E}
    (hG : ∀ a b, FD.cc (G a b) = G b a) :
    negIndex (G.map (ComplexEmbedding.conjugate τ)) = negIndex (G.map τ) :=
  negIndex_map_conj (isHermitian_map τ hG)

omit [DecidableEq n] in

theorem map_congr {m : Type*} (τ : E →+* ℂ) (G : Matrix n n E) (P : Matrix n m E) :
    (Pᵀ * G * P.map FD.cc).map τ = (P.map τ)ᵀ * G.map τ * (P.map τ).map conj := by
  have h : (P.map FD.cc).map τ = (P.map τ).map conj := by
    ext a b
    exact embedding_cc τ _
  rw [Matrix.map_mul, Matrix.map_mul, transpose_map, h]

theorem posIndex_map_congr (τ : E →+* ℂ) (G : Matrix n n E) {P : Matrix n n E} (hP : P.det ≠ 0) :
    posIndex ((Pᵀ * G * P.map FD.cc).map τ) = posIndex (G.map τ) := by
  rw [map_congr, posIndex_congr _ (det_map_ne_zero τ hP)]

theorem posIndex_map_eq_card_of_congr_diagonal (τ : E →+* ℂ) {G P : Matrix n n E} {d : n → E}
    (hP : P.det ≠ 0) (hd : Pᵀ * G * P.map FD.cc = diagonal d) :
    posIndex (G.map τ) = (Finset.univ.filter fun k => 0 < (τ (d k)).re).card := by
  rw [← posIndex_map_congr τ G hP, hd, diagonal_map (map_zero τ), posIndex_diagonal]

theorem posIndex_map_data (X : FD.Data E r) (τ : E →+* ℂ) : posIndex (X.Gm.map τ) = X.p0 := by
  have key : ∀ σ ∈ X.Ψ, posIndex (X.Gm.map σ) = X.p0 := fun σ hσ =>
    ((gram_eq_sgn_iff σ X.Gm_herm X.Gm_det X.p0).1 ⟨X.p0_le, X.signature ⟨σ, hσ⟩⟩).symm
  by_cases h : τ ∈ X.Ψ
  · exact key τ h
  · rw [← posIndex_map_conjugate τ X.Gm_herm]
    refine key _ ?_
    by_contra h'
    exact h ((X.cmType τ).2 h')

theorem negIndex_map_data (X : FD.Data E r) (τ : E →+* ℂ) :
    negIndex (X.Gm.map τ) = r - X.p0 := by
  rw [← posIndex_neg,
    posIndex_neg_eq_sub (isHermitian_map τ X.Gm_herm) (det_map_ne_zero τ X.Gm_det),
    posIndex_map_data, Fintype.card_fin]

end CM

open NumberField in

theorem law_of_inertia :
    (∀ (r : ℕ) (G : Matrix (Fin r) (Fin r) ℂ), G.IsHermitian → G.det ≠ 0 →
      (∃! p : ℕ, p ≤ r ∧ ∃ P : Matrix (Fin r) (Fin r) ℂ, P.det ≠ 0 ∧
        Pᵀ * G * P.map conj = diagonal fun a : Fin r => ((FD.sgn p a : ℝ) : ℂ)) ∧
      (∀ p : ℕ, (p ≤ r ∧ ∃ P : Matrix (Fin r) (Fin r) ℂ, P.det ≠ 0 ∧
        Pᵀ * G * P.map conj = diagonal fun a : Fin r => ((FD.sgn p a : ℝ) : ℂ)) ↔
          p = posIndex G) ∧
      (∀ (P : Matrix (Fin r) (Fin r) ℂ) (d : Fin r → ℂ), P.det ≠ 0 →
        Pᵀ * G * P.map conj = diagonal d →
          posIndex G = (Finset.univ.filter fun k => 0 < (d k).re).card) ∧
      IsGreatest {d | ∃ W : Submodule ℂ (Fin r → ℂ), finrank ℂ W = d ∧
        ∀ x ∈ W, x ≠ 0 → 0 < (x ⬝ᵥ G *ᵥ star x).re} (posIndex G) ∧
      (∀ (s : ℕ) (H : Matrix (Fin s) (Fin s) ℂ), H.IsHermitian →
        posIndex (fromBlocks G 0 0 H) = posIndex G + posIndex H ∧
        posIndex (reindex finSumFinEquiv finSumFinEquiv (fromBlocks G 0 0 H)) =
          posIndex G + posIndex H) ∧
      posIndex (-G) = r - posIndex G) ∧
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ),
      (∀ (G : Matrix (Fin r) (Fin r) E), (∀ a b, FD.cc (G a b) = G b a) → G.det ≠ 0 →
        ∀ τ : E →+* ℂ,
          (∀ p : ℕ, (p ≤ r ∧ ∃ P : Matrix (Fin r) (Fin r) ℂ, P.det ≠ 0 ∧
            FD.gram τ G P = diagonal fun a : Fin r => ((FD.sgn p a : ℝ) : ℂ)) ↔
              p = posIndex (G.map τ)) ∧
          posIndex (G.map (ComplexEmbedding.conjugate τ)) = posIndex (G.map τ)) ∧
      ∀ (X : FD.Data E r) (τ : E →+* ℂ), posIndex (X.Gm.map τ) = X.p0 :=
  ⟨fun _ G hG hG0 => ⟨existsUnique_congr_sgn hG hG0, congr_sgn_iff hG hG0,
      fun _ _ hP hd => posIndex_eq_card_of_congr_diagonal hP hd, isGreatest_posIndex G,
      fun _ _ hH => ⟨posIndex_fromBlocks hG hH, posIndex_reindex_fromBlocks hG hH⟩,
      by simpa only [Fintype.card_fin] using posIndex_neg_eq_sub hG hG0⟩,
    fun _ _ _ _ _ => ⟨fun _ hG hG0 τ => ⟨gram_eq_sgn_iff τ hG hG0, posIndex_map_conjugate τ hG⟩,
      posIndex_map_data⟩⟩

end GlobalTheory.Inertia
