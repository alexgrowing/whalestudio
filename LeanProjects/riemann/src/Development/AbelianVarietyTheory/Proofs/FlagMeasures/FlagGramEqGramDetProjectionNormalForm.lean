import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsNormalFormStabilizerMeasure
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalFormFlagZeroMiddleInverseMinorOrthogonalStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicLeviEmbeddingHomomorphismPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicStabilizerRadicalStructureStatement

noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.NormalGram

variable {k r : ℕ}

def mid (k r : ℕ) (v : Fin (2 * r + k + 1) → ℂ) : Fin (k + 1) → ℂ := fun j => v (wI k r j)

theorem idx_cases (i : Fin (2 * r + k + 1)) :
    (∃ a, i = eI k r a) ∨ (∃ j, i = wI k r j) ∨ ∃ a, i = esI k r a := by
  have hi := i.2
  by_cases h1 : i.val < r
  · exact Or.inl ⟨⟨i.val, h1⟩, rfl⟩
  by_cases h2 : i.val ≤ r + k
  · exact Or.inr (Or.inl ⟨⟨i.val - r, by omega⟩, Fin.ext (by simp only [wI]; omega)⟩)
  · exact Or.inr (Or.inr ⟨⟨2 * r + k - i.val, by omega⟩, Fin.ext (by simp only [esI]; omega)⟩)

theorem wI_inj : Function.Injective (wI k r) := by
  intro a b h
  have := congrArg Fin.val h
  simp only [wI] at this
  exact Fin.ext (by omega)

theorem sum_mid (f : Fin (2 * r + k + 1) → ℂ) (hf : inWb k r f) : ∑ i, f i = ∑ j, f (wI k r j) := by
  symm
  refine Finset.sum_of_injOn (wI k r) wI_inj.injOn (by simp) ?_ (by simp)
  intro i _ hi
  apply hf
  by_contra hc
  apply hi
  refine ⟨⟨i.val - r, by omega⟩, by simp, Fin.ext ?_⟩
  simp only [wI]; omega

theorem mulVec_of_row {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) (i i' : Fin n) (c : ℂ)
    (h : ∀ j, A i j = if j = i' then c else 0) : (A *ᵥ v) i = c * v i' := by
  simp [Matrix.mulVec, dotProduct, h]

theorem H_eI (v : Fin (2 * r + k + 1) → ℂ) (a : Fin r) : (Hpk k r *ᵥ v) (eI k r a) = v (esI k r a) := by
  rw [mulVec_of_row _ _ _ (esI k r a) 1, one_mul]
  intro j
  have := a.2; have := j.2
  simp only [Hpk, eI, esI, Fin.ext_iff]
  split_ifs <;> first | rfl | omega

theorem H_esI (v : Fin (2 * r + k + 1) → ℂ) (a : Fin r) : (Hpk k r *ᵥ v) (esI k r a) = v (eI k r a) := by
  rw [mulVec_of_row _ _ _ (eI k r a) 1, one_mul]
  intro j
  have := a.2; have := j.2
  simp only [Hpk, eI, esI, Fin.ext_iff]
  split_ifs <;> first | rfl | omega

theorem H_wI (v : Fin (2 * r + k + 1) → ℂ) (b : Fin (k + 1)) :
    (Hpk k r *ᵥ v) (wI k r b) = (if b = Fin.last k then -1 else 1) * v (wI k r b) := by
  rw [mulVec_of_row _ _ _ (wI k r b) _]
  intro j
  have := b.2; have := j.2
  have e : (wI k r b).val = r + b.val := rfl
  simp only [Hpk, Fin.ext_iff, Fin.val_last]
  split_ifs <;> first | rfl | omega

theorem herm_eI (v : Fin (2 * r + k + 1) → ℂ) (a : Fin r) :
    herm (Hpk k r) v (bvec (eI k r a)) = v (esI k r a) := by
  rw [← H_eI v a]
  simp [herm, bvec, dotProduct, Pi.single_apply]

theorem herm_mid (v z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) :
    herm (Hpk k r) v z = herm (Hb k) (mid k r v) (mid k r z) := by
  unfold herm dotProduct
  rw [sum_mid]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [H_wI]
    simp [Hb, mid, Matrix.mulVec_diagonal]
  · intro i hi
    simp [hz i hi]

theorem mid_uEmb (u : Matrix (Fin r) (Fin r) ℂ) (v : Fin (2 * r + k + 1) → ℂ) :
    mid k r (uEmb k r u *ᵥ v) = mid k r v := by
  funext b
  simp only [mid]
  rw [mulVec_of_row _ _ _ (wI k r b) 1, one_mul]
  intro j
  have := b.2; have := j.2
  simp only [uEmb, wI, Fin.ext_iff]
  split_ifs <;> first | rfl | omega

theorem mid_mEmb (m : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (v : Fin (2 * r + k + 1) → ℂ) :
    mid k r (mEmb k r m *ᵥ v) = m *ᵥ mid k r v := by
  funext b
  simp only [mid, Matrix.mulVec, dotProduct]
  have := b.2
  rw [sum_mid]
  · refine Finset.sum_congr rfl fun j _ => ?_
    have := j.2
    congr 1
    have e : (wI k r b).val = r + b.val := rfl
    have e' : (wI k r j).val = r + j.val := rfl
    unfold mEmb
    rw [dif_pos (by omega)]
    congr 1 <;> exact Fin.ext (by simp only []; omega)
  · intro i hi
    simp only [mEmb, wI, Fin.ext_iff]
    split_ifs <;> first | omega | simp

theorem top_mEmb (m : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (v : Fin (2 * r + k + 1) → ℂ) (a : Fin r) :
    (mEmb k r m *ᵥ v) (esI k r a) = v (esI k r a) := by
  rw [mulVec_of_row _ _ _ (esI k r a) 1, one_mul]
  intro j
  have := a.2; have := j.2
  simp only [mEmb, esI, Fin.ext_iff]
  split_ifs <;> first | rfl | omega

theorem top_pEl (B : Fin r → Fin (k + 1) → ℂ) (S : Matrix (Fin r) (Fin r) ℂ) (v : Fin (2 * r + k + 1) → ℂ) (a : Fin r) :
    (pEl k r B S *ᵥ v) (esI k r a) = v (esI k r a) := by
  rw [mulVec_of_row _ _ _ (esI k r a) 1, one_mul]
  intro j
  have := a.2; have := j.2
  have e : (esI k r a).val = 2 * r + k - a.val := rfl
  simp only [pEl, Fin.ext_iff]
  split_ifs <;> first | rfl | omega

theorem top_uEmb (u : Matrix (Fin r) (Fin r) ℂ) (v : Fin (2 * r + k + 1) → ℂ) (hv : ∀ a, v (esI k r a) = 0) (a : Fin r) :
    (uEmb k r u *ᵥ v) (esI k r a) = 0 := by
  simp only [Matrix.mulVec, dotProduct]
  refine Finset.sum_eq_zero fun i _ => ?_
  have := a.2
  rcases idx_cases i with ⟨b, rfl⟩ | ⟨b, rfl⟩ | ⟨b, rfl⟩
  · have := b.2
    simp only [uEmb, esI, eI, Fin.ext_iff]
    split_ifs <;> first | omega | simp
  · have := b.2
    simp only [uEmb, esI, wI, Fin.ext_iff]
    split_ifs <;> first | omega | simp
  · simp [hv]

theorem top_uEmb_iff (u : Matrix (Fin r) (Fin r) ℂ) (hu : IsUnit u.det) (v : Fin (2 * r + k + 1) → ℂ) :
    (∀ a, (uEmb k r u *ᵥ v) (esI k r a) = 0) ↔ ∀ a, v (esI k r a) = 0 := by
  refine ⟨fun h a => ?_, top_uEmb u v⟩
  have h1 := top_uEmb u⁻¹ _ h a
  obtain ⟨hm, h0, -⟩ := GlobalTheory.T.isotropicLeviEmbedding_homomorphism_properties k r
  rwa [Matrix.mulVec_mulVec, ← hm _ _ (Matrix.isUnit_nonsing_inv_det u hu) hu, Matrix.nonsing_inv_mul u hu, h0,
    Matrix.one_mulVec] at h1

theorem mid_pEl (B : Fin r → Fin (k + 1) → ℂ) (S : Matrix (Fin r) (Fin r) ℂ) (v : Fin (2 * r + k + 1) → ℂ)
    (hv : ∀ a, v (esI k r a) = 0) : mid k r (pEl k r B S *ᵥ v) = mid k r v := by
  funext b
  simp only [mid, Matrix.mulVec, dotProduct]
  have := b.2
  rw [Finset.sum_eq_single (wI k r b)]
  · simp [pEl]
  · intro i _ hi
    rcases idx_cases i with ⟨c, rfl⟩ | ⟨c, rfl⟩ | ⟨c, rfl⟩
    · have := c.2
      have e : (wI k r b).val = r + b.val := rfl
      have e' : (eI k r c).val = c.val := rfl
      simp only [pEl, Fin.ext_iff]
      split_ifs <;> first | omega | simp
    · have := c.2
      have e : (wI k r b).val = r + b.val := rfl
      have e' : (wI k r c).val = r + c.val := rfl
      simp only [pEl, Fin.ext_iff, ne_eq] at hi ⊢
      split_ifs <;> first | omega | simp
    · simp [hv]
  · simp

theorem mid_pEl_esI (B : Fin r → Fin (k + 1) → ℂ) (S : Matrix (Fin r) (Fin r) ℂ) (a : Fin r) :
    mid k r (pEl k r B S *ᵥ bvec (esI k r a)) = B a := by
  funext b
  have := a.2; have := b.2
  simp only [mid, bvec, Matrix.mulVec_single_one, Matrix.col_apply, pEl, wI, esI, Fin.ext_iff]
  rw [if_neg (by omega), dif_neg (by omega), dif_pos (by omega)]
  congr 1 <;> exact Fin.ext (by simp only []; omega)

theorem gramProj_mul {n j : ℕ} (P : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (C : Matrix (Fin j) (Fin j) ℂ)
    (w : Fin j → Fin n → ℂ) : gramProj P (fun a => ∑ b, C b a • w b) = ‖C.det‖ * gramProj P w := by
  unfold gramProj
  have h : (Matrix.gram ℂ fun a => P.starProjection (WithLp.toLp 2 (∑ b, C b a • w b))) =
      Cᴴ * (Matrix.gram ℂ fun a => P.starProjection (WithLp.toLp 2 (w a))) * C := by
    ext a a'
    simp only [Matrix.gram_apply, WithLp.toLp_sum, WithLp.toLp_smul, map_sum, map_smul, sum_inner, inner_sum,
      inner_smul_left, inner_smul_right, Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
    simp only [Complex.star_def]
    ring
  rw [h, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, norm_mul, norm_mul, norm_star,
    show ∀ x y : ℝ, x * y * x = x ^ 2 * y from fun x y => by ring, Real.sqrt_mul (sq_nonneg _),
    Real.sqrt_sq (norm_nonneg _)]

theorem inner_mid (v u : EuclideanSpace ℂ (Fin (2 * r + k + 1))) (hu : inWb k r u.ofLp) :
    ⟪v, u⟫_ℂ = ⟪(WithLp.toLp 2 (mid k r v.ofLp) : EuclideanSpace ℂ (Fin (k + 1))), WithLp.toLp 2 (mid k r u.ofLp)⟫_ℂ := by
  simp only [PiLp.inner_apply]
  rw [sum_mid]
  · rfl
  · intro i hi
    simp [hu i hi]

theorem exists_mid (p : Fin (k + 1) → ℂ) : ∃ u, inWb k r u ∧ mid k r u = p := by
  refine ⟨fun i => if h : r ≤ i.val ∧ i.val ≤ r + k then p ⟨i.val - r, by omega⟩ else 0, ?_, ?_⟩
  · intro i hi
    exact dif_neg (by omega)
  · funext b
    have := b.2
    have e : (wI k r b).val = r + b.val := rfl
    unfold mid
    simp only []
    rw [dif_pos (by omega)]
    congr 1
    exact Fin.ext (by simp only []; omega)

theorem gramProj_mid {j : ℕ} (P : Submodule ℂ (EuclideanSpace ℂ (Fin (2 * r + k + 1))))
    (P₀ : Submodule ℂ (EuclideanSpace ℂ (Fin (k + 1))))
    (hP : ∀ v, v ∈ P ↔ inWb k r v.ofLp ∧ WithLp.toLp 2 (mid k r v.ofLp) ∈ P₀) (v : Fin j → Fin (2 * r + k + 1) → ℂ) :
    gramProj P v = gramProj P₀ fun a => mid k r (v a) := by
  have key : ∀ y : EuclideanSpace ℂ (Fin (2 * r + k + 1)),
      P₀.starProjection (WithLp.toLp 2 (mid k r y.ofLp)) = WithLp.toLp 2 (mid k r (P.starProjection y).ofLp) := by
    intro y
    refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ((hP _).1 (P.starProjection_apply_mem y)).2 ?_
    intro w hw
    obtain ⟨u, hu, hu'⟩ := exists_mid (r := r) w.ofLp
    have hmem : WithLp.toLp 2 u ∈ P := (hP _).2 ⟨hu, by simpa [hu'] using hw⟩
    have h1 := P.starProjection_inner_eq_zero y _ hmem
    rw [inner_mid _ _ hu] at h1
    simp only [hu'] at h1
    exact h1
  unfold gramProj
  congr 3
  ext a b
  simp only [Matrix.gram_apply]
  rw [inner_mid _ _ ((hP _).1 (P.starProjection_apply_mem _)).1, ← key, ← key]

def P0 (k : ℕ) (m : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (ζ : Fin (k + 1) → ℂ) :
    Submodule ℂ (EuclideanSpace ℂ (Fin (k + 1))) :=
  (Submodule.span ℂ {WithLp.toLp 2 (Pi.single (Fin.last k) 1), WithLp.toLp 2 (mᴴ *ᵥ ((Hb k)ᴴ *ᵥ ζ))})ᗮ

theorem mem_lastZeroOrthImageSubspace_iff (m : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (ζ : Fin (k + 1) → ℂ) (p : Fin (k + 1) → ℂ) :
    WithLp.toLp 2 p ∈ P0 k m ζ ↔ p (Fin.last k) = 0 ∧ herm (Hb k) (m *ᵥ p) ζ = 0 := by
  have e1 : ⟪(WithLp.toLp 2 (Pi.single (Fin.last k) 1) : EuclideanSpace ℂ (Fin (k + 1))), WithLp.toLp 2 p⟫_ℂ =
      p (Fin.last k) := by
    simp [PiLp.inner_apply]
  have e2 : ⟪(WithLp.toLp 2 (mᴴ *ᵥ ((Hb k)ᴴ *ᵥ ζ)) : EuclideanSpace ℂ (Fin (k + 1))), WithLp.toLp 2 p⟫_ℂ =
      herm (Hb k) (m *ᵥ p) ζ := by
    rw [EuclideanSpace.inner_toLp_toLp, dotProduct_comm, herm, Matrix.star_mulVec, Matrix.star_mulVec,
      Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_conjTranspose, Matrix.dotProduct_mulVec,
      Matrix.dotProduct_mulVec]
  unfold P0
  rw [Submodule.span_insert, ← Submodule.inf_orthogonal, Submodule.mem_inf,
    Submodule.mem_orthogonal_singleton_iff_inner_right, Submodule.mem_orthogonal_singleton_iff_inner_right, e1, e2]

theorem finrank_lastZeroOrthImageSubspace_ge (m : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (ζ : Fin (k + 1) → ℂ) :
    k - 1 ≤ Module.finrank ℂ (P0 k m ζ) := by
  classical
  unfold P0
  set a : EuclideanSpace ℂ (Fin (k + 1)) := WithLp.toLp 2 (Pi.single (Fin.last k) 1)
  set b : EuclideanSpace ℂ (Fin (k + 1)) := WithLp.toLp 2 (mᴴ *ᵥ ((Hb k)ᴴ *ᵥ ζ))
  have h1 := Submodule.finrank_add_finrank_orthogonal (Submodule.span ℂ ({a, b} : Set _))
  have h2 : Module.finrank ℂ (Submodule.span ℂ ({a, b} : Set _)) ≤ 2 := by
    have := finrank_span_finset_le_card (R := ℂ) ({a, b} : Finset _)
    have e : ((({a, b} : Finset _)) : Set (EuclideanSpace ℂ (Fin (k + 1)))) = {a, b} := by simp
    rw [← e]
    exact this.trans Finset.card_le_two
  simp only [finrank_euclideanSpace, Fintype.card_fin] at h1
  omega

theorem mem_Ppos_iff (z z' : Fin (2 * r + k + 1) → ℂ) (hz' : inWb k r z') (g : Mat k r)
    (hH : ∀ w, w ∈ Hcom k r z z' g ⊔ Xsp k r ↔ ∀ a : Fin (r + 1), herm (Hpk k r) w (fvec k r z' a) = 0)
    (B : Fin r → Fin (k + 1) → ℂ) (S u t : Matrix (Fin r) (Fin r) ℂ) (hu : IsUnit u.det) (ht : IsUnit t.det)
    (m : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (v : EuclideanSpace ℂ (Fin (2 * r + k + 1))) :
    v ∈ Ppos k r z z' g (pEl k r B S * uEmb k r u * (uEmb k r t * mEmb k r m)) ↔
      inWb k r v.ofLp ∧ WithLp.toLp 2 (mid k r v.ofLp) ∈ P0 k m (mid k r z') := by
  set x := pEl k r B S * uEmb k r u * (uEmb k r t * mEmb k r m) with hx
  have hxv : x *ᵥ v.ofLp = pEl k r B S *ᵥ (uEmb k r u *ᵥ (uEmb k r t *ᵥ (mEmb k r m *ᵥ v.ofLp))) := by
    simp only [hx, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have htop : (∀ a, (x *ᵥ v.ofLp) (esI k r a) = 0) ↔ ∀ a, v.ofLp (esI k r a) = 0 := by
    simp only [hxv, top_pEl]
    rw [top_uEmb_iff u hu, top_uEmb_iff t ht]
    simp only [top_mEmb]
  have hmid : (∀ a, v.ofLp (esI k r a) = 0) → mid k r (x *ᵥ v.ofLp) = m *ᵥ mid k r v.ofLp := by
    intro h
    rw [hxv, mid_pEl, mid_uEmb, mid_uEmb, mid_mEmb]
    exact top_uEmb _ _ (top_uEmb _ _ (by simpa only [top_mEmb] using h))
  have hf : (∀ a : Fin (r + 1), herm (Hpk k r) (x *ᵥ v.ofLp) (fvec k r z' a) = 0) ↔
      (∀ a, (x *ᵥ v.ofLp) (esI k r a) = 0) ∧ herm (Hpk k r) (x *ᵥ v.ofLp) z' = 0 := by
    constructor
    · intro h
      refine ⟨fun a => ?_, ?_⟩
      · have := h a.castSucc
        rw [← herm_eI (x *ᵥ v.ofLp) a]
        simpa [fvec] using this
      · simpa [fvec] using h (Fin.last r)
    · rintro ⟨h1, h2⟩ a
      unfold fvec
      split_ifs
      · rw [herm_eI]; exact h1 _
      · exact h2
  have hm : v ∈ Ppos k r z z' g x ↔ Hpk k r *ᵥ v.ofLp = v.ofLp ∧ x *ᵥ v.ofLp ∈ Hcom k r z z' g ⊔ Xsp k r := by
    simp only [Ppos, Submodule.mem_comap, Submodule.mem_inf, LinearMap.mem_ker, Matrix.toLin'_apply,
      Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero]
    rfl
  rw [hm, hH, hf, htop, mem_lastZeroOrthImageSubspace_iff, herm_mid _ _ hz']
  constructor
  · rintro ⟨h1, h2, h3⟩
    rw [hmid h2] at h3
    refine ⟨?_, ?_, h3⟩
    · intro i hi
      rcases idx_cases i with ⟨a, rfl⟩ | ⟨b, rfl⟩ | ⟨a, rfl⟩
      · rw [← h1, H_eI]; exact h2 a
      · have := b.2
        have e : (wI k r b).val = r + b.val := rfl
        omega
      · exact h2 a
    · have := congrFun h1 (wI k r (Fin.last k))
      rw [H_wI, if_pos rfl] at this
      show v.ofLp (wI k r (Fin.last k)) = 0
      linear_combination (-1 / 2 : ℂ) * this
  · rintro ⟨h1, h2, h3⟩
    have he : ∀ a, v.ofLp (eI k r a) = 0 := fun a => h1 _ (Or.inl a.2)
    have hs : ∀ a, v.ofLp (esI k r a) = 0 := fun a => h1 _ (Or.inr (by have := a.2; simp only [esI]; omega))
    refine ⟨?_, hs, by rw [hmid hs]; exact h3⟩
    funext i
    rcases idx_cases i with ⟨a, rfl⟩ | ⟨b, rfl⟩ | ⟨a, rfl⟩
    · rw [H_eI, he, hs]
    · rw [H_wI]
      split_ifs with hb
      · have : v.ofLp (wI k r b) = 0 := by rw [hb]; exact h2
        rw [this, mul_zero]
      · rw [one_mul]
    · rw [H_esI, he, hs]

theorem eq_sum_of_mem_XstJ {j : ℕ} (hj : j ≤ r) (y : Fin (2 * r + k + 1) → ℂ) (hy : y ∈ XstJ k r j) :
    y = ∑ b : Fin j, y (esI k r (Fin.castLE hj b)) • bvec (esI k r (Fin.castLE hj b)) := by
  unfold XstJ at hy
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨⟨a, ha⟩, rfl⟩ := hy
    rw [Finset.sum_eq_single (⟨a.val, ha⟩ : Fin j)]
    · have : Fin.castLE hj ⟨a.val, ha⟩ = a := rfl
      simp [this, bvec]
    · intro b _ hb
      have : esI k r (Fin.castLE hj b) ≠ esI k r a := by
        intro h
        have h1 := congrArg Fin.val h
        have := b.2
        simp only [esI, Fin.val_castLE] at h1
        exact hb (Fin.ext (by simp only []; omega))
      simp [bvec, Pi.single_eq_of_ne this]
    · simp
  | zero => simp
  | add y y' _ _ h h' =>
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
    rw [← h, ← h']
  | smul c y _ h =>
    simp only [Pi.smul_apply, smul_eq_mul, mul_smul, ← Finset.smul_sum]
    rw [← h]

theorem mid_sum {j : ℕ} (c : Fin j → ℂ) (v : Fin j → Fin (2 * r + k + 1) → ℂ) :
    mid k r (∑ b, c b • v b) = ∑ b, c b • mid k r (v b) := by
  funext i
  simp [mid, Finset.sum_apply]

theorem Dj_eq {j : ℕ} (hj : j ≤ r) (z z' : Fin (2 * r + k + 1) → ℂ) (g : Mat k r) :
    Dj k r hj z z' g = ‖(Matrix.of fun b a : Fin j =>
      (g *ᵥ bvec (eI k r (Fin.castLE hj a))) (esI k r (Fin.castLE hj b))).det‖ := by
  unfold Dj Dmin
  congr 2
  ext b a
  have ha : a.val < r := lt_of_lt_of_le a.2 hj
  have hb : b.val < r := lt_of_lt_of_le b.2 hj
  simp only [Matrix.submatrix_apply, Zhat, fvec, Fin.val_castLE, Matrix.of_apply]
  rw [dif_pos ha, dif_pos hb, herm_eI]
  rfl

theorem Yj_eq_gramProj : ∀ (k r j : ℕ) (hj : j ≤ r) (z z' : (Fin (2 * r + k + 1) → ℂ)), ∀ (g₀ : Mat k r) (β : Fin r → ℕ) (c : ℂ), inWb k r z → inWb k r z' → 0 < Tz k r z → IsNormal0 k r hj β c z z' g₀ → ∀ m ∈ UH (Hb k), ∃ P₀ : Submodule ℂ (EuclideanSpace ℂ (Fin (k + 1))), k - 1 ≤ Module.finrank ℂ P₀ ∧ ∀ (q : PSec k r j × (UToff β → ℂ)) (a : Fin r → ℝ), (∀ b, 0 < a b) → Yj k r hj z z' g₀ (sEl k r j β q * (uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m)) = gramProj P₀ fun b : Fin j => m⁻¹ *ᵥ q.1.1 ⟨Fin.castLE hj b, b.2⟩ := by
  intro k r j hj z z' g β c hz hz' hT hN m hm
  obtain ⟨-, -, -, hD, hD', -, hH⟩ := GlobalTheory.T.normalFormFlagZero_middle_inverse_minor_orthogonal k r j hj z z' g β c hz hz' hT hN
  obtain ⟨-, -, hU, hup⟩ := GlobalTheory.T.isotropicLeviEmbedding_homomorphism_properties k r
  obtain ⟨hp, hsk, -, -, hM⟩ := GlobalTheory.T.isotropicStabilizerRadical_structure k r
  refine ⟨P0 k m (mid k r z'), finrank_lastZeroOrthImageSubspace_ge _ _, fun q a ha => ?_⟩
  have hu : IsUnit (upperOff β q.2).det := by
    unfold upperOff
    rw [(hup _).1]; exact isUnit_one
  have ht : IsUnit (Matrix.diagonal fun b => (a b : ℂ)).det := by
    rw [Matrix.det_diagonal, isUnit_iff_ne_zero]
    exact Finset.prod_ne_zero_iff.2 fun b _ => by exact_mod_cast (ha b).ne'
  unfold Yj sEl pSec pOf
  rw [gramProj_mid _ _ (mem_Ppos_iff z z' hz' g hH _ _ _ _ hu ht m), div_eq_iff hD.ne', ← hD', Dj_eq, mul_comm (gramProj _ _)]
  set C : Matrix (Fin j) (Fin j) ℂ := Matrix.of fun b a : Fin j =>
      (g⁻¹ *ᵥ bvec (eI k r (Fin.castLE hj a))) (esI k r (Fin.castLE hj b)) with hC
  have hn : ‖C.det‖ = ‖(-C).det‖ := by
    rw [Matrix.det_neg, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  rw [hn, ← gramProj_mul]
  congr 1
  funext b
  rw [eq_sum_of_mem_XstJ hj _ (hN.2.2.2.2.2.1 (Fin.castLE hj b) b.2).1, Matrix.mulVec_sum]
  simp only [Matrix.mulVec_smul]
  rw [mid_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.mul_inv_rev, (hM m hm).2, (hU _ hu).2.1, (hU _ ht).2.1,
    ((hp _ _).2.2.2 (hsk _ _)).2]
  simp only [← Matrix.mulVec_mulVec]
  rw [mid_mEmb, mid_uEmb, mid_uEmb, mid_pEl_esI]
  simp only [Pi.neg_apply, Matrix.neg_apply, hC, Matrix.of_apply, Matrix.mulVec_neg, smul_neg, neg_smul]
  rw [dif_pos (show (Fin.castLE hj d).val < j from d.2)]

end GlobalTheory.Amp.NormalGram
