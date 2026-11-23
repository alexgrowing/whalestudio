import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.BlockAnti
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicLeviEmbeddingHomomorphismProperties
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicStabilizerRadicalStructure

noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.Iwa

open Rad

section abstract
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] {ι : Type} [Fintype ι]
  [DecidableEq ι]

theorem exists_iso (p q : ι → E) (hp : Orthonormal ℂ p) (hq : Orthonormal ℂ q) :
    ∃ U : E ≃ₗᵢ[ℂ] E, ∀ a, U (p a) = q a := by
  have hle : Fintype.card ι ≤ Module.finrank ℂ E := hp.linearIndependent.fintype_card_le_finrank
  have hcard : Module.finrank ℂ E = Fintype.card (ι ⊕ Fin (Module.finrank ℂ E - Fintype.card ι)) := by
    simp; omega
  have hres : ∀ w : ι → E, Orthonormal ℂ w →
      Orthonormal ℂ ((Set.range (Sum.inl : _ → ι ⊕ Fin (Module.finrank ℂ E - Fintype.card ι))).restrict
        (Sum.elim w 0)) := by
    intro w hw
    rw [orthonormal_iff_ite] at hw ⊢
    rintro ⟨x, hx⟩ ⟨y, hy⟩
    obtain ⟨p, rfl⟩ := hx
    obtain ⟨q, rfl⟩ := hy
    change inner ℂ (w p) (w q) = _
    rw [hw p q]
    by_cases hpq : p = q
    · subst hpq; rw [if_pos rfl, if_pos rfl]
    · rw [if_neg hpq, if_neg]; intro h; exact hpq (Sum.inl_injective (congrArg Subtype.val h))
  obtain ⟨bP, hbP⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq hcard (hres _ hp)
  obtain ⟨bQ, hbQ⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq hcard (hres _ hq)
  have hP : ∀ a, bP (Sum.inl a) = p a := fun a => hbP _ ⟨a, rfl⟩
  have hQ : ∀ a, bQ (Sum.inl a) = q a := fun a => hbQ _ ⟨a, rfl⟩
  refine ⟨bP.repr.trans bQ.repr.symm, fun a => ?_⟩
  rw [← hP, ← hQ]; simp

theorem exists_half (H : E →ₗ[ℂ] E) (hH : ∀ x, H (H x) = x) (hadj : ∀ x y, inner ℂ (H x) y = inner ℂ x (H y))
    (c u : ι → E) (hc : Orthonormal ℂ c) (hu : Orthonormal ℂ u)
    (hci : ∀ a b, inner ℂ (c a) (H (c b)) = 0) (hui : ∀ a b, inner ℂ (u a) (H (u b)) = 0) :
    ∃ U : E →ₗ[ℂ] E, (∀ x, H (U x) = U x) ∧ (∀ x, U (H x) = U x) ∧
      (∀ x y, inner ℂ (U x) (U y) = inner ℂ (x + H x) (y + H y)) ∧ ∀ a, U (c a) = u a + H (u a) := by
  let S : Submodule ℂ E := LinearMap.ker (H - LinearMap.id)
  have hS : ∀ x, x ∈ S ↔ H x = x := fun x => by simp [S, sub_eq_zero]
  let P : E →ₗ[ℂ] S := (LinearMap.id + H).codRestrict S fun x => by
    rw [hS]; simp [hH, add_comm]
  have hP : ∀ x, (P x : E) = x + H x := fun x => rfl
  let s : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)⁻¹
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num
  have hs : s * s * 2 = 1 := by
    simp only [s]; rw [← mul_inv, h2]; norm_num
  have hs' : (starRingEnd ℂ) s = s := by simp [s]
  have hs0 : s ≠ 0 := fun h => by simp [h] at hs
  have hO : ∀ w : ι → E, Orthonormal ℂ w → (∀ a b, inner ℂ (w a) (H (w b)) = 0) →
      Orthonormal ℂ fun a => s • P (w a) := by
    intro w hw hwi
    rw [orthonormal_iff_ite] at hw ⊢
    intro a b
    rw [inner_smul_left, inner_smul_right, hs', Submodule.coe_inner, hP, hP]
    simp only [inner_add_left, inner_add_right, hadj, hH, hw, hwi]
    split_ifs
    · linear_combination hs
    · ring
  obtain ⟨U, hU⟩ := exists_iso _ _ (hO c hc hci) (hO u hu hui)
  refine ⟨S.subtype ∘ₗ U.toLinearEquiv.toLinearMap ∘ₗ P, fun x => (hS _).1 (U (P x)).2, fun x => ?_,
    fun x y => ?_, fun a => ?_⟩
  · have : P (H x) = P x := Subtype.ext (by rw [hP, hP, hH, add_comm])
    show ((U (P (H x)) : S) : E) = (U (P x) : S)
    rw [this]
  · show inner ℂ ((U (P x) : S) : E) ((U (P y) : S) : E) = _
    rw [← Submodule.coe_inner, U.inner_map_map, Submodule.coe_inner, hP, hP]
  · show ((U (P (c a)) : S) : E) = _
    have := hU a
    rw [map_smul] at this
    rw [smul_right_injective _ hs0 this, hP]

theorem exists_comm (H : E →ₗ[ℂ] E) (hH : ∀ x, H (H x) = x) (hadj : ∀ x y, inner ℂ (H x) y = inner ℂ x (H y))
    (c u : ι → E) (hc : Orthonormal ℂ c) (hu : Orthonormal ℂ u)
    (hci : ∀ a b, inner ℂ (c a) (H (c b)) = 0) (hui : ∀ a b, inner ℂ (u a) (H (u b)) = 0) :
    ∃ K : E →ₗ[ℂ] E, (∀ x, K (H x) = H (K x)) ∧ (∀ x y, inner ℂ (K x) (K y) = inner ℂ x y) ∧
      ∀ a, K (c a) = u a := by
  obtain ⟨U, h1, h2, h3, h4⟩ := exists_half H hH hadj c u hc hu hci hui
  obtain ⟨V, g1, g2, g3, g4⟩ := exists_half (-H) (by simp [hH]) (by simp [hadj]) c u hc hu (by simp [hci])
    (by simp [hui])
  simp only [LinearMap.neg_apply, map_neg, neg_eq_iff_eq_neg] at g1 g2 g3 g4
  have hUV : ∀ x y, inner ℂ (U x) (V y) = 0 := fun x y => by
    have : inner ℂ (U x) (V y) = -inner ℂ (U x) (V y) := by
      conv_lhs => rw [← h1, hadj, g1, inner_neg_right]
    linear_combination this / 2
  have hVU : ∀ x y, inner ℂ (V x) (U y) = 0 := fun x y => by
    rw [← inner_conj_symm, hUV, map_zero]
  refine ⟨(1 / 2 : ℂ) • (U + V), fun x => ?_, fun x y => ?_, fun a => ?_⟩
  · simp [h1, h2, g1, g2]
  · simp only [LinearMap.smul_apply, LinearMap.add_apply, inner_smul_left, inner_smul_right, inner_add_left,
      inner_add_right, hUV, hVU, h3, g3, inner_neg_left, inner_neg_right, hadj, hH, map_div₀, map_one, map_ofNat]
    ring
  · simp only [LinearMap.smul_apply, LinearMap.add_apply, h4, g4]
    module

end abstract

variable {k r : ℕ}

theorem UH_mul {n : ℕ} {H a b : Matrix (Fin n) (Fin n) ℂ} (ha : a ∈ UH H) (hb : b ∈ UH H) : a * b ∈ UH H := by
  have ha' : aᴴ * H * a = H := ha
  have hb' : bᴴ * H * b = H := hb
  show (a * b)ᴴ * H * (a * b) = H
  calc (a * b)ᴴ * H * (a * b) = bᴴ * (aᴴ * H * a) * b := by simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = H := by rw [ha', hb']

theorem UH_det {n : ℕ} {H a : Matrix (Fin n) (Fin n) ℂ} (hH : H * H = 1) (ha : a ∈ UH H) : IsUnit a.det := by
  have ha' : aᴴ * H * a = H := ha
  have h1 : (H * aᴴ * H) * a = 1 := by
    rw [← hH]; nth_rewrite 4 [← ha']; simp only [Matrix.mul_assoc]
  exact Matrix.isUnit_det_of_left_inverse h1

theorem UH_inv {n : ℕ} {H a : Matrix (Fin n) (Fin n) ℂ} (hH : H * H = 1) (ha : a ∈ UH H) : a⁻¹ ∈ UH H := by
  have ha' : aᴴ * H * a = H := ha
  have hu := UH_det hH ha
  show a⁻¹ᴴ * H * a⁻¹ = H
  calc a⁻¹ᴴ * H * a⁻¹ = a⁻¹ᴴ * (aᴴ * H * a) * a⁻¹ := by rw [ha']
    _ = (a * a⁻¹)ᴴ * H * (a * a⁻¹) := by simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = H := by rw [Matrix.mul_nonsing_inv _ hu]; simp

theorem Hb_sq : Hb k * Hb k = 1 := by
  unfold Hb; rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1; funext j; split_ifs <;> simp

theorem sg_sq (j : Fin (k + 1)) : sg k j * sg k j = 1 := by
  unfold sg; split_ifs <;> simp

theorem Hpk_sq : Hpk k r * Hpk k r = 1 := by
  ext x y
  rw [Matrix.mul_apply, sum3]
  induction x using cases3 <;> induction y using cases3 <;>
    simp [H_ee, H_ew, H_es, H_we, H_ww, H_ws, H_se, H_sw, H_ss, Matrix.one_apply,
      eI_inj, wI_inj, esI_inj, eI_ne_wI, eI_ne_esI, wI_ne_esI, wI_ne_eI, esI_ne_eI, esI_ne_wI]
  split_ifs with h
  · subst h; exact sg_sq _
  · rfl

theorem Hpk_herm : (Hpk k r)ᴴ = Hpk k r := by
  ext x y
  rw [conjTranspose_apply]
  induction x using cases3 <;> induction y using cases3 <;>
    simp [H_ee, H_ew, H_es, H_we, H_ww, H_ws, H_se, H_sw, H_ss, apply_ite (starRingEnd ℂ), eq_comm]
  split_ifs with h
  · subst h; exact (star_sg _).symm
  · rfl

theorem stab (p : Mat k r) (hp : p ∈ GG k r) (a : Fin r → ℝ) (ha : ∀ b, 0 < a b)
    (h1 : ∀ (b : Fin r) (i : Fin (2 * r + k + 1)), b.val ≤ i.val → p i (eI k r b) = if i = eI k r b then (a b : ℂ) else 0) :
    ∃ n ∈ Nset k r, ∃ m ∈ UH (Hb k), p = n * uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m := by
  have hp' : pᴴ * Hpk k r * p = Hpk k r := hp
  have ha0 : ∀ b, (a b : ℂ) ≠ 0 := fun b => by exact_mod_cast (ha b).ne'
  have hwe : ∀ j b, p (wI k r j) (eI k r b) = 0 := fun j b => by
    rw [h1 b _ (by have := b.2; simp only [wI]; omega), if_neg (wI_ne_eI _ _)]
  have hse : ∀ j b, p (esI k r j) (eI k r b) = 0 := fun j b => by
    rw [h1 b _ (by have := b.2; have := j.2; simp only [esI]; omega), if_neg (esI_ne_eI _ _)]
  have hsw : ∀ j b, p (esI k r b) (wI k r j) = 0 := by
    intro j b
    induction b using WellFoundedLT.induction with
    | ind b ih =>
      have := congrFun (congrFun hp' (eI k r b)) (wI k r j)
      simp only [Matrix.mul_apply, sum3, Matrix.conjTranspose_apply] at this
      simp [hwe, hse, H_ee, H_ew, H_es, H_we, H_ww, H_ws, H_se, H_sw, H_ss] at this
      rw [Finset.sum_eq_single b, h1 b _ le_rfl, if_pos rfl] at this
      · simpa [(ha b).ne'] using this
      · intro c _ hc
        rcases lt_or_gt_of_ne hc with h | h
        · rw [ih c h, mul_zero]
        · rw [h1 b _ h.le, if_neg (by rw [eI_inj]; exact hc)]; simp
      · simp
  let m : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ := Matrix.of fun i j => p (wI k r i) (wI k r j)
  have hm : m ∈ UH (Hb k) := by
    show mᴴ * Hb k * m = Hb k
    ext i j
    have := congrFun (congrFun hp' (wI k r i)) (wI k r j)
    simp only [Matrix.mul_apply, sum3, Matrix.conjTranspose_apply] at this
    simp [hsw, H_ee, H_ew, H_es, H_we, H_ww, H_ws, H_se, H_sw, H_ss] at this
    simpa [Matrix.mul_apply, Hb_apply, m] using this
  have hmu := UH_det Hb_sq hm
  have hd : IsUnit (Matrix.diagonal fun b => (a b : ℂ)⁻¹).det := by
    rw [det_diagonal, isUnit_iff_ne_zero, Finset.prod_ne_zero_iff]
    exact fun b _ => inv_ne_zero (ha0 b)
  have u_we : ∀ u j b, uEmb k r u (wI k r j) (eI k r b) = 0 := fun u j b => UEmb.u_me u b j
  have u_ew : ∀ u j b, uEmb k r u (eI k r b) (wI k r j) = 0 := fun u j b => UEmb.u_em u b j
  have u_sw : ∀ u j b, uEmb k r u (esI k r b) (wI k r j) = 0 := fun u j b => UEmb.u_sm u b j
  have u_ww : ∀ u i j, uEmb k r u (wI k r i) (wI k r j) = if i = j then 1 else 0 := fun u i j => UEmb.u_mm u i j
  refine ⟨p * mEmb k r m⁻¹ * uEmb k r (Matrix.diagonal fun b => (a b : ℂ)⁻¹),
    ⟨UH_mul (UH_mul hp (mEmb_mem _ (UH_inv Hb_sq hm))) (UEmb.uEmb_mem _ hd), fun b i hi => ?_,
      fun i j g1 g2 g3 => ?_⟩, m, hm, ?_⟩
  · simp only [Matrix.mul_apply, sum3]
    simp [u_we, UEmb.u_ee, UEmb.u_se, m_e, middleSpaceLeviEmbedding_apply_es_row, m_we, Matrix.diagonal_apply, eI_inj, esI_ne_eI]
    rw [h1 b i hi]
    split_ifs
    · exact mul_inv_cancel₀ (ha0 b)
    · simp
  · induction j using cases3 with
    | h1 a => exact absurd a.2 (by simp only [eI] at g1; omega)
    | h3 a => exact absurd a.2 (by simp only [esI] at g2; omega)
    | h2 j =>
      simp only [Matrix.mul_apply, sum3]
      simp [u_ew, u_sw, u_ww, m_e, middleSpaceLeviEmbedding_apply_es_row, m_ww, eI_ne_wI, esI_ne_wI]
      induction i using cases3 with
      | h1 a => exact absurd a.2 (by simp only [eI] at g3; omega)
      | h2 i =>
        have := congrFun (congrFun (Matrix.mul_nonsing_inv m hmu) i) j
        simpa [Matrix.mul_apply, Matrix.one_apply, wI_inj, m] using this
      | h3 b => simp [hsw, esI_ne_wI]
  · have : (Matrix.diagonal fun b => (a b : ℂ)⁻¹) * (Matrix.diagonal fun b => (a b : ℂ)) = 1 := by
      rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext b; exact inv_mul_cancel₀ (ha0 b)
    rw [Matrix.mul_assoc (p * _), ← UEmb.uEmb_mul, this, UEmb.uEmb_one, Matrix.mul_one, Matrix.mul_assoc,
      mEmb_mul, Matrix.nonsing_inv_mul _ hmu, mEmb_one, Matrix.mul_one]

theorem exists_K (c u : Fin r → EuclideanSpace ℂ (Fin (2 * r + k + 1))) (hc : Orthonormal ℂ c) (hu : Orthonormal ℂ u)
    (hci : ∀ a b, inner ℂ (c a) (Matrix.toEuclideanLin (Hpk k r) (c b)) = 0)
    (hui : ∀ a b, inner ℂ (u a) (Matrix.toEuclideanLin (Hpk k r) (u b)) = 0) :
    ∃ κ ∈ GG k r, κᴴ * κ = 1 ∧ ∀ a, κ *ᵥ (c a).ofLp = (u a).ofLp := by
  obtain ⟨K, hκH, hκi, hκc⟩ := exists_comm (Matrix.toEuclideanLin (Hpk k r))
    (fun x => by simp [Matrix.toEuclideanLin_apply, Hpk_sq])
    (Matrix.isHermitian_iff_isSymmetric.1 Hpk_herm) c u hc hu hci hui
  set κ : Mat k r := Matrix.toEuclideanLin.symm K with hκdef
  have hκ : ∀ v, WithLp.toLp 2 (κ *ᵥ v) = K (WithLp.toLp 2 v) := by
    intro v
    have h1 : Matrix.toEuclideanLin κ = K := LinearEquiv.apply_symm_apply _ _
    have := LinearMap.congr_fun h1 (WithLp.toLp 2 v)
    rw [Matrix.toEuclideanLin_apply, WithLp.ofLp_toLp] at this
    exact this
  have hunit : κᴴ * κ = 1 := by
    ext i j
    have h2 : inner ℂ (WithLp.toLp 2 (κ *ᵥ Pi.single i 1) : EuclideanSpace ℂ _) (WithLp.toLp 2 (κ *ᵥ Pi.single j 1)) =
        inner ℂ (WithLp.toLp 2 (Pi.single i 1) : EuclideanSpace ℂ _) (WithLp.toLp 2 (Pi.single j 1)) := by
      rw [hκ, hκ, hκi]
    simp only [EuclideanSpace.inner_eq_star_dotProduct, WithLp.ofLp_toLp, dotProduct] at h2
    simp only [mul_apply, conjTranspose_apply, one_apply]
    convert h2 using 1
    · refine Finset.sum_congr rfl fun m _ => ?_
      simp [mulVec_single, mul_comm]
    · simp [Pi.single_apply, eq_comm]
  have hv : ∀ v, κ *ᵥ (Hpk k r *ᵥ v) = Hpk k r *ᵥ (κ *ᵥ v) := by
    intro v
    have := hκH (WithLp.toLp 2 v)
    rw [Matrix.toEuclideanLin_apply, WithLp.ofLp_toLp, ← hκ, ← hκ, Matrix.toEuclideanLin_apply,
      WithLp.ofLp_toLp] at this
    simpa using congrArg WithLp.ofLp this
  have hcomm : κ * Hpk k r = Hpk k r * κ := by
    ext i j
    have := congrFun (hv (Pi.single j 1)) i
    rw [mulVec_mulVec, mulVec_mulVec] at this
    simpa [mulVec, dotProduct, Pi.single_apply] using this
  refine ⟨κ, ?_, hunit, fun a => ?_⟩
  · show κᴴ * Hpk k r * κ = Hpk k r
    rw [Matrix.mul_assoc, ← hcomm, ← Matrix.mul_assoc, hunit, Matrix.one_mul]
  · rw [← hκc, ← WithLp.toLp_ofLp 2 (c a), ← hκ]

open InnerProductSpace in

theorem iwasawa : ∀ (k r : ℕ), ∀ g ∈ GG k r, ∃ n ∈ Nset k r, ∃ a : Fin r → ℝ, (∀ b, 0 < a b) ∧ ∃ m ∈ UH (Hb k), ∃ κ ∈ (GG k r ∩ (Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ : Set (Mat k r))), g = n * uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m * κ := by
  intro k r g hg
  have hgu := UH_det Hpk_sq hg
  have hgi : g⁻¹ᴴ * Hpk k r * g⁻¹ = Hpk k r := UH_inv Hpk_sq hg
  let c : Fin r → EuclideanSpace ℂ (Fin (2 * r + k + 1)) := fun a => WithLp.toLp 2 (bvec (eI k r a))
  let w : Fin r → EuclideanSpace ℂ (Fin (2 * r + k + 1)) := fun a => WithLp.toLp 2 (g⁻¹ *ᵥ bvec (eI k r a))
  have hc : Orthonormal ℂ c := by
    rw [orthonormal_iff_ite]
    intro a b
    simp [c, EuclideanSpace.inner_eq_star_dotProduct, bvec, Pi.single_apply, eI_inj, eq_comm, Pi.star_single]
  have hgw : ∀ a, Matrix.toEuclideanLin g (w a) = c a := fun a => by
    simp [w, c, Matrix.toEuclideanLin_apply, Matrix.mul_nonsing_inv _ hgu]
  have hw : LinearIndependent ℂ w := LinearIndependent.of_comp (Matrix.toEuclideanLin g) (by
    have : (Matrix.toEuclideanLin g) ∘ w = c := funext hgw
    rw [this]; exact hc.linearIndependent)
  have hci : ∀ a b, inner ℂ (c a) (Matrix.toEuclideanLin (Hpk k r) (c b)) = 0 := fun a b => by
    simp [c, EuclideanSpace.inner_eq_star_dotProduct, bvec, Matrix.toEuclideanLin_apply, Pi.star_single, H_ee]
  have hwi : ∀ a b, inner ℂ (w a) (Matrix.toEuclideanLin (Hpk k r) (w b)) = 0 := fun a b => by
    rw [← hci a b]
    simp only [w, c, EuclideanSpace.inner_eq_star_dotProduct, Matrix.toEuclideanLin_apply, WithLp.ofLp_toLp]
    rw [dotProduct_comm, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, hgi, dotProduct_comm]
  have hspan : ∀ a, gramSchmidtNormed ℂ w a ∈ Submodule.span ℂ (Set.range w) := fun a => by
    rw [← span_gramSchmidt, ← span_gramSchmidtNormed_range]; exact Submodule.subset_span ⟨a, rfl⟩
  have hui : ∀ a b, inner ℂ (gramSchmidtNormed ℂ w a)
      (Matrix.toEuclideanLin (Hpk k r) (gramSchmidtNormed ℂ w b)) = 0 := by
    intro a b
    obtain ⟨ca, hca⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 (hspan a)
    obtain ⟨cb, hcb⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 (hspan b)
    rw [← hca, ← hcb, map_sum, sum_inner]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [inner_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [map_smul, inner_smul_left, inner_smul_right, hwi, mul_zero, mul_zero]
  obtain ⟨κ, hκ, hκu, hκc⟩ := exists_K c _ hc (gramSchmidtNormed_orthonormal hw) hci hui
  have hlow : ∀ (b : Fin r) (i : Fin (2 * r + k + 1)), b.val ≤ i.val →
      ∀ y ∈ Submodule.span ℂ (w '' Set.Iio b), (Matrix.toEuclideanLin g y) i = 0 := by
    intro b i hi y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      have ha' : a.val < b.val := ha
      rw [hgw]
      exact (bvec_apply _ _).trans (if_neg fun h => by rw [h] at hi; simp only [eI] at hi; omega)
    | zero => simp
    | add x y _ _ h1 h2 => rw [map_add, PiLp.add_apply, h1, h2, add_zero]
    | smul t x _ h1 => rw [map_smul, PiLp.smul_apply, h1, smul_zero]
  have hgs : ∀ b, w b - gramSchmidt ℂ w b ∈ Submodule.span ℂ (w '' Set.Iio b) := fun b => by
    rw [← span_gramSchmidt_Iio]
    nth_rewrite 1 [gramSchmidt_def'' ℂ w b]
    rw [add_sub_cancel_left]
    exact Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨i, Finset.mem_Iio.1 hi, rfl⟩)
  have hpos : ∀ b, 0 < ‖gramSchmidt ℂ w b‖⁻¹ := fun b => inv_pos.2 (norm_pos_iff.2 (gramSchmidt_ne_zero b hw))
  obtain ⟨n, hn, m, hm, h⟩ := stab (g * κ) (UH_mul hg hκ) (fun b => ‖gramSchmidt ℂ w b‖⁻¹) hpos (by
    intro b i hi
    have h1 := hlow b i hi _ (hgs b)
    rw [map_sub, hgw, PiLp.sub_apply, sub_eq_zero] at h1
    have h2 : (g * κ) i (eI k r b) = (Matrix.toEuclideanLin g (gramSchmidtNormed ℂ w b)) i := by
      rw [← mulVec_bvec (g * κ), ← mulVec_mulVec, Matrix.toEuclideanLin_apply, ← hκc]
    rw [h2, gramSchmidtNormed, map_smul, PiLp.smul_apply, ← h1]
    show _ • bvec (eI k r b) i = _
    rw [bvec_apply]
    split_ifs <;> simp)
  have hκu' : κ * κᴴ = 1 := mul_eq_one_comm.1 hκu
  refine ⟨n, hn, _, hpos, m, hm, κᴴ, ⟨?_, ?_⟩, ?_⟩
  · rw [← Matrix.inv_eq_left_inv hκu]; exact UH_inv Hpk_sq hκ
  · show κᴴ ∈ Matrix.unitaryGroup _ ℂ
    rw [Matrix.mem_unitaryGroup_iff, star_eq_conjTranspose, conjTranspose_conjTranspose]; exact hκu
  · rw [← h, Matrix.mul_assoc, hκu', Matrix.mul_one]

end GlobalTheory.Amp.Iwa
