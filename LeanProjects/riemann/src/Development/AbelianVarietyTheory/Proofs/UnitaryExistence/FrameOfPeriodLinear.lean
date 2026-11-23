import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HermFormConjDiag

open NumberField Matrix
open scoped nonZeroDivisors ComplexConjugate
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.FramePeriod

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

omit [NumberField E] [IsCMField E] in

lemma eq_of_hermC_eq (τ : E →+* ℂ) (Gm : Matrix (Fin r) (Fin r) E) (hG : Gm.det ≠ 0)
    (v w : Fin r → ℂ) (h : ∀ u, FD.hermC τ Gm v u = FD.hermC τ Gm w u) : v = w := by
  classical
  have hd : (τ.mapMatrix Gm).det ≠ 0 := by
    rw [← RingHom.map_det]; exact (map_ne_zero τ).2 hG
  rw [← sub_eq_zero]
  apply Matrix.eq_zero_of_vecMul_eq_zero hd
  rw [sub_vecMul, sub_eq_zero]
  funext b
  have := h (Pi.single b 1)
  simpa [FD.hermC, Pi.single_apply, apply_ite, vecMul, dotProduct] using this

lemma loc_compare (τ : E →+* ℂ) (Gm : Matrix (Fin r) (Fin r) E) (hG : Gm.det ≠ 0) (q : ℕ)
    (M M' K : Matrix (Fin r) (Fin r) ℂ) (hM : M.det ≠ 0) (hM' : M'.det ≠ 0)
    (hK : ∀ a c : Fin r, ¬ ((a : ℕ) < q ↔ (c : ℕ) < q) → K a c = 0)
    (h : ∀ u, locPer τ Gm q M' u = K *ᵥ locPer τ Gm q M u) :
    (∀ a c : Fin r, (a : ℕ) < q → K a c = (M⁻¹ * M') c a) ∧
      ∀ a c : Fin r, q ≤ (a : ℕ) → K a c = (M⁻¹ * M')⁻¹ a c := by
  classical
  have hMu : IsUnit M.det := isUnit_iff_ne_zero.2 hM
  constructor
  · intro a c ha
    have h1 : FD.col M' a = ∑ e, K a e • FD.col M e := by
      apply eq_of_hermC_eq τ Gm hG
      intro u
      have := congrFun (h u) a
      rw [locPer_apply, if_pos ha] at this
      rw [this, FD.hermC_sum_left, mulVec, dotProduct]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [FD.hermC_smul_left, locPer_apply]
      by_cases he : (e : ℕ) < q
      · rw [if_pos he]
      · rw [hK a e (by simp [ha, he])]; simp
    rw [← FD.Data.mulVec_eq_sum_col] at h1
    have h2 : M⁻¹ *ᵥ FD.col M' a = K a := by
      rw [h1, mulVec_mulVec, Matrix.nonsing_inv_mul _ hMu, one_mulVec]
    rw [← h2]
    rfl
  · intro a c ha
    have ha' : ¬ (a : ℕ) < q := not_lt.2 ha
    rw [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hMu]
    have h1 := congrFun (h (M *ᵥ Pi.single c 1)) a
    rw [locPer_apply, if_neg ha', mulVec_mulVec] at h1
    have h2 : (K *ᵥ locPer τ Gm q M (M *ᵥ Pi.single c 1)) a = (K *ᵥ Pi.single c 1) a := by
      rw [mulVec, mulVec, dotProduct, dotProduct]
      refine Finset.sum_congr rfl fun e _ => ?_
      by_cases he : (e : ℕ) < q
      · rw [hK a e (by simp [ha', he])]; simp
      · rw [locPer_apply, if_neg he, mulVec_mulVec, Matrix.nonsing_inv_mul _ hMu, one_mulVec]
    rw [h2] at h1
    simpa using h1.symm

lemma allPer_scale {Ψ : Finset (E →+* ℂ)} (Gm : Matrix (Fin r) (Fin r) E) (q : ℕ) (x : FD.Frame Ψ r)
    {g : ℕ} (idx : Fin g ≃ Ψ × Fin r) (c : Ψ → ℂ) (y : Ψ → Fin r → ℂ) (k : Fin g) :
    allPer Gm q x idx (fun τ => c τ • y τ) k =
      (if ((idx k).2 : ℕ) < q then conj (c (idx k).1) else c (idx k).1) * allPer Gm q x idx y k := by
  rw [allPer_apply, allPer_apply, locPer_apply, locPer_apply]
  split_ifs
  · rw [FD.hermC_smul_right]
  · rw [mulVec_smul]; rfl

lemma block_of_allPer {Ψ : Finset (E →+* ℂ)} (Gm : Matrix (Fin r) (Fin r) E) (q : ℕ)
    (x x' : FD.Frame Ψ r) {g : ℕ} (idx : Fin g ≃ Ψ × Fin r) (h : Matrix (Fin g) (Fin g) ℂ)
    (hs : Function.Surjective (allPer Gm q x idx))
    (hh : ∀ y, allPer Gm q x' idx y = h *ᵥ allPer Gm q x idx y) (k k' : Fin g)
    (hk : ¬ ((idx k).1 = (idx k').1 ∧ (((idx k).2 : ℕ) < q ↔ ((idx k').2 : ℕ) < q))) : h k k' = 0 := by
  classical
  have key : ∀ c : Ψ → ℂ, ((if ((idx k).2 : ℕ) < q then conj (c (idx k).1) else c (idx k).1) -
      (if ((idx k').2 : ℕ) < q then conj (c (idx k').1) else c (idx k').1)) * h k k' = 0 := by
    intro c
    obtain ⟨y, hy⟩ := hs (Pi.single k' 1)
    have h1 := congrFun (hh (fun τ => c τ • y τ)) k
    rw [allPer_scale, hh, hy] at h1
    have h2 : allPer Gm q x idx (fun τ => c τ • y τ) = Pi.single k'
        (if ((idx k').2 : ℕ) < q then conj (c (idx k').1) else c (idx k').1) := by
      funext l
      rw [allPer_scale, hy]
      by_cases hl : l = k'
      · subst hl; simp
      · simp [hl]
    rw [h2] at h1
    simp only [mulVec_single, Pi.smul_apply, col_apply, MulOpposite.smul_eq_mul_unop,
      MulOpposite.unop_op, mul_one] at h1
    linear_combination h1
  by_cases h1 : (idx k).1 = (idx k').1
  · have h2 := key (fun _ => Complex.I)
    have hI : (2 * Complex.I) ≠ 0 := by simp
    by_cases ha : ((idx k).2 : ℕ) < q <;> by_cases hb : ((idx k').2 : ℕ) < q
    · exact absurd ⟨h1, by simp [ha, hb]⟩ hk
    · rw [if_pos ha, if_neg hb, Complex.conj_I] at h2
      apply mul_left_cancel₀ hI
      linear_combination -h2
    · rw [if_neg ha, if_pos hb, Complex.conj_I] at h2
      apply mul_left_cancel₀ hI
      linear_combination h2
    · exact absurd ⟨h1, by simp [ha, hb]⟩ hk
  · have h2 := key (Pi.single (idx k).1 1)
    simpa [Ne.symm h1] using h2

theorem frame_of_period_linear : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (r : ℕ) (ξ : E) (Gm : Matrix (Fin r) (Fin r) E) (φ : D.La →ₗ[𝓞 E] (Fin r → E)) (Ψ : Finset (E →+* ℂ)) (hΨ : ∀ τ, τ ∈ Ψ ↔ τ (H.rt : E) = H.rt0) (g : ℕ) (idx : Fin g ≃ Ψ × Fin r) (ty : Fin g → (E →+* ℂ)) (hty : ∀ k, ty k = if ((idx k).2 : ℕ) < D.q then ComplexEmbedding.conjugate (idx k).1.1 else (idx k).1.1), FD.cc ξ = -ξ → (∀ τ ∈ Ψ, 0 < (τ ξ).im) → (Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧ (∀ a b, FD.cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, ((D.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * FD.herm Gm (φ x) (φ y))) → ∀ (P : D.La →+ (Fin g → ℂ)), ∀ x ∈ FD.GG Ψ Gm D.q, ∀ x' ∈ FD.GG Ψ Gm D.q, (∀ v k, P v k = if ((idx k).2 : ℕ) < D.q then FD.hermC (idx k).1.1 Gm (FD.col (FD.mat x (idx k).1) (idx k).2) (FD.Data.emb (idx k).1.1 (φ v)) else ((FD.mat x (idx k).1)⁻¹ *ᵥ FD.Data.emb (idx k).1.1 (φ v)) (idx k).2) → ∀ (P' : D.La →+ (Fin g → ℂ)), (∀ v k, P' v k = if ((idx k).2 : ℕ) < D.q then FD.hermC (idx k).1.1 Gm (FD.col (FD.mat x' (idx k).1) (idx k).2) (FD.Data.emb (idx k).1.1 (φ v)) else ((FD.mat x' (idx k).1)⁻¹ *ᵥ FD.Data.emb (idx k).1.1 (φ v)) (idx k).2) → ∀ h : Matrix (Fin g) (Fin g) ℂ, (∀ v, P' v = h *ᵥ P v) → ∃ b : FD.Frame Ψ r, x' = FD.rmul x b ∧ (∀ τ (a c : Fin r), (c : ℕ) < D.q → D.q ≤ (a : ℕ) → b τ a c = 0) ∧ (∀ k k', (idx k).1 = (idx k').1 → ((idx k).2 : ℕ) < D.q → ((idx k').2 : ℕ) < D.q → h k k' = b (idx k).1 (idx k').2 (idx k).2) ∧ (∀ k k', (idx k).1 = (idx k').1 → D.q ≤ ((idx k).2 : ℕ) → D.q ≤ ((idx k').2 : ℕ) → h k k' = (FD.mat b (idx k).1)⁻¹ (idx k).2 (idx k').2) ∧ ∀ k k', ty k ≠ ty k' → h k k' = 0 := by
  classical
  intro E _ _ _ H D r ξ Gm φ Ψ hΨ g idx ty hty hξ hpos ⟨hφ, hspan, hG, hdet, hEF⟩ P x hx x' hx' hP P' hP' h hh
  have hcm := cmType H Ψ hΨ
  have hloc := fun τ : Ψ => (exists_loc τ.1 Gm hG D.q (FD.mat x τ) (hx τ).1 (hx τ).2).1
  have hbij := allPer_bijective Gm D.q x idx hloc
  have hQ : ∀ v, P v = allPer Gm D.q x idx (CMLattice.embAll Ψ r (φ v)) := fun v =>
    funext fun k => hP v k
  have hQ' : ∀ v, P' v = allPer Gm D.q x' idx (CMLattice.embAll Ψ r (φ v)) := fun v =>
    funext fun k => hP' v k
  have := D.fin
  obtain ⟨b, hb⟩ := CMLattice.exists_basis_of_cmType Ψ hcm r (LinearMap.range φ)
    (Module.Finite.iff_fg.1 inferInstance) (by rw [LinearMap.coe_range]; exact hspan)
  have hall : ∀ y, allPer Gm D.q x' idx y = h *ᵥ allPer Gm D.q x idx y := by
    have : allPer Gm D.q x' idx = (h.mulVecLin.restrictScalars ℝ) ∘ₗ allPer Gm D.q x idx := by
      apply b.ext
      intro i
      obtain ⟨_, ⟨v, rfl⟩, hv⟩ := (hb (b i)).1 (Submodule.subset_span ⟨i, rfl⟩)
      rw [← hv, ← hQ', hh, hQ]
      rfl
    intro y
    rw [this]; rfl
  have hblock := block_of_allPer Gm D.q x x' idx h hbij.2 hall
  let K : Ψ → Matrix (Fin r) (Fin r) ℂ := fun τ =>
    Matrix.of fun a c => h (idx.symm (τ, a)) (idx.symm (τ, c))
  have hK0 : ∀ τ (a c : Fin r), ¬ ((a : ℕ) < D.q ↔ (c : ℕ) < D.q) → K τ a c = 0 := by
    intro τ a c hac
    apply hblock
    simpa using hac
  have hK : ∀ (τ : Ψ) u, locPer τ.1 Gm D.q (FD.mat x' τ) u =
      K τ *ᵥ locPer τ.1 Gm D.q (FD.mat x τ) u := by
    intro τ u
    funext a
    have h1 := congrFun (allPer_symm Gm D.q x' idx (fun _ => u) τ) a
    rw [← h1, hall, mulVec, mulVec, dotProduct, dotProduct, ← idx.symm.sum_comp, Fintype.sum_prod_type,
      Finset.sum_eq_single τ]
    · refine Finset.sum_congr rfl fun c _ => ?_
      rw [← allPer_symm Gm D.q x idx (fun _ => u) τ]
      rfl
    · intro σ _ hσ
      refine Finset.sum_eq_zero fun c _ => ?_
      rw [hblock, zero_mul]
      simp [hσ.symm]
    · simp
  have hc := fun τ : Ψ => loc_compare τ.1 Gm hdet D.q (FD.mat x τ) (FD.mat x' τ) (K τ) (hx τ).1 (hx' τ).1
    (hK0 τ) (hK τ)
  have hhK : ∀ k k', (idx k).1 = (idx k').1 → h k k' = K (idx k).1 (idx k).2 (idx k').2 := by
    intro k k' e
    simp only [K, of_apply]
    conv_rhs => rw [Prod.mk.eta, e, Prod.mk.eta]
    simp
  refine ⟨fun τ => ((FD.mat x τ)⁻¹ * FD.mat x' τ : Matrix (Fin r) (Fin r) ℂ), ?_, ?_, ?_, ?_, ?_⟩
  · funext τ
    exact (Matrix.mul_nonsing_inv_cancel_left (FD.mat x τ) (FD.mat x' τ)
      (isUnit_iff_ne_zero.2 (hx τ).1)).symm
  · intro τ a c hcq ha
    exact ((hc τ).1 c a hcq).symm.trans (hK0 τ c a (by simp [hcq, ha]))
  · intro k k' e h1 _
    rw [hhK k k' e]
    exact (hc _).1 _ _ h1
  · intro k k' e h1 _
    rw [hhK k k' e]
    exact (hc _).2 _ _ h1
  · intro k k' hne
    apply hblock
    rintro ⟨e1, e2⟩
    apply hne
    rw [hty, hty, e1]
    simp only [e2]

end

end GlobalTheory.FramePeriod
