import Mathlib
open scoped Matrix

namespace GlobalTheory

theorem exists_det_add_mul_ne_zero_of_ker_inf {k : Type} [Field k] {n : ℕ}
    (A C : Matrix (Fin n) (Fin n) k)
    (h : ∀ v : Fin n → k, A *ᵥ v = 0 → C *ᵥ v = 0 → v = 0) :
    ∃ X : Matrix (Fin n) (Fin n) k, (A + X * C).det ≠ 0 := by
  classical
  set a := Matrix.toLin' A with ha
  set c := Matrix.toLin' C with hc
  obtain ⟨L', hL'⟩ := Submodule.exists_isCompl (LinearMap.ker c)
  obtain ⟨U, hU⟩ := Submodule.exists_isCompl ((LinearMap.ker c).map a)

  have hkey : ∀ x ∈ LinearMap.ker c, a x = 0 → x = 0 := by
    intro x hx hax
    rw [LinearMap.mem_ker] at hx
    exact h x (by simpa [ha] using hax) (by simpa [hc] using hx)
  have hinj : Function.Injective (a.domRestrict (LinearMap.ker c)) := by
    intro x y hxy
    have hxy' : a ((x : Fin n → k) - y) = 0 := by
      rw [map_sub]; exact sub_eq_zero.mpr (by simpa using hxy)
    have := hkey _ (Submodule.sub_mem _ x.2 y.2) hxy'
    exact Subtype.ext (sub_eq_zero.mp this)
  have hrank : Module.finrank k L' = Module.finrank k U := by
    have h1 := Submodule.finrank_add_eq_of_isCompl hL'
    have h2 := Submodule.finrank_add_eq_of_isCompl hU
    have h3 : Module.finrank k ((LinearMap.ker c).map a) = Module.finrank k (LinearMap.ker c) := by
      rw [← LinearMap.range_domRestrict, LinearMap.finrank_range_of_inj hinj]
    omega
  let e : L' ≃ₗ[k] U := LinearEquiv.ofFinrankEq L' U hrank
  let g : (Fin n → k) →ₗ[k] (Fin n → k) :=
    LinearMap.ofIsCompl hL' (a.domRestrict (LinearMap.ker c)) (U.subtype ∘ₗ e.toLinearMap)
  have hgL : ∀ x (hx : x ∈ LinearMap.ker c), g x = a x := fun x hx =>
    LinearMap.ofIsCompl_apply_left hL' ⟨x, hx⟩
  have hgL' : ∀ y (hy : y ∈ L'), g y = (e ⟨y, hy⟩ : Fin n → k) := fun y hy =>
    LinearMap.ofIsCompl_apply_right hL' ⟨y, hy⟩

  have hg_inj : ∀ v, g v = 0 → v = 0 := by
    intro v hv
    have hvmem : v ∈ LinearMap.ker c ⊔ L' := by rw [hL'.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hvmem
    rw [map_add, hgL x hx, hgL' y hy] at hv
    have hax : a x ∈ (LinearMap.ker c).map a ⊓ U := by
      refine ⟨Submodule.mem_map_of_mem hx, ?_⟩
      rw [eq_neg_of_add_eq_zero_left hv]
      exact U.neg_mem (e ⟨y, hy⟩).2
    rw [hU.inf_eq_bot, Submodule.mem_bot] at hax
    have hx0 := hkey x hx hax
    rw [hax, zero_add] at hv
    have hy0 : e ⟨y, hy⟩ = 0 := Subtype.ext hv
    rw [LinearEquiv.map_eq_zero_iff] at hy0
    rw [hx0, zero_add]
    exact congrArg Subtype.val hy0

  have hle : LinearMap.ker c ≤ LinearMap.ker (g - a) := fun x hx => by
    rw [LinearMap.mem_ker, LinearMap.sub_apply, hgL x hx, sub_self]
  let f0 : LinearMap.range c →ₗ[k] (Fin n → k) :=
    ((LinearMap.ker c).liftQ (g - a) hle) ∘ₗ (c.quotKerEquivRange.symm.toLinearMap)
  obtain ⟨Y, hY⟩ := LinearMap.exists_extend f0
  have hfac : ∀ v, Y (c v) = g v - a v := by
    intro v
    have h0 := LinearMap.congr_fun hY ⟨c v, LinearMap.mem_range_self c v⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at h0
    rw [h0]
    simp only [f0, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      LinearMap.quotKerEquivRange_symm_apply_image]
    rw [Submodule.mkQ_apply, Submodule.liftQ_apply, LinearMap.sub_apply]
  refine ⟨LinearMap.toMatrix' Y, fun hdet => ?_⟩
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  apply hv0
  apply hg_inj
  have hmv : (A + LinearMap.toMatrix' Y * C) *ᵥ v = g v := by
    rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, LinearMap.toMatrix'_mulVec]
    have hcv : C *ᵥ v = c v := by rw [hc, Matrix.toLin'_apply]
    have hav : A *ᵥ v = a v := by rw [ha, Matrix.toLin'_apply]
    rw [hcv, hfac, hav]
    abel
  rw [← hmv, hv]

theorem exists_isUnit_det_toBlocks_add_mul {R : Type} [CommRing R] [IsLocalRing R] {n : ℕ}
    (H : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) (hH : IsUnit H.det) :
    ∃ X : Matrix (Fin n) (Fin n) R, IsUnit (H.toBlocks₁₁ + X * H.toBlocks₂₁).det := by
  classical
  set Hb := H.map (IsLocalRing.residue R) with hHb_def
  have hHb : Hb.det ≠ 0 := by
    rw [hHb_def, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (hH.map (IsLocalRing.residue R)).ne_zero
  obtain ⟨Xb, hXb⟩ := exists_det_add_mul_ne_zero_of_ker_inf Hb.toBlocks₁₁ Hb.toBlocks₂₁ (by
    intro v h1 h2
    by_contra hv
    apply hHb
    refine Matrix.exists_mulVec_eq_zero_iff.mp ⟨Sum.elim v 0, ?_, ?_⟩
    · intro h0
      apply hv
      funext i
      simpa using congrFun h0 (Sum.inl i)
    · funext i
      cases i with
      | inl i =>
        simpa [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.toBlocks₁₁] using congrFun h1 i
      | inr i =>
        simpa [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.toBlocks₂₁] using congrFun h2 i)
  choose X hX using fun i j => IsLocalRing.residue_surjective (R := R) (Xb i j)
  refine ⟨Matrix.of X, ?_⟩
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det]
  have hm : (IsLocalRing.residue R).mapMatrix (H.toBlocks₁₁ + Matrix.of X * H.toBlocks₂₁) =
      Hb.toBlocks₁₁ + Xb * Hb.toBlocks₂₁ := by
    ext i j
    simp [RingHom.mapMatrix_apply, Matrix.mul_apply, map_sum, hX, hHb_def, Matrix.toBlocks₁₁,
      Matrix.toBlocks₂₁]
  rw [hm]
  exact hXb

theorem isUnit_det_of_dual_blocks {R : Type} [CommRing R] {n : ℕ}
    (S A B C D A' C' : Matrix (Fin n) (Fin n) R) (hA : IsUnit A.det)
    (h1 : Aᵀ * (S * C') + Cᵀ * (S * A') = 0)
    (h2 : IsUnit (Bᵀ * (S * C') + Dᵀ * (S * A')).det) : IsUnit A'.det := by
  have hAt : IsUnit Aᵀ.det := by rwa [Matrix.det_transpose]
  have hSC : S * C' = -(Aᵀ⁻¹ * (Cᵀ * (S * A'))) := by
    have h1' : Aᵀ * (S * C') = -(Cᵀ * (S * A')) := eq_neg_of_add_eq_zero_left h1
    calc S * C' = Aᵀ⁻¹ * (Aᵀ * (S * C')) := by
          rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hAt, Matrix.one_mul]
      _ = -(Aᵀ⁻¹ * (Cᵀ * (S * A'))) := by rw [h1', Matrix.mul_neg]
  have key : Bᵀ * (S * C') + Dᵀ * (S * A') = (Dᵀ - Bᵀ * Aᵀ⁻¹ * Cᵀ) * (S * A') := by
    rw [hSC]
    generalize Aᵀ⁻¹ = M
    noncomm_ring
  rw [key, Matrix.det_mul, Matrix.det_mul] at h2
  exact isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_right h2)

private lemma blocks_conj_eq_fromBlocks_sums {R : Type} [CommRing R] {n : ℕ}
    (G : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) :
    Matrix.fromBlocks 1 1 1 (-1) * G * Matrix.fromBlocks 1 1 1 (-1) =
      Matrix.fromBlocks (G.toBlocks₁₁ + G.toBlocks₁₂ + G.toBlocks₂₁ + G.toBlocks₂₂)
        (G.toBlocks₁₁ - G.toBlocks₁₂ + G.toBlocks₂₁ - G.toBlocks₂₂)
        (G.toBlocks₁₁ + G.toBlocks₁₂ - G.toBlocks₂₁ - G.toBlocks₂₂)
        (G.toBlocks₁₁ - G.toBlocks₁₂ - G.toBlocks₂₁ + G.toBlocks₂₂) := by
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks G]
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  congr 1 <;> noncomm_ring

private lemma H_affine_combination_eq_of_quadratic_relation {R : Type} [CommRing R] {n : ℕ}
    (S a11 a12 a21 a22 b11 b12 b21 b22 X₁ X₂ : Matrix (Fin n) (Fin n) R)
    (E11 : a11ᵀ * S * b11 - a21ᵀ * S * b21 = S) (E12 : a11ᵀ * S * b12 - a21ᵀ * S * b22 = 0)
    (E21 : a12ᵀ * S * b11 - a22ᵀ * S * b21 = 0) (E22 : a12ᵀ * S * b12 - a22ᵀ * S * b22 = -S)
    (hX : X₁ᵀ * S + S * X₂ = 0) :
    (a11 + a12 + a21 + a22 + X₁ * (a11 + a12 - a21 - a22))ᵀ * (S * (b11 + b12 - b21 - b22)) +
        (a11 + a12 - a21 - a22)ᵀ *
          (S * (b11 + b12 + b21 + b22 + X₂ * (b11 + b12 - b21 - b22))) = 0 ∧
      (a11 - a12 + a21 - a22 + X₁ * (a11 - a12 - a21 + a22))ᵀ * (S * (b11 + b12 - b21 - b22)) +
        (a11 - a12 - a21 + a22)ᵀ *
          (S * (b11 + b12 + b21 + b22 + X₂ * (b11 + b12 - b21 - b22))) = S + S + S + S := by
  simp only [Matrix.transpose_add, Matrix.transpose_sub, Matrix.transpose_mul]
  constructor
  · calc _ = ((a11ᵀ * S * b11 - a21ᵀ * S * b21 - S) + (a11ᵀ * S * b12 - a21ᵀ * S * b22) +
            (a12ᵀ * S * b11 - a22ᵀ * S * b21) + (a12ᵀ * S * b12 - a22ᵀ * S * b22 + S)) +
          ((a11ᵀ * S * b11 - a21ᵀ * S * b21 - S) + (a11ᵀ * S * b12 - a21ᵀ * S * b22) +
            (a12ᵀ * S * b11 - a22ᵀ * S * b21) + (a12ᵀ * S * b12 - a22ᵀ * S * b22 + S)) +
          (a11ᵀ + a12ᵀ - a21ᵀ - a22ᵀ) * (X₁ᵀ * S + S * X₂) * (b11 + b12 - b21 - b22) := by
          noncomm_ring
      _ = 0 := by rw [E11, E12, E21, E22, hX]; noncomm_ring
  · calc _ = ((a11ᵀ * S * b11 - a21ᵀ * S * b21 - S) + (a11ᵀ * S * b12 - a21ᵀ * S * b22) -
            (a12ᵀ * S * b11 - a22ᵀ * S * b21) - (a12ᵀ * S * b12 - a22ᵀ * S * b22 + S)) +
          ((a11ᵀ * S * b11 - a21ᵀ * S * b21 - S) + (a11ᵀ * S * b12 - a21ᵀ * S * b22) -
            (a12ᵀ * S * b11 - a22ᵀ * S * b21) - (a12ᵀ * S * b12 - a22ᵀ * S * b22 + S)) +
          (a11ᵀ - a12ᵀ - a21ᵀ + a22ᵀ) * (X₁ᵀ * S + S * X₂) * (b11 + b12 - b21 - b22) +
          (S + S + S + S) := by
          noncomm_ring
      _ = S + S + S + S := by rw [E11, E12, E21, E22, hX]; noncomm_ring

theorem exists_dual_pair_isUnit_det_blocks :
    ∀ {R : Type} [CommRing R] [IsLocalRing R], IsUnit (2 : R) → ∀ {n : ℕ} (S : Matrix (Fin n) (Fin n) R), IsUnit S.det →
    ∀ (G₁ G₂ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R), IsUnit G₁.det →
      G₁ᵀ * Matrix.fromBlocks S 0 0 (-S) * G₂ = Matrix.fromBlocks S 0 0 (-S) →
      ∃ X₁ X₂ : Matrix (Fin n) (Fin n) R, X₁ᵀ * S + S * X₂ = 0 ∧
        IsUnit (G₁.toBlocks₁₁ + G₁.toBlocks₁₂ + G₁.toBlocks₂₁ + G₁.toBlocks₂₂ +
          X₁ * (G₁.toBlocks₁₁ + G₁.toBlocks₁₂ - G₁.toBlocks₂₁ - G₁.toBlocks₂₂)).det ∧
        IsUnit (G₂.toBlocks₁₁ + G₂.toBlocks₁₂ + G₂.toBlocks₂₁ + G₂.toBlocks₂₂ +
          X₂ * (G₂.toBlocks₁₁ + G₂.toBlocks₁₂ - G₂.toBlocks₂₁ - G₂.toBlocks₂₂)).det := by
  intro R _ _ h2 n S hS G₁ G₂ hG₁ hG
  classical
  have hKdet : IsUnit (Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) R) (1 : Matrix (Fin n) (Fin n) R)
      (1 : Matrix (Fin n) (Fin n) R) (-1 : Matrix (Fin n) (Fin n) R)).det := by
    rw [Matrix.det_fromBlocks_one₁₁]
    have e : (-1 - 1 * 1 : Matrix (Fin n) (Fin n) R) = (-2 : R) • (1 : Matrix (Fin n) (Fin n) R) := by
      ext i j
      simp only [Matrix.sub_apply, Matrix.neg_apply, Matrix.one_mul, Matrix.smul_apply, smul_eq_mul,
        Matrix.one_apply]
      split_ifs <;> ring
    rw [e, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
    exact h2.neg.pow n
  obtain ⟨X₁, hX₁⟩ := exists_isUnit_det_toBlocks_add_mul
    (Matrix.fromBlocks 1 1 1 (-1) * G₁ * Matrix.fromBlocks 1 1 1 (-1))
    (by rw [Matrix.det_mul, Matrix.det_mul]; exact (hKdet.mul hG₁).mul hKdet)
  rw [blocks_conj_eq_fromBlocks_sums, Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₂₁] at hX₁
  have hsum : X₁ᵀ * S + S * -(S⁻¹ * X₁ᵀ * S) = 0 := by
    rw [Matrix.mul_neg, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hS,
      Matrix.one_mul, add_neg_cancel]
  refine ⟨X₁, -(S⁻¹ * X₁ᵀ * S), hsum, hX₁, ?_⟩
  have hG' := hG
  rw [← Matrix.fromBlocks_toBlocks G₁, ← Matrix.fromBlocks_toBlocks G₂, Matrix.fromBlocks_transpose,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply] at hG'
  obtain ⟨e11, e12, e21, e22⟩ := Matrix.fromBlocks_inj.mp hG'
  have E11 : G₁.toBlocks₁₁ᵀ * S * G₂.toBlocks₁₁ - G₁.toBlocks₂₁ᵀ * S * G₂.toBlocks₂₁ = S := by
    convert e11 using 1; noncomm_ring
  have E12 : G₁.toBlocks₁₁ᵀ * S * G₂.toBlocks₁₂ - G₁.toBlocks₂₁ᵀ * S * G₂.toBlocks₂₂ = 0 := by
    convert e12 using 1; noncomm_ring
  have E21 : G₁.toBlocks₁₂ᵀ * S * G₂.toBlocks₁₁ - G₁.toBlocks₂₂ᵀ * S * G₂.toBlocks₂₁ = 0 := by
    convert e21 using 1; noncomm_ring
  have E22 : G₁.toBlocks₁₂ᵀ * S * G₂.toBlocks₁₂ - G₁.toBlocks₂₂ᵀ * S * G₂.toBlocks₂₂ = -S := by
    convert e22 using 1; noncomm_ring
  obtain ⟨c1, c2⟩ := H_affine_combination_eq_of_quadratic_relation S _ _ _ _ _ _ _ _ X₁ _ E11 E12 E21 E22 hsum
  have h4 : IsUnit (4 : R) := by
    have := h2.mul h2
    norm_num at this
    exact this
  have hU4 : IsUnit (S + S + S + S).det := by
    have e : S + S + S + S = (4 : R) • S := by
      ext i j
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      ring
    rw [e, Matrix.det_smul]
    exact (h4.pow _).mul hS
  rw [← c2] at hU4
  exact isUnit_det_of_dual_blocks S _ _ _ _ _ _ hX₁ c1 hU4

end GlobalTheory
