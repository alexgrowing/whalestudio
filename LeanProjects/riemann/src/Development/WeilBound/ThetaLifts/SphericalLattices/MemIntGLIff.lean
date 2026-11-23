import Development.WeilBound.ThetaLifts.SphericalLattices.LocModSt
import Development.WeilBound.CoreStatements.LocalThetaKernels.IwasLoc

noncomputable section

namespace PositivityTheory.Sph.M2.Chart

open Matrix Formalism.UG GlobalTheory.CompanionTheory.VacLoc.BigCellLocal PositivityTheory.ThKH.Iwas

section Alg

variable {L : Type} [Field L] {c : L →+* L} {β : Type} [Fintype β] [DecidableEq β]

omit [Fintype β] in
theorem Wm_transpose : (Wm L β)ᵀ = Wm L β := by
  simp [Wm, fromBlocks_transpose]

theorem exists_compl (hc : ∀ x, c (c x) = x) {w : L} (hw : w + c w = 1) {Y : Matrix (β ⊕ β) β L} {R : Matrix β (β ⊕ β) L}
    (hR : R * Y = 1) (hY : Yᵀ * Wm L β * Y.map c = 0) : ∃ X : Matrix (β ⊕ β) β L, Iso c (Wm L β) (Wm L β) (fromCols Y X) := by
  have hcc : ∀ {ι κ : Type} (N : Matrix ι κ L), (N.map c).map c = N := fun N => Matrix.ext fun i j => hc _
  have sym : ∀ A B : Matrix (β ⊕ β) β L, ((Aᵀ * Wm L β * B.map c).map c)ᵀ = Bᵀ * Wm L β * A.map c := fun A B => by
    rw [Matrix.map_mul, Matrix.map_mul, hcc, Wm_map, transpose_mul, transpose_mul, Wm_transpose, Matrix.mul_assoc]
    rfl
  obtain ⟨X₀, h1⟩ : ∃ X₀ : Matrix (β ⊕ β) β L, Yᵀ * Wm L β * X₀.map c = 1 :=
    ⟨(Wm L β * Rᵀ).map c, by
      rw [hcc, Matrix.mul_assoc, ← Matrix.mul_assoc (Wm L β), Wm_mul_self, Matrix.one_mul, ← transpose_mul, hR,
        transpose_one]⟩
  have h2 : X₀ᵀ * Wm L β * Y.map c = 1 := by
    rw [← sym, h1, map_one', transpose_one]
  obtain ⟨H, hH⟩ : ∃ H, X₀ᵀ * Wm L β * X₀.map c = H := ⟨_, rfl⟩
  have h3 : (H.map c)ᵀ = H := by rw [← hH, sym]
  have h4 : ((w • H)ᵀ).map c = c w • H := by
    ext i j
    have : c (H j i) = H i j := congrFun (congrFun h3 i) j
    simp [this]
  have e1 : (X₀ - Y * (w • H)ᵀ).map c = X₀.map c - Y.map c * (c w • H) := by
    rw [Matrix.map_sub _ (map_sub c), Matrix.map_mul, h4]
  have e2 : (X₀ - Y * (w • H)ᵀ)ᵀ * Wm L β = X₀ᵀ * Wm L β - (w • H) * (Yᵀ * Wm L β) := by
    rw [transpose_sub, transpose_mul, transpose_transpose, Matrix.sub_mul, Matrix.mul_assoc]
  have a1 : Yᵀ * Wm L β * (X₀ - Y * (w • H)ᵀ).map c = 1 := by
    rw [e1, Matrix.mul_sub, h1, ← Matrix.mul_assoc, hY, Matrix.zero_mul, sub_zero]
  have a2 : (X₀ - Y * (w • H)ᵀ)ᵀ * Wm L β * Y.map c = 1 := by
    rw [← sym, a1, map_one', transpose_one]
  have a3 : (X₀ - Y * (w • H)ᵀ)ᵀ * Wm L β * (X₀ - Y * (w • H)ᵀ).map c = 0 := by
    rw [e2, Matrix.sub_mul, Matrix.mul_assoc (w • H), a1, e1, Matrix.mul_sub, hH, ← Matrix.mul_assoc, h2, Matrix.one_mul,
      Matrix.mul_one, sub_sub, ← add_smul, add_comm, hw, one_smul, sub_self]
  refine ⟨X₀ - Y * (w • H)ᵀ, ?_⟩
  unfold Iso
  rw [transpose_fromCols, fromCols_map, fromRows_mul, fromRows_mul_fromCols, hY, a1, a2, a3]
  rfl

theorem exists_leftInv {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] {Y : Matrix ι κ L}
    (hY : ∀ z, Y *ᵥ z = 0 → z = 0) : ∃ R : Matrix κ ι L, R * Y = 1 := by
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' Y) (LinearMap.ker_eq_bot'.2 hY)
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  have := congrArg LinearMap.toMatrix' hg
  rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_id] at this

theorem block_iff {M : Matrix (β ⊕ β) (β ⊕ β) L} {T : Matrix β β L} (hT : IsUnit T.det) :
    (∃ t : Matrix β β L, M * fromRows T (0 : Matrix β β L) = fromRows T (0 : Matrix β β L) * t) ↔ M.toBlocks₂₁ = 0 := by
  rw [← fromBlocks_toBlocks M, fromBlocks_mul_fromRows, toBlocks_fromBlocks₂₁]
  simp only [Matrix.mul_zero, add_zero, fromRows_mul, Matrix.zero_mul, fromRows_ext_iff]
  constructor
  · rintro ⟨t, -, h⟩
    rw [← Matrix.mul_nonsing_inv_cancel_right T M.toBlocks₂₁ hT, h, Matrix.zero_mul]
  · intro h
    exact ⟨T⁻¹ * (M.toBlocks₁₁ * T), (Matrix.mul_nonsing_inv_cancel_left _ _ hT).symm, by rw [h, Matrix.zero_mul]⟩

theorem block_det {M : Matrix (β ⊕ β) (β ⊕ β) L} {T t : Matrix β β L} (hT : IsUnit T.det)
    (h : M * fromRows T (0 : Matrix β β L) = fromRows T (0 : Matrix β β L) * t) : M.toBlocks₁₁.det = t.det := by
  rw [← fromBlocks_toBlocks M, fromBlocks_mul_fromRows] at h
  simp only [Matrix.mul_zero, add_zero, fromRows_mul, Matrix.zero_mul, fromRows_ext_iff] at h
  have := congrArg det h.1
  rw [det_mul, det_mul, mul_comm] at this
  exact mul_left_cancel₀ hT.ne_zero this

end Alg

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {c : L →+* L} {m : ℕ}

theorem exists_move {ϖ : L} {q : ℕ} (hU : IsUnramInv ϖ c q) {Y : Matrix (Fin m ⊕ Fin m) (Fin m) L}
    (hf : ∀ z, Y *ᵥ z = 0 → z = 0) (hY : Yᵀ * Wm L (Fin m) * Y.map c = 0) :
    ∃ k k' : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L, k * k' = 1 ∧ Iso c (Wm L (Fin m)) (Wm L (Fin m)) k ∧
      (∀ i j, Valued.v (k i j) ≤ 1) ∧ (∀ i j, Valued.v (k' i j) ≤ 1) ∧
      ∃ T : Matrix (Fin m) (Fin m) L, IsUnit T.det ∧ k * Y = fromRows T (0 : Matrix (Fin m) (Fin m) L) := by
  obtain ⟨hc, hv, -, -, ⟨x, hx, hx1⟩, -, -⟩ := hU
  have hx0 : c x - x ≠ 0 := by
    intro h; rw [h, map_zero] at hx1; exact zero_ne_one hx1
  have hw : c x * (c x - x)⁻¹ + c (c x * (c x - x)⁻¹) = 1 := by
    rw [map_mul, map_inv₀, map_sub, hc, ← neg_sub (c x) x, inv_neg]
    field_simp
    ring
  obtain ⟨R, hR⟩ := exists_leftInv hf
  obtain ⟨X, hX⟩ := exists_compl hc hw hR hY
  obtain ⟨k, hk, hki, h0⟩ := exists_reduce hc hv _ hX
  have hku := Matrix.mul_nonsing_inv _ (hk.isUnit_det Wm_det)
  have h21 : (k * fromCols Y X).toBlocks₂₁ = 0 := Matrix.ext h0
  refine ⟨k, k⁻¹, hku, hk, hki, fun i j => ?_, (k * fromCols Y X).toBlocks₁₁, ?_, ?_⟩
  · rw [inv_apply_of_iso hc hk hku, hv]; exact hki _ _
  · have := (hk.mul hX).isUnit_det Wm_det
    rw [← fromBlocks_toBlocks (k * fromCols Y X), h21, det_fromBlocks_zero₂₁] at this
    exact isUnit_of_mul_isUnit_left this
  · ext (i | i) j
    · rfl
    · exact h0 i j

theorem mem_IntGL_iff {g : GL (Fin m ⊕ Fin m) L} :
    g ∈ IntGL L m ↔ (∀ i j, Valued.v (g.val i j) ≤ 1) ∧ ∀ i j, Valued.v ((g⁻¹).val i j) ≤ 1 := by
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨fun i j => (k.val i j).2, fun i j => ((k⁻¹).val i j).2⟩
  · rintro ⟨h1, h2⟩
    have inj : Function.Injective
        ((intL L).subtype.mapMatrix : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (intL L) →+* _) := fun a b e => by
      ext i j
      exact congrFun (congrFun e i) j
    refine ⟨⟨Matrix.of fun i j => ⟨_, h1 i j⟩, Matrix.of fun i j => ⟨_, h2 i j⟩, inj ?_, inj ?_⟩, Units.ext rfl⟩
    · rw [map_mul, map_one]; exact Units.mul_inv g
    · rw [map_mul, map_one]; exact Units.inv_mul g

end PositivityTheory.Sph.M2.Chart

end
