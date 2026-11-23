import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.OmHeightslockG

open AlgebraicGeometry CategoryTheory NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.BMx ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder

namespace PositivityTheory.Xgp.c_bm_exists_period

theorem det_head {p q k : ℕ} {I : Type} [Fintype I] [DecidableEq I] (M : Matrix (Fin (p + q)) (Fin (p + q)) ℂ)
    (f : I → Fin q ⊕ Fin p) (hf : Function.Injective f)
    (hr : ∀ x, ((blockEquiv p q x : Fin (p + q)) : ℕ) < k ↔ ∃ i, f i = x) :
    (M.submatrix (Subtype.val : {a : Fin (p + q) // (a : ℕ) < k} → _) Subtype.val).det =
      ((M.submatrix (blockEquiv p q) (blockEquiv p q)).submatrix f f).det := by
  let e : I ≃ {a : Fin (p + q) // (a : ℕ) < k} := Equiv.ofBijective
    (fun i => ⟨blockEquiv p q (f i), (hr _).2 ⟨i, rfl⟩⟩)
    ⟨fun i j h => hf ((blockEquiv p q).injective (congrArg Subtype.val h)), fun ⟨a, ha⟩ => by
      obtain ⟨x, rfl⟩ := (blockEquiv p q).surjective a
      obtain ⟨i, rfl⟩ := (hr x).1 ha
      exact ⟨i, rfl⟩⟩
  rw [← Matrix.det_submatrix_equiv_self e]
  rfl

theorem sub_conj {m I : Type} [Fintype m] (H Y : Matrix m m ℂ) (f : I → m) :
    (Hᴴ * Y * H).submatrix f f = (H.submatrix id f)ᴴ * Y * H.submatrix id f := by
  ext a b
  simp [Matrix.mul_apply]

theorem periodGram_of {p q : ℕ} (Pi : Matrix (Fin (p + q)) (Fin (p + q)) ℂ) (Go : Matrix (Fin q) (Fin q) ℂ)
    (Gw : Matrix (Fin p) (Fin p) ℂ) (Z : Matrix (Fin q) (Fin p) ℂ) (hGo : Go.PosDef) (hdet : IsUnit Pi.det)
    (h : (gramOf (sigForm (p + q) p) Pi).submatrix (blockEquiv p q) (blockEquiv p q) =
      (fromBlocks 1 Z 0 1)ᴴ * fromBlocks (-Go) 0 0 Gw * fromBlocks 1 Z 0 1) :
    IsPeriodGram p Pi ((fromBlocks Go 0 0 Gw).submatrix (blockEquiv p q).symm (blockEquiv p q).symm) := by
  classical
  refine ⟨⟨hdet, ?_⟩, fun h' hb k => ?_⟩
  · let f : {a : Fin (p + q) // (a : ℕ) < p + q - p} → Fin q := fun a => ⟨a.1, by have := a.2; omega⟩
    have hf : Function.Injective f := fun a b e => Subtype.ext (Fin.ext (congrArg Fin.val e :))
    convert hGo.submatrix hf using 1
    ext a b
    have := congrFun (congrFun h (.inl (f a))) (.inl (f b))
    simp only [fromBlocks_conjTranspose, fromBlocks_multiply] at this
    simp at this
    simp only [gramHead, Matrix.neg_apply, Matrix.submatrix_apply]
    rw [neg_eq_iff_eq_neg]
    exact this
  have e1 : (gramOf (sigForm (p + q) p) (Pi * h')).submatrix (blockEquiv p q) (blockEquiv p q) =
      (fromBlocks (omBlock h') 0 0 (wBlock h'))ᴴ *
        ((fromBlocks 1 Z 0 1)ᴴ * fromBlocks (-Go) 0 0 Gw * fromBlocks 1 Z 0 1) *
        fromBlocks (omBlock h') 0 0 (wBlock h') := by
    rw [← h, ← hb.eq_fromBlocks, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
      Matrix.submatrix_mul_equiv]
    simp only [gramOf, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have e2 : (h'ᴴ * (fromBlocks Go 0 0 Gw).submatrix (blockEquiv p q).symm (blockEquiv p q).symm * h').submatrix
      (blockEquiv p q) (blockEquiv p q) =
      (fromBlocks (omBlock h') 0 0 (wBlock h'))ᴴ * fromBlocks Go 0 0 Gw * fromBlocks (omBlock h') 0 0 (wBlock h') := by
    rw [← hb.eq_fromBlocks, Matrix.conjTranspose_submatrix, ← Matrix.submatrix_mul_equiv _ _ _ (blockEquiv p q),
      ← Matrix.submatrix_mul_equiv _ _ _ (blockEquiv p q)]
    simp
  unfold gramHead
  by_cases hk : q ≤ k
  · let f : Fin q ⊕ {b : Fin p // q + (b : ℕ) < k} → Fin q ⊕ Fin p := Sum.map id Subtype.val
    have hf : Function.Injective f := Sum.map_injective.2 ⟨Function.injective_id, Subtype.val_injective⟩
    have hr : ∀ x, ((blockEquiv p q x : Fin (p + q)) : ℕ) < k ↔ ∃ i, f i = x := by
      rintro (a | b)
      · exact ⟨fun _ => ⟨.inl a, rfl⟩, fun _ => by show (a : ℕ) < k; omega⟩
      · refine ⟨fun h => ⟨.inr ⟨b, h⟩, rfl⟩, ?_⟩
        rintro ⟨a | a, ha⟩
        · simp [f] at ha
        · obtain rfl : a.1 = b := by simpa [f] using ha
          exact a.2
    rw [det_head _ f hf hr, det_head _ f hf hr, e1, e2, sub_conj, sub_conj]
    set h₂ : Matrix (Fin p) {b : Fin p // q + (b : ℕ) < k} ℂ := (wBlock h').submatrix id Subtype.val
    have e3 : (fromBlocks (omBlock h') 0 0 (wBlock h')).submatrix id f = fromBlocks (omBlock h') 0 0 h₂ := by
      ext (a | a) (b | b) <;> rfl
    rw [e3]
    have e4 : (fromBlocks (omBlock h') 0 0 h₂)ᴴ *
        ((fromBlocks 1 Z 0 1)ᴴ * fromBlocks (-Go) 0 0 Gw * fromBlocks 1 Z 0 1) * fromBlocks (omBlock h') 0 0 h₂ =
        (fromBlocks (omBlock h') (Z * h₂) 0 1)ᴴ * fromBlocks (-Go) 0 0 (h₂ᴴ * Gw * h₂) *
          fromBlocks (omBlock h') (Z * h₂) 0 1 := by
      simp only [fromBlocks_conjTranspose, fromBlocks_multiply]
      simp [Matrix.mul_assoc, Matrix.mul_add, Matrix.add_mul]
    have e5 : (fromBlocks (omBlock h') 0 0 h₂)ᴴ * fromBlocks Go 0 0 Gw * fromBlocks (omBlock h') 0 0 h₂ =
        (fromBlocks (omBlock h') 0 0 1)ᴴ * fromBlocks Go 0 0 (h₂ᴴ * Gw * h₂) * fromBlocks (omBlock h') 0 0 1 := by
      simp only [fromBlocks_conjTranspose, fromBlocks_multiply]
      simp [Matrix.mul_assoc]
    rw [e4, e5]
    simp only [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_fromBlocks_zero₂₁, Matrix.det_neg, norm_mul,
      norm_pow, norm_neg, norm_one, one_pow, one_mul]
  · let f : {a : Fin q // (a : ℕ) < k} → Fin q ⊕ Fin p := fun a => .inl a.1
    have hf : Function.Injective f := fun a b e => Subtype.ext (Sum.inl_injective e)
    have hr : ∀ x, ((blockEquiv p q x : Fin (p + q)) : ℕ) < k ↔ ∃ i, f i = x := by
      rintro (a | b)
      · refine ⟨fun h => ⟨⟨a, h⟩, rfl⟩, ?_⟩
        rintro ⟨b, hb⟩
        obtain rfl : b.1 = a := Sum.inl_injective hb
        exact b.2
      · refine ⟨fun h => absurd h (by show ¬ q + (b : ℕ) < k; omega), ?_⟩
        rintro ⟨a, ha⟩
        simp [f] at ha
    rw [det_head _ f hf hr, det_head _ f hf hr, e1, e2, sub_conj, sub_conj]
    set h₁ : Matrix (Fin q) {a : Fin q // (a : ℕ) < k} ℂ := (omBlock h').submatrix id Subtype.val
    set O : Matrix (Fin p) {a : Fin q // (a : ℕ) < k} ℂ := 0 with hO
    have e3 : (fromBlocks (omBlock h') 0 0 (wBlock h')).submatrix id f = fromRows h₁ O := by
      ext (a | a) b <;> rfl
    rw [e3]
    have e4 : (fromRows h₁ O)ᴴ * ((fromBlocks 1 Z 0 1)ᴴ * fromBlocks (-Go) 0 0 Gw * fromBlocks 1 Z 0 1) *
        fromRows h₁ O = -((fromRows h₁ O)ᴴ * fromBlocks Go 0 0 Gw * fromRows h₁ O) := by
      simp only [fromBlocks_conjTranspose, fromBlocks_multiply, conjTranspose_fromRows_eq_fromCols_conjTranspose,
        fromCols_mul_fromBlocks, fromCols_mul_fromRows]
      simp [hO]
    rw [e4, Matrix.det_neg]
    simp

theorem periodGram_conj {N j : ℕ} {Pi G : Matrix (Fin N) (Fin N) ℂ} (h : IsPeriodGram j Pi G) :
    IsPeriodGram j (Pi.map (starRingEnd ℂ)) (G.map (starRingEnd ℂ)) := by
  classical
  have g : ∀ (k : ℕ) (X : Matrix (Fin N) (Fin N) ℂ), gramHead (sigForm N j) k (X.map (starRingEnd ℂ)) =
      (gramHead (sigForm N j) k X).map (starRingEnd ℂ) := fun k X => by
    ext a b
    simp [gramHead, gramOf, Matrix.mul_apply, Matrix.diagonal_apply, apply_ite]
  have dm : ∀ {I : Type} [Fintype I] [DecidableEq I] (X : Matrix I I ℂ),
      (X.map (starRingEnd ℂ)).det = starRingEnd ℂ X.det := fun X => (RingHom.map_det _ X).symm
  refine ⟨⟨?_, ?_⟩, fun h' hb k => ?_⟩
  · rw [dm]; exact h.1.1.map _
  · rw [g]
    suffices e : -(gramHead (sigForm N j) (N - j) Pi).map (starRingEnd ℂ) = (-gramHead (sigForm N j) (N - j) Pi)ᵀ by
      rw [e]; exact h.1.2.transpose
    ext a b
    have := h.1.2.isHermitian.apply a b
    simp only [Matrix.neg_apply, star_neg, neg_inj] at this
    simp only [Matrix.neg_apply, Matrix.map_apply, Matrix.transpose_apply, neg_inj]
    rw [← this]; simp
  · have := h.2 (h'.map (starRingEnd ℂ)) (fun a b hab => by simp [hb a b hab]) k
    have e1 : Pi.map (starRingEnd ℂ) * h' = (Pi * h'.map (starRingEnd ℂ)).map (starRingEnd ℂ) := by
      ext a b; simp [Matrix.mul_apply]
    have e2 : (h'ᴴ * G.map (starRingEnd ℂ) * h').submatrix (Subtype.val : {a : Fin N // (a : ℕ) < k} → Fin N)
        (Subtype.val : {a : Fin N // (a : ℕ) < k} → Fin N) = (((h'.map (starRingEnd ℂ))ᴴ * G * h'.map (starRingEnd ℂ)).submatrix
          (Subtype.val : {a : Fin N // (a : ℕ) < k} → Fin N)
          (Subtype.val : {a : Fin N // (a : ℕ) < k} → Fin N)).map (starRingEnd ℂ) := by
      ext a b; simp [Matrix.mul_apply]
    rw [e1, g, e2, dm, dm, Complex.norm_conj, Complex.norm_conj, this]

theorem blockG_conj {p q : ℕ} (Γ : Matrix (Fin (p + q)) (Fin (p + q)) ℂ) :
    blockG (Γ.map (starRingEnd ℂ)) = (blockG Γ).map (starRingEnd ℂ) := by
  have e : (omBlock (Γ.map (starRingEnd ℂ)))ᵀ⁻¹ = ((omBlock Γ)ᵀ⁻¹).map (starRingEnd ℂ) := by
    have e1 : (omBlock (Γ.map (starRingEnd ℂ)))ᵀ = (omBlock Γ)ᴴ := rfl
    rw [e1, ← Matrix.conjTranspose_nonsing_inv, ← Matrix.transpose_nonsing_inv]
    rfl
  ext a b
  simp only [blockG, e, Matrix.submatrix_apply, Matrix.map_apply]
  rcases (blockEquiv p q).symm a with a | a <;> rcases (blockEquiv p q).symm b with b | b <;>
    simp [wBlock]

end PositivityTheory.Xgp.c_bm_exists_period
