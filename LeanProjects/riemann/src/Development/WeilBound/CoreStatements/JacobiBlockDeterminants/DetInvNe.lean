import Development.WeilBound.CoreStatements.JacobiBlockDeterminants.ExistsColFrame

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace HeightCancellation.G

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB
open SquareStatements.Sing
open scoped ComplexOrder

section Blocks

variable {R : Type} [CommRing R] {p q : ℕ}

theorem bmul {A B : Matrix (Fin (p + q)) (Fin (p + q)) R} (hA : IsBlockDiag p A) (hB : IsBlockDiag p B) :
    omBlock (A * B) = omBlock A * omBlock B ∧ wBlock (A * B) = wBlock A * wBlock B := by
  have e := (hA.mul hB).eq_fromBlocks
  rw [← Matrix.submatrix_mul_equiv A B _ (blockEquiv p q) _, hA.eq_fromBlocks, hB.eq_fromBlocks,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_inj] at e
  exact ⟨by simpa using e.1.symm, by simpa using e.2.2.2.symm⟩

theorem bd_ct {N j : ℕ} {A : Matrix (Fin N) (Fin N) ℂ} (hA : IsBlockDiag j A) : IsBlockDiag j Aᴴ := fun a b h => by
  rw [Matrix.conjTranspose_apply, hA b a fun e => h e.symm, star_zero]

def blk (a : Matrix (Fin q) (Fin q) R) (b : Matrix (Fin p) (Fin p) R) : Matrix (Fin (p + q)) (Fin (p + q)) R :=
  (Matrix.fromBlocks a 0 0 b).submatrix (blockEquiv p q).symm (blockEquiv p q).symm

theorem blk_apply (a : Matrix (Fin q) (Fin q) R) (b : Matrix (Fin p) (Fin p) R) (s t : Fin q ⊕ Fin p) :
    blk a b (blockEquiv p q s) (blockEquiv p q t) = Matrix.fromBlocks a 0 0 b s t := by
  simp [blk]

theorem om_blk (a : Matrix (Fin q) (Fin q) R) (b : Matrix (Fin p) (Fin p) R) : omBlock (blk a b) = a := by
  ext s t; exact blk_apply a b (.inl s) (.inl t)

theorem w_blk (a : Matrix (Fin q) (Fin q) R) (b : Matrix (Fin p) (Fin p) R) : wBlock (blk a b) = b := by
  ext s t; exact blk_apply a b (.inr s) (.inr t)

theorem bd_blk (a : Matrix (Fin q) (Fin q) R) (b : Matrix (Fin p) (Fin p) R) : IsBlockDiag p (blk a b) := by
  intro s t h
  obtain ⟨s, rfl⟩ := (blockEquiv p q).surjective s
  obtain ⟨t, rfl⟩ := (blockEquiv p q).surjective t
  rw [blk_apply]
  rcases s with s | s <;> rcases t with t | t
  · exact absurd (show (s : ℕ) < p + q - p ↔ (t : ℕ) < p + q - p by omega) h
  · rfl
  · rfl
  · exact absurd (show q + (s : ℕ) < p + q - p ↔ q + (t : ℕ) < p + q - p by omega) h

theorem tri_blk {a : Matrix (Fin q) (Fin q) R} {b : Matrix (Fin p) (Fin p) R} (ha : a.BlockTriangular id)
    (hb : b.BlockTriangular id) : (blk a b).BlockTriangular id := by
  intro s t h
  obtain ⟨s, rfl⟩ := (blockEquiv p q).surjective s
  obtain ⟨t, rfl⟩ := (blockEquiv p q).surjective t
  rw [blk_apply]
  rcases s with s | s <;> rcases t with t | t
  · exact ha (show (t : ℕ) < s from h)
  · rfl
  · rfl
  · exact hb (show (t : ℕ) < s from Nat.lt_of_add_lt_add_left (show q + (t : ℕ) < q + s from h))

end Blocks

section Rev

variable {F : Type} [Field F] {r : ℕ}

theorem tri_rev {U : Matrix (Fin r) (Fin r) F} (hU : U.BlockTriangular id) (hd : U.det ≠ 0) :
    (Uᵀ⁻¹.submatrix Fin.rev Fin.rev).BlockTriangular id := by
  letI := Matrix.invertibleOfIsUnitDet U hd.isUnit
  intro a b h
  rw [← Matrix.transpose_nonsing_inv]
  exact blockTriangular_inv_of_blockTriangular hU (show a.rev < b.rev from Fin.rev_lt_rev.2 h)

theorem det_rev (A : Matrix (Fin r) (Fin r) F) : (A.submatrix Fin.rev Fin.rev).det = A.det :=
  Matrix.det_submatrix_equiv_self Fin.revPerm A

theorem det_inv_ne {A : Matrix (Fin r) (Fin r) F} (h : A.det ≠ 0) : Aᵀ⁻¹.det ≠ 0 :=
  (Matrix.isUnit_nonsing_inv_det _ (by rw [Matrix.det_transpose]; exact h.isUnit)).ne_zero

theorem det_col {A : Matrix (Fin r) (Fin r) F} (h : A.det ≠ 0) : (A.submatrix id Fin.rev).det ≠ 0 := by
  have := Matrix.det_permute' Fin.revPerm A
  refine fun h0 => ?_
  rw [show A.submatrix id Fin.revPerm = A.submatrix id Fin.rev from rfl, h0] at this
  refine mul_ne_zero ?_ h this.symm
  rcases Int.units_eq_one_or (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin r))) with e | e <;> simp [e]

theorem inv_diag {U : Matrix (Fin r) (Fin r) F} (hU : U.BlockTriangular id) (hd : U.det ≠ 0) (k : Fin r) :
    U⁻¹ k k = (U k k)⁻¹ := by
  letI := Matrix.invertibleOfIsUnitDet U hd.isUnit
  have hi := blockTriangular_inv_of_blockTriangular hU
  have e := congrFun (congrFun (Matrix.mul_nonsing_inv U hd.isUnit) k) k
  rw [Matrix.mul_apply, Matrix.one_apply_eq, Finset.sum_eq_single k] at e
  · exact eq_inv_of_mul_eq_one_right e
  · intro l _ hl
    rcases lt_or_gt_of_ne hl with h | h
    · rw [hU h, zero_mul]
    · rw [hi h, mul_zero]
  · simp

theorem rev_mul (A B : Matrix (Fin r) (Fin r) F) (f g : Fin r → Fin r) :
    A.submatrix f Fin.rev * B.submatrix Fin.rev g = (A * B).submatrix f g :=
  Matrix.submatrix_mul_equiv A B f Fin.revPerm g

theorem tinv_tinv {A : Matrix (Fin r) (Fin r) F} (h : A.det ≠ 0) : Aᵀ⁻¹ᵀ⁻¹ = A := by
  rw [← Matrix.transpose_nonsing_inv A, Matrix.transpose_transpose, Matrix.nonsing_inv_nonsing_inv _ h.isUnit]

theorem tinv_mul (A B : Matrix (Fin r) (Fin r) F) : (A * B)ᵀ⁻¹ = Aᵀ⁻¹ * Bᵀ⁻¹ := by
  rw [Matrix.transpose_mul, Matrix.mul_inv_rev]

theorem tinv_rev (A : Matrix (Fin r) (Fin r) F) : (A.submatrix Fin.rev Fin.rev)ᵀ⁻¹ = Aᵀ⁻¹.submatrix Fin.rev Fin.rev :=
  Matrix.inv_submatrix_equiv Aᵀ Fin.revPerm Fin.revPerm

end Rev

section Tot

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l}
  {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {S : Finset ℕ}
  {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {M : FlagModel y (CMType H) (D.p + D.q) D.p} {𝔐 : HodgeCpt Y S M.x} {tie : FlagTie M 𝔐} {𝔐' : HodgeCpt Y S y}
  {Fl : 𝔐'.Flag} {pr : 𝔐'.X ⟶ 𝔐.X} {j : 𝔐.Li →+ 𝔐'.Li} {F : FrameData ι (CMType H) (D.p + D.q) M.Ω M.blk}

theorem mapT (hF : M.IsFrame F) (τ : CMType H) :
    IsBlockDiag D.p ((F.T τ).map (algebraMap M.Ω Φ)) ∧ IsUnit ((F.T τ).map (algebraMap M.Ω Φ)).det := by
  refine ⟨(hF.1 τ).1.map _, ?_⟩
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact (hF.1 τ).2.isUnit.map _

theorem bdA (hF : M.IsFrame F) (τ : CMType H) : IsBlockDiag D.p (((F.T τ).map (algebraMap M.Ω Φ))⁻¹ * M.g τ) ∧
    (((F.T τ).map (algebraMap M.Ω Φ))⁻¹ * M.g τ).det ≠ 0 := by
  refine ⟨((mapT hF τ).1.inv (mapT hF τ).2).mul (M.g_block τ), ?_⟩
  rw [Matrix.det_mul]
  exact mul_ne_zero (Matrix.isUnit_nonsing_inv_det _ (mapT hF τ).2).ne_zero (M.g_indep.isUnit_det τ).ne_zero

theorem flagW (ht : Tot tie 𝔐' Fl pr j) (hF : M.IsFrame F) (τ : CMType H) :
    Fl.b (.inl τ) = colFrame (fun a => j (tie.wFrame F τ a)) (wBlock (((F.T τ).map (algebraMap M.Ω Φ))⁻¹ * M.g τ)) := by
  funext k
  rw [ht.2.2.1 τ k, FlagTie.wFrame, map_colFrame ht.1.2.2.2.1.1, ← colFrame_mul,
    show (wBlock (F.T τ)).map (algebraMap M.Ω Φ) = wBlock ((F.T τ).map (algebraMap M.Ω Φ)) from rfl,
    ← (bmul (mapT hF τ).1 (bdA hF τ).1).2, Matrix.mul_nonsing_inv_cancel_left _ _ (mapT hF τ).2]

theorem flagO (ht : Tot tie 𝔐' Fl pr j) (hF : M.IsFrame F) (τ : CMType H) {v : Fin D.q → 𝔐.Vgen (.inr τ)}
    (hv : ∀ a b, tie.omFrame F τ a (v b) = if a = b then 1 else 0) :
    Fl.b (.inr τ) = colFrame (fun a => j (v a))
      ((omBlock (((F.T τ).map (algebraMap M.Ω Φ))⁻¹ * M.g τ))ᵀ⁻¹.submatrix id Fin.rev) := by
  have hT : (omBlock (F.T τ)).det ≠ 0 := fun h => (hF.1 τ).2 (by rw [(hF.1 τ).1.det_eq_blocks, h, zero_mul])
  have e1 : colFrame (tie.omFrame F τ) (omBlock (F.T τ))⁻¹ = tie.eO τ := by
    rw [FlagTie.omFrame, ← colFrame_mul, Matrix.mul_nonsing_inv _ hT.isUnit, colFrame_one]
  have e2 : (omBlock (F.T τ))⁻¹ᵀ⁻¹ = (omBlock (F.T τ))ᵀ := by
    rw [← Matrix.transpose_nonsing_inv, Matrix.nonsing_inv_nonsing_inv _ hT.isUnit]
  have hd := colFrame_dual _ _ hv (omBlock (F.T τ))⁻¹ (Matrix.isUnit_nonsing_inv_det _ hT.isUnit)
  rw [e1, e2] at hd
  have e3 : (fun a => j ((colFrame v (omBlock (F.T τ))ᵀ a : 𝔐.Vgen (.inr τ)) : 𝔐.Li)) =
      colFrame (fun a => j (v a)) (omBlock ((F.T τ).map (algebraMap M.Ω Φ)))ᵀ := by
    refine Eq.trans ?_ (map_colFrame ht.1.2.2.2.1.1 (fun a => (v a : 𝔐.Li)) (omBlock (F.T τ))ᵀ)
    funext a
    simp [colFrame]
  have e4 : omBlock ((F.T τ).map (algebraMap M.Ω Φ)) * omBlock (((F.T τ).map (algebraMap M.Ω Φ))⁻¹ * M.g τ) =
      omBlock (M.g τ) := by
    rw [← (bmul (mapT hF τ).1 (bdA hF τ).1).1, Matrix.mul_nonsing_inv_cancel_left _ _ (mapT hF τ).2]
  have hT' : IsUnit (omBlock ((F.T τ).map (algebraMap M.Ω Φ)))ᵀ.det := by
    have := (mapT hF τ).2
    rw [(mapT hF τ).1.det_eq_blocks] at this
    rw [Matrix.det_transpose]
    exact isUnit_of_mul_isUnit_left this
  funext k
  rw [ht.2.2.2 τ _ hd k, e3, ← colFrame_mul, ← e4, tinv_mul, Matrix.mul_nonsing_inv_cancel_left _ _ hT']
  rfl

theorem frame_up (ht : Tot tie 𝔐' Fl pr j) {z : Spec (CommRingCat.of ℂ) ⟶ 𝔐'.X} (s : CMType H ⊕ CMType H) {r : ℕ}
    {b : Fin r → 𝔐.Li} (hb : (𝔐.V s).IsFrameAt b ⟨centre (z ≫ pr), 𝔐.all _⟩) :
    (𝔐'.V s).IsFrameAt (fun a => j (b a)) ⟨centre z, 𝔐'.all _⟩ := by
  rw [ht.2.1 s]
  exact FlagPull.pull_isFrameAt ht.1.1 ht.1.2.2.2.1 ⟨centre z, 𝔐'.all _⟩ (𝔐.all _) hb

end Tot

theorem c3w : GradedLineNormsW := by
  intro E _ _ _ H D l Xo c Y S K _ ι _ Φ _ y M 𝔐 tie 𝔐' Fl pr j z F τ B h G ht hF hfr ⟨bB, tB, dB, bh, dh, hv⟩ bG pG _ hG k
  have e : wBlock (hᴴ * G * h) = (wBlock h)ᴴ * wBlock G * wBlock h := by
    rw [(bmul ((bd_ct bh).mul bG) bh).2, (bmul (bd_ct bh) bG).2]; rfl
  rw [e]
  refine grNorm_of 𝔐' (frame_up ht (.inl τ) hfr) (gram_pull ht.1 hG) (pG.submatrix (wEmb_strictMono _ _).injective)
    (flagW ht hF τ) (U := wBlock B) (fun a b hab => tB (wEmb_strictMono _ _ hab))
    (fun h0 => dB (by rw [bB.det_eq_blocks, h0, mul_zero])) (fun h0 => dh (by rw [bh.det_eq_blocks, h0, mul_zero]))
    (fun a b => ?_) k
  rw [← (bmul (bdA hF τ).1 bB).2]
  exact hv _ _

theorem c3o : GradedLineNormsDualOmega := by
  intro E _ _ _ H D l Xo c Y S K _ ι _ Φ _ y M 𝔐 tie 𝔐' Fl pr j z F τ B h G ht hF hfr ⟨bB, tB, dB, bh, dh, hv⟩ bG pG
    _ ⟨v, Γ, hv1, hG, hΓ⟩ k
  have dB' : (omBlock B).det ≠ 0 := fun h0 => dB (by rw [bB.det_eq_blocks, h0, zero_mul])
  have dh' : (omBlock h).det ≠ 0 := fun h0 => dh (by rw [bh.det_eq_blocks, h0, zero_mul])
  have tB' : (omBlock B).BlockTriangular id := fun a b hab => tB (omEmb_strictMono _ _ hab)
  have eΓ : Γ = (omBlock G)ᵀ⁻¹ := (Matrix.inv_eq_right_inv hΓ).symm
  have pG' : (omBlock G).PosDef := pG.submatrix (omEmb_strictMono _ _).injective
  have e : revDual (omBlock (hᴴ * G * h)) = ((omBlock h)ᵀ⁻¹.submatrix id Fin.rev)ᴴ * Γ *
      (omBlock h)ᵀ⁻¹.submatrix id Fin.rev := by
    rw [(bmul ((bd_ct bh).mul bG) bh).1, (bmul (bd_ct bh) bG).1, revDual, tinv_mul, tinv_mul, ← eΓ,
      Matrix.conjTranspose_submatrix, Matrix.conjTranspose_nonsing_inv]
    rfl
  have e2 : (B (omEmb D.p D.q k.rev) (omEmb D.p D.q k.rev))⁻¹ = ((omBlock B)ᵀ⁻¹.submatrix Fin.rev Fin.rev) k k := by
    rw [← Matrix.transpose_nonsing_inv]
    exact (inv_diag tB' dB' k.rev).symm
  rw [e, e2]
  refine grNorm_of 𝔐' (frame_up ht (.inr τ) ((omBundle_dualFrame 𝔐 τ _ hfr).2 v hv1)) (gram_pull ht.1 hG)
    (eΓ ▸ pG'.transpose.inv) (flagO ht hF τ hv1) (tri_rev tB' dB') (by rw [det_rev]; exact det_inv_ne dB')
    (det_col (det_inv_ne dh')) (fun a b => ?_) k
  rw [rev_mul, ← tinv_mul, ← (bmul (bdA hF τ).1 bB).1]
  exact (val_inv (A := (omBlock (inFrame M F τ B))ᵀ) (h := (omBlock h)ᵀ) (𝔐'.all _) (fun a b => hv _ _)
    (by rwa [Matrix.det_transpose])).2 a b.rev

theorem c1 : C1 := by
  intro E _ _ _ H D l Xo c Y S K _ ι _ Φ _ y M 𝔐 tie 𝔐' Fl pr j z F τ ht hF hW hO
  obtain ⟨⟨v, hv⟩, hv'⟩ := omBundle_dualFrame 𝔐 τ _ hO
  obtain ⟨U, h, tU, dU, dh, vU⟩ := exists_adapt 𝔐'.tie.gen (𝔐'.all _) (frame_up ht (.inl τ) hW) (Fl.sub (.inl τ))
    (flagW ht hF τ)
  obtain ⟨U', h', tU', dU', dh', vU'⟩ := exists_adapt 𝔐'.tie.gen (𝔐'.all _) (frame_up ht (.inr τ) (hv' v hv))
    (Fl.sub (.inr τ)) (flagO ht hF τ hv)
  obtain ⟨bA, dA⟩ := bdA hF τ
  set A := ((F.T τ).map (algebraMap M.Ω Φ))⁻¹ * M.g τ with hA
  have dA' : (omBlock A).det ≠ 0 := fun h0 => dA (by rw [bA.det_eq_blocks, h0, zero_mul])
  have d1 : (h'.submatrix id Fin.rev).det ≠ 0 := det_col dh'
  refine ⟨blk (U'ᵀ⁻¹.submatrix Fin.rev Fin.rev) U, blk (h'.submatrix id Fin.rev)ᵀ⁻¹ h, bd_blk _ _,
    tri_blk (tri_rev tU' dU') tU, ?_, bd_blk _ _, ?_, fun a b => ?_⟩
  · rw [(bd_blk _ _).det_eq_blocks, om_blk, w_blk, det_rev]
    exact mul_ne_zero (det_inv_ne dU') dU
  · rw [(bd_blk _ _).det_eq_blocks, om_blk, w_blk]
    exact mul_ne_zero (det_inv_ne d1) dh
  · obtain ⟨a, rfl⟩ := (blockEquiv D.p D.q).surjective a
    obtain ⟨b, rfl⟩ := (blockEquiv D.p D.q).surjective b
    have e := congrFun (congrFun (bA.mul (bd_blk (U'ᵀ⁻¹.submatrix Fin.rev Fin.rev) U)).eq_fromBlocks a) b
    rw [Matrix.submatrix_apply, (bmul bA (bd_blk _ _)).1, (bmul bA (bd_blk _ _)).2, om_blk, w_blk] at e
    rw [blk_apply]
    show ValAt _ _ ((A * blk (U'ᵀ⁻¹.submatrix Fin.rev Fin.rev) U) (blockEquiv D.p D.q a) (blockEquiv D.p D.q b)) _
    rw [e]
    have z0 : ValAt 𝔐'.ξ z 0 0 := ⟨𝔐'.all _, 0, map_zero _, map_zero _⟩
    rcases a with a | a <;> rcases b with b | b
    · have e1 : omBlock A * U'ᵀ⁻¹.submatrix Fin.rev Fin.rev =
          (((omBlock A)ᵀ⁻¹.submatrix id Fin.rev * U').submatrix id Fin.rev)ᵀ⁻¹ := by
        have e2 : ((omBlock A)ᵀ⁻¹.submatrix id Fin.rev * U').submatrix id Fin.rev =
            (omBlock A)ᵀ⁻¹ * U'.submatrix Fin.rev Fin.rev := by
          have e3 : U' = (U'.submatrix Fin.rev id).submatrix Fin.rev id := by
            ext s t; simp
          conv_lhs => rw [e3, rev_mul]
          rfl
        rw [e2, tinv_mul, tinv_tinv dA', tinv_rev]
      rw [e1]
      exact (val_inv (A := (((omBlock A)ᵀ⁻¹.submatrix id Fin.rev * U').submatrix id Fin.rev)ᵀ)
        (h := (h'.submatrix id Fin.rev)ᵀ) (𝔐'.all _) (fun a b => vU' _ _) (by rwa [Matrix.det_transpose])).2 a b
    · exact z0
    · exact z0
    · exact vU a b

end HeightCancellation.G
