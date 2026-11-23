import Mathlib
import Mathlib
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
import Development.AutomorphicSpectrum.Statements.MetricStatements.ExistsFlagModelBaseMetric
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.RootOnFund
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ContDiffUncentre
import Development.AutomorphicSpectrum.Proofs.MetricProofs.OmHeightslockG
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalRingPointsExistsUniqueStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexPointsIffCentresStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValAtIffValueAtStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.InteriorPointPolarisedStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GramMatrixTwoFramesStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GramMatrixConjugationStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ConjugatePointSameCentreStatement
import Development.WeilBound.CoreStatements.PluriharmonicCharts.RefNorm
import Development.WeilBound.CoreStatements.PluriharmonicCharts.XCBmExistsBlockpos
import Development.WeilBound.CoreStatements.PluriharmonicCharts.XCBmExistsGram
open AlgebraicGeometry CategoryTheory NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.BMx ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder

namespace PositivityTheory.Xgp.c_bm_exists_hom

open GroundTheory.Heights₂.Heights.LowerBoundFree

section Lin

variable {R : Type} [CommRing R] {p q : ℕ}

theorem blocks_mul {A B : Matrix (Fin (p + q)) (Fin (p + q)) R} (hA : IsBlockDiag p A) (hB : IsBlockDiag p B) :
    omBlock (A * B) = omBlock A * omBlock B ∧ wBlock (A * B) = wBlock A * wBlock B := by
  have e := (hA.mul hB).eq_fromBlocks
  rw [← Matrix.submatrix_mul_equiv A B _ (blockEquiv p q) _, hA.eq_fromBlocks, hB.eq_fromBlocks,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_inj] at e
  exact ⟨by simpa using e.1.symm, by simpa using e.2.2.2.symm⟩

theorem omBlock_one : omBlock (1 : Matrix (Fin (p + q)) (Fin (p + q)) R) = 1 :=
  Matrix.submatrix_one _ (omEmb_strictMono p q).injective

theorem isBlockDiag_conjTranspose {N j : ℕ} {A : Matrix (Fin N) (Fin N) ℂ} (hA : IsBlockDiag j A) :
    IsBlockDiag j Aᴴ := fun a b h => by
  rw [Matrix.conjTranspose_apply, hA b a fun e => h e.symm, star_zero]

theorem blockG_conj (Γ : Matrix (Fin (p + q)) (Fin (p + q)) ℂ) :
    blockG (Γ.map (starRingEnd ℂ)) = (blockG Γ).map (starRingEnd ℂ) := by
  have e : (omBlock (Γ.map (starRingEnd ℂ)))ᵀ⁻¹ = ((omBlock Γ)ᵀ⁻¹).map (starRingEnd ℂ) := by
    show ((omBlock Γ)ᵀᴴᵀ)⁻¹ = ((omBlock Γ)ᵀ⁻¹)ᴴᵀ
    rw [← Matrix.transpose_nonsing_inv, ← Matrix.conjTranspose_nonsing_inv]
  unfold blockG
  rw [e, ← Matrix.submatrix_map, Matrix.fromBlocks_map]
  simp only [Matrix.map_zero _ (map_zero (starRingEnd ℂ))]
  rfl

theorem blockG_change {Γ Γ' Rz Rz' : Matrix (Fin (p + q)) (Fin (p + q)) ℂ} (hΓ : Γ.PosDef) (hΓ' : Γ'.PosDef)
    (bR : IsBlockDiag p Rz) (bR' : IsBlockDiag p Rz') (e : Rz' * Rz = 1)
    (eo : omBlock Γ' = (omBlock Rz')ᵀᴴ * omBlock Γ * (omBlock Rz')ᵀ)
    (ew : wBlock Γ' = (wBlock Rz)ᴴ * wBlock Γ * wBlock Rz) : blockG Γ' = Rzᴴ * blockG Γ * Rz := by
  have b := (PositivityTheory.Xgp.t_c_bm_exists_blockpos p q Γ hΓ).1
  have b' := (PositivityTheory.Xgp.t_c_bm_exists_blockpos p q Γ' hΓ').1
  have c := isBlockDiag_conjTranspose bR
  have e1 : (omBlock Rz')⁻¹ = omBlock Rz :=
    Matrix.inv_eq_right_inv (by rw [← (blocks_mul bR' bR).1, e, omBlock_one])
  refine b'.ext_blocks ((c.mul b).mul bR) ?_ ?_
  · rw [(blocks_mul (c.mul b) bR).1, (blocks_mul c b).1, omBlock_blockG, omBlock_blockG, eo, Matrix.transpose_mul,
      Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_inv_rev, Matrix.mul_inv_rev, e1]
    have : (omBlock Rz')ᵀᴴᵀ⁻¹ = omBlock Rzᴴ := by
      show ((omBlock Rz')ᴴ)⁻¹ = (omBlock Rz)ᴴ
      rw [← Matrix.conjTranspose_nonsing_inv, e1]
    rw [this]
  · rw [(blocks_mul (c.mul b) bR).2, (blocks_mul c b).2, wBlock_blockG, wBlock_blockG, ew]
    rfl

end Lin

theorem frame_coeff {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {V : Type}
    [AddCommGroup V] [Module Ω V] {L : Lat ξ V} {r : ℕ} {b : Fin r → V} {S : Matrix (Fin r) (Fin r) Ω} {q : Cpt ξ}
    (h : L.IsFrameAt b q) (h' : L.IsFrameAt (colFrame b S) q) (a c : Fin r) : S a c ∈ regAt ξ q := by
  have hm : colFrame b S c ∈ Submodule.span (regAt ξ q) (Set.range b) := by
    rw [← h.2, h'.2]; exact Submodule.subset_span ⟨c, rfl⟩
  obtain ⟨t, ht⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hm
  have h0 : ∑ i, (S i c - t i) • b i = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib]
    exact sub_eq_zero.2 ht.symm
  have := sub_eq_zero.1 (Fintype.linearIndependent_iff.1 h.1 _ h0 a)
  rw [this]
  exact (t a).2

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {S : Finset ℕ}
  {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {M : FlagModel y (CMType H) (D.p + D.q) D.p} {𝔐 : HodgeCpt Y S M.x}

theorem frames_rel (tie : FlagTie M 𝔐) {F F' : FrameData ι (CMType H) (D.p + D.q) M.Ω M.blk} (hF : M.IsFrame F)
    (hF' : M.IsFrame F') (τ : CMType H) :
    IsBlockDiag D.p ((F.T τ)⁻¹ * F'.T τ) ∧
    tie.wFrame F' τ = colFrame (tie.wFrame F τ) (wBlock ((F.T τ)⁻¹ * F'.T τ)) ∧
    tie.omFrame F' τ = colFrame (tie.omFrame F τ) (omBlock ((F.T τ)⁻¹ * F'.T τ)) := by
  have hu : IsUnit (F.T τ).det := (hF.1 τ).2.isUnit
  have bR : IsBlockDiag D.p ((F.T τ)⁻¹ * F'.T τ) := ((hF.1 τ).1.inv hu).mul (hF'.1 τ).1
  have e := blocks_mul (hF.1 τ).1 bR
  rw [Matrix.mul_nonsing_inv_cancel_left _ _ hu] at e
  refine ⟨bR, ?_, ?_⟩
  · unfold FlagTie.wFrame
    rw [e.2, colFrame_mul]
  · unfold FlagTie.omFrame
    rw [e.1, colFrame_mul]

theorem change_reg (tie : FlagTie M 𝔐) {F F' : FrameData ι (CMType H) (D.p + D.q) M.Ω M.blk} (hF : M.IsFrame F)
    (hF' : M.IsFrame F') (τ : CMType H) {z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X} {w : (Σ k, baseIdx ι M.blk k) → ℂ}
    (hw : CoordsAt 𝔐.ξ M.x z w) (gd : M.GoodAt F (mCoordIdeal w)) (gd' : M.GoodAt F' (mCoordIdeal w)) :
    ∃ Rz : Matrix (Fin (D.p + D.q)) (Fin (D.p + D.q)) ℂ, ∀ a b, GlobalTheory.CompanionTheory.Ar.ValAt 𝔐.ξ z (((F.T τ)⁻¹ * F'.T τ) a b) (Rz a b) := by
  obtain ⟨bR, ew, eo⟩ := frames_rel tie hF hF' τ
  obtain ⟨f1, f2⟩ := tie.frames_centre hw hF gd τ
  obtain ⟨f1', f2'⟩ := tie.frames_centre hw hF' gd' τ
  rw [ew] at f1'
  rw [eo] at f2'
  have key : ∀ a b, ((F.T τ)⁻¹ * F'.T τ) a b ∈ regAt 𝔐.ξ ⟨centre z, 𝔐.all _⟩ := by
    intro a b
    obtain ⟨a, rfl⟩ := (blockEquiv D.p D.q).surjective a
    obtain ⟨b, rfl⟩ := (blockEquiv D.p D.q).surjective b
    have e := congrFun (congrFun bR.eq_fromBlocks a) b
    rw [Matrix.submatrix_apply] at e
    rw [e]
    rcases a with a | a <;> rcases b with b | b
    exacts [frame_coeff f2 f2' a b, zero_mem _, zero_mem _, frame_coeff f1 f1' a b]
  choose s hs using key
  exact ⟨Matrix.of fun a b => (Scheme.stalkClosedPointTo z).hom (s a b), fun a b => ⟨𝔐.all _, s a b, hs a b, rfl⟩⟩

theorem dual_change (tie : FlagTie M 𝔐) {F F' : FrameData ι (CMType H) (D.p + D.q) M.Ω M.blk} (hF : M.IsFrame F)
    (hF' : M.IsFrame F') (τ : CMType H)
    (hv : ∀ a b, tie.omFrame F τ a (dualFam tie F τ b) = if a = b then 1 else 0)
    (hv' : ∀ a b, tie.omFrame F' τ a (dualFam tie F' τ b) = if a = b then 1 else 0) (m : Fin D.q) :
    dualFam tie F' τ m = colFrame (dualFam tie F τ) (omBlock ((F'.T τ)⁻¹ * F.T τ))ᵀ m := by
  obtain ⟨bR, -, eo⟩ := frames_rel tie hF hF' τ
  obtain ⟨bR', -, -⟩ := frames_rel tie hF' hF τ
  have hu : IsUnit (F.T τ).det := (hF.1 τ).2.isUnit
  have hu' : IsUnit (F'.T τ).det := (hF'.1 τ).2.isUnit
  have e1 : omBlock ((F'.T τ)⁻¹ * F.T τ) * omBlock ((F.T τ)⁻¹ * F'.T τ) = 1 := by
    rw [← (blocks_mul bR' bR).1, Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hu,
      Matrix.nonsing_inv_mul _ hu', omBlock_one]
  have e2 : (omBlock ((F.T τ)⁻¹ * F'.T τ))ᵀ⁻¹ = (omBlock ((F'.T τ)⁻¹ * F.T τ))ᵀ := by
    rw [← Matrix.transpose_nonsing_inv, Matrix.inv_eq_left_inv e1]
  have e3 := fun k => colFrame_dual _ _ hv (omBlock ((F.T τ)⁻¹ * F'.T τ)) (Matrix.isUnit_det_of_left_inverse e1) k m
  rw [e2, ← eo] at e3
  rw [← sub_eq_zero]
  generalize hd : dualFam tie F' τ m - colFrame (dualFam tie F τ) (omBlock ((F'.T τ)⁻¹ * F.T τ))ᵀ m = d
  have h1 : ∀ k, tie.omFrame F' τ k d = 0 := fun k => by rw [← hd, map_sub, e3, hv', sub_self]
  have e4 : (tie.eO τ : Fin D.q → _) = colFrame (tie.omFrame F' τ) (omBlock (F'.T τ)⁻¹) := by
    unfold FlagTie.omFrame
    rw [← colFrame_mul, ← (blocks_mul (hF'.1 τ).1 ((hF'.1 τ).1.inv hu')).1, Matrix.mul_nonsing_inv _ hu',
      omBlock_one, colFrame_one]
  have h2 : ∀ k, tie.eO τ k d = 0 := fun k => by
    rw [e4]; simp [colFrame, h1]
  refine (Module.forall_dual_apply_eq_zero_iff M.Ω d).1 fun ψ => ?_
  rw [← (tie.eO τ).sum_repr ψ, LinearMap.sum_apply]
  exact Finset.sum_eq_zero fun k _ => by rw [LinearMap.smul_apply, h2, smul_zero]

theorem gramAt_sub {X : Scheme.{0}} {Ω : Type} [Field Ω] {G : Over X} [GrpObj G]
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} {Li : Type} [AddCommGroup Li] [Module Ω Li] {M : LieModel G ξ Li}
    {L : LB G.left} {z : Spec (CommRingCat.of ℂ) ⟶ X} {r s : ℕ} {b : Fin r → Li} {Γ : Matrix (Fin r) (Fin r) ℂ}
    (h : M.GramAt L z b Γ) (e : Fin s → Fin r) : M.GramAt L z (fun a => b (e a)) (Γ.submatrix e e) :=
  let ⟨v, hv, h'⟩ := h
  ⟨fun a => v (e a), fun a => hv (e a), fun a a' => h' (e a) (e a')⟩

theorem gb_om (tie : FlagTie M 𝔐) (F : FrameData ι (CMType H) (D.p + D.q) M.Ω M.blk) (τ : CMType H) (a : Fin D.q) :
    gb tie F τ (omEmb D.p D.q a) = dualFam tie F τ a := by
  simp [gb, gbS, ← blockEquiv_inl]

theorem gb_w (tie : FlagTie M 𝔐) (F : FrameData ι (CMType H) (D.p + D.q) M.Ω M.blk) (τ : CMType H) (a : Fin D.p) :
    gb tie F τ (wEmb D.p D.q a) = tie.wFrame F τ a := by
  simp [gb, gbS, ← blockEquiv_inr]

theorem dualFam_spec (tie : FlagTie M 𝔐) {F : FrameData ι (CMType H) (D.p + D.q) M.Ω M.blk} (hF : M.IsFrame F)
    (τ : CMType H) {z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X} {w : (Σ k, baseIdx ι M.blk k) → ℂ}
    (hw : CoordsAt 𝔐.ξ M.x z w) (gd : M.GoodAt F (mCoordIdeal w)) :
    ∀ a b, tie.omFrame F τ a (dualFam tie F τ b) = if a = b then 1 else 0 := by
  have h := (omBundle_dualFrame 𝔐 τ _ (tie.frames_centre hw hF gd τ).2).1
  unfold dualFam
  rw [dif_pos h]
  exact h.choose_spec

def Gr (tie : FlagTie M 𝔐) (F : FrameData ι (CMType H) (D.p + D.q) M.Ω M.blk) (τ : CMType H)
    (w : (Σ k, baseIdx ι M.blk k) → ℂ) (G : Matrix (Fin (D.p + D.q)) (Fin (D.p + D.q)) ℂ) : Prop :=
  M.IsFrame F ∧ M.GoodAt F (mCoordIdeal w) ∧ ∃ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X)
    (Γ : Matrix (Fin (D.p + D.q)) (Fin (D.p + D.q)) ℂ), CoordsAt 𝔐.ξ M.x z w ∧ 𝔐.Interior z ∧
      𝔐.M.GramAt 𝔐.t.PP.L z (gb tie F τ) Γ ∧ Γ.PosDef ∧ G = blockG Γ

theorem gr_good (tie : FlagTie M 𝔐) (F τ w G) (h : Gr tie F τ w G) : M.IsFrame F ∧ w ∈ mcPts (mCoordIdeal M.x) ∧
    M.GoodAt F (mCoordIdeal w) ∧ IsBlockDiag D.p G ∧ G.PosDef := by
  obtain ⟨hF, gd, z, Γ, hw, -, -, hp, rfl⟩ := h
  exact ⟨hF, (GlobalTheory.T.complex_points_iff_centres 𝔐.X M.Ω 𝔐.ξ _ _ M.x 𝔐.tie w).2 ⟨z, 𝔐.all _, hw⟩, gd,
    PositivityTheory.Xgp.t_c_bm_exists_blockpos _ _ Γ hp⟩

theorem gr_tor (tie : FlagTie M 𝔐) (F τ w G) (cv : NonPluckerBlocks M.blk → ℂ) (hc : ∀ k, cv k ≠ 0) (h : Gr tie F τ w G) :
    Gr tie F τ (torusSmul cv w) G := by
  obtain ⟨hF, gd, z, Γ, hw, h'⟩ := h
  have hz' : CoordsAt 𝔐.ξ M.x z (torusSmul cv w) :=
    (((GlobalTheory.T.local_ring_points_existsUnique 𝔐.X M.Ω 𝔐.ξ _ _ M.x 𝔐.tie ℂ).2.2 z w (𝔐.all _) hw).2 _).2
      ⟨fun k => Units.mk0 (cv k) (hc k), rfl⟩
  refine ⟨hF, ?_, z, Γ, hz', h'⟩
  rwa [← ptIdeal_centre hz' (𝔐.all _), ptIdeal_centre hw]

theorem gr_conj (tie : FlagTie M 𝔐) (F τ w G) (h : Gr tie F τ w G) :
    Gr tie F τ (conjVec w) (G.map (starRingEnd ℂ)) := by
  obtain ⟨hF, gd, z, Γ, hw, hi, hΓ, hp, rfl⟩ := h
  have hcc := GlobalTheory.T.conjugate_point_same_centre 𝔐.X M.Ω 𝔐.ξ _ _ M.x z w
  refine ⟨hF, ?_, _, _, hcc.2 hw, ?_, GlobalTheory.T.gramAt_conj_point_map_conj E H D l Xo c Y S M.Ω _ _ M.x 𝔐 z _ _ _ hΓ, ?_,
    (blockG_conj Γ).symm⟩
  · have e : mCoordIdeal (conjVec w) = mCoordIdeal w :=
      (ptIdeal_centre (hcc.2 hw) (𝔐.all _)).symm.trans
        ((congrArg (ptIdeal 𝔐.ξ M.x) (Subtype.ext hcc.1)).trans (ptIdeal_centre hw (𝔐.all _)))
    rwa [e]
  · show centre _ ∈ _
    rw [hcc.1]
    exact hi
  · show (Γᴴᵀ).PosDef
    rw [hp.1.eq]
    exact hp.transpose

theorem gr_comp (tie : FlagTie M 𝔐) (F F' τ w G G') (h : Gr tie F τ w G) (h' : Gr tie F' τ w G') :
    ∃ Rz : Matrix (Fin (D.p + D.q)) (Fin (D.p + D.q)) ℂ,
      (∀ a b, IsValueAt M.x (((F.T τ)⁻¹ * F'.T τ) a b) w (Rz a b)) ∧ Rz.det ≠ 0 ∧ G' = Rzᴴ * G * Rz := by
  have hm := (gr_good tie F τ w G h).2.1
  obtain ⟨hF, gd, z, Γ, hw, hi, hΓ, hp, rfl⟩ := h
  obtain ⟨hF', gd', z', Γ', hw', -, hΓ', hp', rfl⟩ := h'
  have tp := GlobalTheory.T.local_ring_points_existsUnique 𝔐.X M.Ω 𝔐.ξ _ _ M.x 𝔐.tie ℂ
  obtain rfl : z = z' := (tp.1 w hw.1 (tp.2.2 z w (𝔐.all _) hw).1).unique ⟨𝔐.all _, hw⟩ ⟨𝔐.all _, hw'⟩
  have hpol := GlobalTheory.T.interior_point_polarised E H D l Xo c Y S M.Ω _ _ M.x 𝔐 z hi
  obtain ⟨Rz, hR⟩ := change_reg tie hF hF' τ hw gd gd'
  obtain ⟨Rz', hR'⟩ := change_reg tie hF' hF τ hw gd' gd
  have tv := GlobalTheory.T.valAt_iff_value_at 𝔐.X M.Ω 𝔐.ξ _ _ M.x 𝔐.tie z w (𝔐.all _) hw
  obtain ⟨bR, ew, -⟩ := frames_rel tie hF hF' τ
  obtain ⟨bR', -, -⟩ := frames_rel tie hF' hF τ
  let RA : Matrix (Fin (D.p + D.q)) (Fin (D.p + D.q)) (CPts.regRing M.x w) :=
    Matrix.of fun a b => ⟨_, _, (tv _ _).1 (hR a b)⟩
  let RA' : Matrix (Fin (D.p + D.q)) (Fin (D.p + D.q)) (CPts.regRing M.x w) :=
    Matrix.of fun a b => ⟨_, _, (tv _ _).1 (hR' a b)⟩
  have e1 : RA.map (CPts.regRing M.x w).subtype = (F.T τ)⁻¹ * F'.T τ := by ext a b; rfl
  have e1' : RA'.map (CPts.regRing M.x w).subtype = (F'.T τ)⁻¹ * F.T τ := by ext a b; rfl
  have e2 : RA.map (CPts.regVal hm) = Rz := by ext a b; exact valAt_eq hm ((tv _ _).1 (hR a b))
  have e2' : RA'.map (CPts.regVal hm) = Rz' := by ext a b; exact valAt_eq hm ((tv _ _).1 (hR' a b))
  have b1 : IsBlockDiag D.p Rz := by
    have : IsBlockDiag D.p RA := fun a b hab => Subtype.ext (bR a b hab)
    exact e2 ▸ this.map _
  have b1' : IsBlockDiag D.p Rz' := by
    have : IsBlockDiag D.p RA' := fun a b hab => Subtype.ext (bR' a b hab)
    exact e2' ▸ this.map _
  have e3 : Rz' * Rz = 1 := by
    have : RA' * RA = 1 := by
      apply Matrix.map_injective (CPts.regRing M.x w).subtype_injective
      show (RA' * RA).map _ = Matrix.map 1 _
      rw [Matrix.map_mul, e1, e1', Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_assoc,
        Matrix.mul_nonsing_inv_cancel_left _ _ (hF.1 τ).2.isUnit, Matrix.nonsing_inv_mul _ (hF'.1 τ).2.isUnit]
    rw [← e2, ← e2', ← Matrix.map_mul, this, Matrix.map_one _ (map_zero _) (map_one _)]
  refine ⟨Rz, fun a b => (tv _ _).1 (hR a b), (Matrix.isUnit_det_of_left_inverse e3).ne_zero,
    blockG_change hp hp' b1 b1' e3 ?_ ?_⟩
  · refine GlobalTheory.T.gram_matrix_two_frames E H D l Xo c Y S M.Ω _ _ M.x 𝔐 z _ _ _ _ _ (omBlock ((F'.T τ)⁻¹ * F.T τ))ᵀ _ hpol
      (gramAt_sub hΓ (omEmb D.p D.q)) (gramAt_sub hΓ' (omEmb D.p D.q)) (fun m => ?_) fun a b => hR' _ _
    simp only [gb_om]
    rw [dual_change tie hF hF' τ (dualFam_spec tie hF τ hw gd) (dualFam_spec tie hF' τ hw gd') m]
    simp [colFrame]
  · refine GlobalTheory.T.gram_matrix_two_frames E H D l Xo c Y S M.Ω _ _ M.x 𝔐 z _ _ _ _ _ (wBlock ((F.T τ)⁻¹ * F'.T τ)) _ hpol
      (gramAt_sub hΓ (wEmb D.p D.q)) (gramAt_sub hΓ' (wEmb D.p D.q)) (fun m => ?_) fun a b => hR _ _
    simp only [gb_w]
    exact congrFun ew m

end PositivityTheory.Xgp.c_bm_exists_hom

theorem PositivityTheory.Xgp.t_c_bm_exists_hom : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (M : FlagModel y (CMType H) (D.p + D.q) D.p) (𝔐 : HodgeCpt Y S M.x) (tie : FlagTie M 𝔐), ∀ (n : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (s : Rb.X → Rb.X → ℂ), (∀ (x : Rb.X) (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X), CoordsAt 𝔐.ξ M.x z (Rb.lift x x) → (x ∉ bdry s ↔ 𝔐.Interior z)) → ∀ (q : ℕ) (O : Fin q → Set Rb.X) (F : Fin q → FrameData ι (CMType H) (D.p + D.q) M.Ω M.blk), (∀ x, ∃ l, x ∈ O l) → (∀ l, M.IsFrame (F l)) → (∀ l, ∀ x ∈ O l, M.GoodAt (F l) (mCoordIdeal (Rb.lift x x))) → ∃ hom : CMType H × Fin (D.p + D.q) → HermLine ι, (∀ p, (hom p).a = M.dy p) ∧ (∀ l, ∀ x ∈ O l \ bdry s, ∀ p, M.IsInducedAt (F l) (Rb.lift x x) p (blockG (baseGram tie (F l) p.1 Rb x)) (hom p)) ∧ ∀ p, ∀ z ∈ mcPts (mCoordIdeal y), ∀ x, x ∉ bdry s → SameOrbit (basePart M.blk z) (Rb.lift x x) → (hom p).h (fun q => starRingEnd ℂ (z q)) = (hom p).h z := by
  intro E _ _ _ H D Xo l c Y S K _ ι _ Φ _ y M 𝔐 tie n Rb s hInt q O F _ hF hgd
  choose hom h1 h2 h3 using PositivityTheory.Xgp.c_bm_exists_hom.exists_hom (PositivityTheory.Xgp.c_bm_exists_hom.gr_good tie)
    (PositivityTheory.Xgp.c_bm_exists_hom.gr_tor tie) (PositivityTheory.Xgp.c_bm_exists_hom.gr_conj tie)
    (PositivityTheory.Xgp.c_bm_exists_hom.gr_comp tie)
  refine ⟨hom, h1, fun i x hx p => h2 p _ _ _ ?_, fun p z _ _ _ _ => h3 p z⟩
  obtain ⟨z, -, hz⟩ := (GlobalTheory.T.complex_points_iff_centres 𝔐.X M.Ω 𝔐.ξ _ _ M.x 𝔐.tie _).1 (Rb.mem x x (Rb.mem_U x))
  have hi := (hInt x z hz).1 hx.2
  obtain ⟨g1, g2, -⟩ := PositivityTheory.Xgp.t_c_bm_exists_gram E H D Xo l c Y S K ι Φ y M 𝔐 tie (F i) (hF i) p.1 _ z hz hi
    (hgd i x hx.1)
  exact ⟨hF i, hgd i x hx.1, z, _, hz, hi, g1, g2, rfl⟩
