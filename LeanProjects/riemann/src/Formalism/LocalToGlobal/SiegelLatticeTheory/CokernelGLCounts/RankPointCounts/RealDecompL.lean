import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RealDecompW
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.ConcreteLevelAdelicSubset
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem

noncomputable section

open Matrix NumberField
open scoped ComplexConjugate

namespace Formalism.L2.SG.Pf.RowForm.RealDecompL

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Mat

variable {r : ℕ}

private theorem snoc_comp {α β : Type*} (φ : α → β) (e : Fin r → α) (z : α) (a : Fin (r + 1)) :
    Fin.snoc (α := fun _ => β) (fun i => φ (e i)) (φ z) a = φ (Fin.snoc (α := fun _ => α) e z a) := by
  induction a using Fin.lastCases with
  | last => simp
  | cast i => simp

private def sgnP (K : Type*) [CommRing K] (r l : ℕ) (h : l ≤ r + 1) : K :=
  ∏ b : Fin l, (-1 : K) ^ (r - (Fin.castLE h b).val)

private theorem localSign_sq (K : Type*) [CommRing K] (r l : ℕ) (h : l ≤ r + 1) : sgnP K r l h * sgnP K r l h = 1 := by
  unfold sgnP
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_eq_one fun b _ => by rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]

private theorem sgnP_map {K K' : Type*} [CommRing K] [CommRing K'] (ψ : K →+* K') (r l : ℕ) (h : l ≤ r + 1) :
    ψ (sgnP K r l h) = sgnP K' r l h := by
  simp only [sgnP, map_prod, map_pow, map_neg, map_one]

private theorem sub_zhatOM {K : Type*} [CommRing K] (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) K) {l : ℕ} (h : l ≤ r + 1) :
    (ZhatOM Z).submatrix (Fin.castLE h) (Fin.castLE h) =
      Z.submatrix (Fin.castLE h) (Fin.castLE h) * diagonal fun b : Fin l => (-1 : K) ^ (r - (Fin.castLE h b).val) := by
  ext a b
  simp only [Matrix.submatrix_apply, ZhatOM, Matrix.mul_diagonal]
  ring

private theorem lead_zhatOM {E : Type} [Field E] [NumberField E] [StarRing E]
    (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) {l : ℕ} (h : l ≤ r + 1) :
    leadMinorE (ZhatOM Z) l = leadMinorE Z l * sgnP E r l h := by
  simp only [leadMinorE, dif_pos h, sub_zhatOM Z h, Matrix.det_mul, Matrix.det_diagonal, sgnP]

private theorem dl_zhatO (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) {l : ℕ} (h : l ≤ r + 1) :
    RealObj.Dl (RealObj.ZhatO Z) l = RealObj.Dl Z l * sgnP ℂ r l h := by
  have e : RealObj.ZhatO Z = ZhatOM Z := rfl
  simp only [RealObj.Dl, dif_pos h, e, sub_zhatOM Z h, Matrix.det_mul, Matrix.det_diagonal, sgnP]

private theorem dl_map {E : Type} [Field E] [NumberField E] [StarRing E] (ψ : E →+* ℂ)
    (A : Matrix (Fin (r + 1)) (Fin (r + 1)) E) {l : ℕ} (h : l ≤ r + 1) :
    RealObj.Dl (A.map ψ) l = ψ (leadMinorE A l) := by
  simp only [RealObj.Dl, leadMinorE, dif_pos h, Matrix.submatrix_map, RingHom.map_det, RingHom.mapMatrix_apply]

private theorem famSc_one' {n : ℕ} (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) : RealObj.famSc 1 e z = RealObj.fam e z := by
  funext a
  simp only [RealObj.famSc, Complex.ofReal_one, one_pow, inv_one, one_smul]

end Mat

section Uni

variable {r : ℕ}

private def sgn (r : ℕ) : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ := Matrix.diagonal fun b => (-1 : ℂ) ^ (r - b.1)

private theorem sgn_sq : sgn r * sgn r = 1 := by
  simp only [sgn, Matrix.diagonal_mul_diagonal]
  rw [← Matrix.diagonal_one]
  congr 1
  funext b
  rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]

private theorem zhatO_eq (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) : RealObj.ZhatO Z = Z * sgn r := by
  ext a b
  simp only [RealObj.ZhatO, sgn, Matrix.mul_diagonal]
  ring

private theorem isLoUni_map {K : Type*} [Field K] (ψ : K →+* ℂ) {L : Matrix (Fin (r + 1)) (Fin (r + 1)) K}
    (h : IsLoUni L) : IsLoUni (L.map ψ) := by
  intro i j
  exact ⟨fun hij => by rw [Matrix.map_apply, (h i j).1 hij, map_zero],
    fun hij => by rw [Matrix.map_apply, (h i j).2 hij, map_one]⟩

private theorem isLoUni_star {L : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (h : IsLoUni L) : IsLoUni (L.map star) := by
  intro i j
  exact ⟨fun hij => by rw [Matrix.map_apply, (h i j).1 hij, star_zero],
    fun hij => by rw [Matrix.map_apply, (h i j).2 hij, star_one]⟩

private theorem isLoUni_sgnT {U : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (h : IsUpUni U) :
    IsLoUni (sgn r * U * sgn r)ᵀ := by
  intro i j
  simp only [sgn, Matrix.transpose_apply, Matrix.diagonal_mul, Matrix.mul_diagonal]
  refine ⟨fun hij => by rw [(h j i).1 hij, mul_zero, zero_mul], fun hij => ?_⟩
  subst hij
  rw [(h i i).2 rfl, mul_one, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]

private theorem det_lo {K : Type*} [Field K] {L : Matrix (Fin (r + 1)) (Fin (r + 1)) K} (h : IsLoUni L) :
    L.det = 1 := by
  rw [Matrix.det_of_lowerTriangular L (fun i j hij => (h i j).1 (OrderDual.toDual_lt_toDual.mp hij))]
  exact Finset.prod_eq_one fun i _ => (h i i).2 rfl

private theorem det_up {K : Type*} [Field K] {U : Matrix (Fin (r + 1)) (Fin (r + 1)) K} (h : IsUpUni U) :
    U.det = 1 := by
  rw [Matrix.det_of_upperTriangular (fun i j hij => (h i j).1 hij)]
  exact Finset.prod_eq_one fun i _ => (h i i).2 rfl

private theorem isUpUni_map {K : Type*} [Field K] (ψ : K →+* ℂ) {U : Matrix (Fin (r + 1)) (Fin (r + 1)) K}
    (h : IsUpUni U) : IsUpUni (U.map ψ) := by
  intro i j
  exact ⟨fun hij => by rw [Matrix.map_apply, (h i j).1 hij, map_zero],
    fun hij => by rw [Matrix.map_apply, (h i j).2 hij, map_one]⟩

private theorem cancel {L A B U : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (hL : L.det ≠ 0) (hU : U.det ≠ 0)
    (h : L * A * U = L * B * U) : A = B := by
  have hLu : IsUnit L := (Matrix.isUnit_iff_isUnit_det L).mpr (isUnit_iff_ne_zero.mpr hL)
  have hUu : IsUnit U := (Matrix.isUnit_iff_isUnit_det U).mpr (isUnit_iff_ne_zero.mpr hU)
  exact hLu.mul_left_cancel (hUu.mul_right_cancel h)

end Uni

section Glob

variable {D : D7} (X : HidaSetting.HidaSetting D)

private theorem zx_eq (u u' : D.what₂.Word) (δ : X.B.I.Ginf) (v : InfinitePlace X.B.I.F) :
    RealObj.ZX X u u' 1 δ v = RealObj.Zhat (X.B.I.ε v)
      (RealObj.fam (fun a => HidaSetting.rv X.B.I v (X.eR a)) (HidaSetting.rv X.B.I v (X.zR u)))
      (RealObj.fam (fun a => HidaSetting.rv X.B.I v (X.eR a)) (HidaSetting.rv X.B.I v (X.zR u'))) (uMat (δ v)) := by
  simp only [RealObj.ZX, RealObj.frm, famSc_one']

theorem ptRep_of_cell (u u' : D.what₂.Word) (γ : X.B.I.Ginf) (w : Point D.host.E (D.R.rS + 1))
    (L U : PairVal.MatR D) (hLo : IsLoUni L) (hUp : IsUpUni U)
    (hZ : ∀ v, RealObj.ZhatO (RealObj.ZX X u u' 1 γ v) = (L * ptMat w * U).map (fun x => X.B.I.φ v (X.ιE.symm x))) :
    ∃ s ∈ X.SinfU u, ∃ s' ∈ X.SinfU u', RealObj.IsPtRep X u u' w (s * γ * s'⁻¹) := by
  let ψ : InfinitePlace X.B.I.F → D.host.E →+* ℂ := fun v => (X.B.I.φ v).comp X.ιE.symm.toRingHom
  let P : InfinitePlace X.B.I.F → Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ := fun v => (L.map (ψ v)).map star
  let P' : InfinitePlace X.B.I.F → Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ :=
    fun v => (sgn D.R.rS * U.map (ψ v) * sgn D.R.rS)ᵀ
  have hzz : ∀ (w' : D.what₂.Word) v,
      HidaSetting.hJ (X.B.I.ε v) (HidaSetting.rv X.B.I v (X.zR w')) (HidaSetting.rv X.B.I v (X.zR w')) ≠ 0 := by
    intro w' v
    rw [(RealObj.HermitianSumRootCoordinateFrames.FrameAtV_holds D X w' v).2.2.2.2.2.1]
    exact neg_ne_zero.2 (Complex.ofReal_ne_zero.2 (RealObj.HermitianSumRootCoordinateFrames.FrameAtV_holds D X w' v).2.2.2.2.2.2)
  have hs : ∀ v, ∃ s : Formalism.REAL.UJ (X.B.I.ε v),
      HidaSetting.InN (X.B.I.ε v) (fun a => HidaSetting.rv X.B.I v (X.eR a)) (HidaSetting.rv X.B.I v (X.zR u)) (uMat s) ∧
      ∀ a, uMat s *ᵥ RealObj.fam (fun a => HidaSetting.rv X.B.I v (X.eR a)) (HidaSetting.rv X.B.I v (X.zR u)) a =
        ∑ c, P v a c • RealObj.fam (fun a => HidaSetting.rv X.B.I v (X.eR a)) (HidaSetting.rv X.B.I v (X.zR u)) c := fun v =>
    RealObj.ThreeBlockFrameInverses.NRealize_holds X.B.I.n D.R.rS (X.B.I.ε v) (fun a => HidaSetting.rv X.B.I v (X.eR a))
      (fun a => HidaSetting.rv X.B.I v (X.fR a))
      (HidaSetting.rv X.B.I v (X.zR u)) (RealObj.HermitianSumRootCoordinateFrames.FrameAtV_holds D X u v).1 (RealObj.HermitianSumRootCoordinateFrames.FrameAtV_holds D X u v).2.1
      (RealObj.HermitianSumRootCoordinateFrames.FrameAtV_holds D X u v).2.2.1 (RealObj.HermitianSumRootCoordinateFrames.FrameAtV_holds D X u v).2.2.2.2.1 (hzz u v) (P v)
      (isLoUni_star (isLoUni_map _ hLo))
  have hs' : ∀ v, ∃ s : Formalism.REAL.UJ (X.B.I.ε v),
      HidaSetting.InN (X.B.I.ε v) (fun a => HidaSetting.rv X.B.I v (X.eR a)) (HidaSetting.rv X.B.I v (X.zR u')) (uMat s) ∧
      ∀ a, uMat s *ᵥ RealObj.fam (fun a => HidaSetting.rv X.B.I v (X.eR a)) (HidaSetting.rv X.B.I v (X.zR u')) a =
        ∑ c, P' v a c • RealObj.fam (fun a => HidaSetting.rv X.B.I v (X.eR a)) (HidaSetting.rv X.B.I v (X.zR u')) c := fun v =>
    RealObj.ThreeBlockFrameInverses.NRealize_holds X.B.I.n D.R.rS (X.B.I.ε v) (fun a => HidaSetting.rv X.B.I v (X.eR a))
      (fun a => HidaSetting.rv X.B.I v (X.fR a))
      (HidaSetting.rv X.B.I v (X.zR u')) (RealObj.HermitianSumRootCoordinateFrames.FrameAtV_holds D X u' v).1
      (RealObj.HermitianSumRootCoordinateFrames.FrameAtV_holds D X u' v).2.1
      (RealObj.HermitianSumRootCoordinateFrames.FrameAtV_holds D X u' v).2.2.1 (RealObj.HermitianSumRootCoordinateFrames.FrameAtV_holds D X u' v).2.2.2.2.1 (hzz u' v) (P' v)
      (isLoUni_sgnT (isUpUni_map _ hUp))
  choose s hsN hsP using hs
  choose s' hs'N hs'P using hs'
  have hsS : s ∈ X.SinfU u := fun v => (hsN v).1
  have hs'S : s' ∈ X.SinfU u' := fun v => (hs'N v).1
  refine ⟨s, hsS, s', hs'S, fun v => ?_⟩
  have hg : s⁻¹ * (s * γ * s'⁻¹) * s' = γ := by group
  have h4 := RealObj.HermitianSumRootCoordinateFrames.ZhatNAct_holds _ _ (X.B.I.ε v)
    (RealObj.fam (fun a => HidaSetting.rv X.B.I v (X.eR a)) (HidaSetting.rv X.B.I v (X.zR u)))
    (RealObj.fam (fun a => HidaSetting.rv X.B.I v (X.eR a)) (HidaSetting.rv X.B.I v (X.zR u'))) (uMat (s v)) (uMat (s⁻¹ v))
    (uMat (s' v)) (uMat ((s * γ * s'⁻¹) v)) (P v) (P' v) (RealObj.InfCut.uMat_inv_mul' (s v))
    (RealObj.HermitianBlockSpans.hJ_map _ (s v).2) (hsP v) (hs'P v)
  have hγv : uMat (s⁻¹ v) * uMat ((s * γ * s'⁻¹) v) * uMat (s' v) = uMat (γ v) := by
    calc uMat (s⁻¹ v) * uMat ((s * γ * s'⁻¹) v) * uMat (s' v)
        = uMat ((s⁻¹ * (s * γ * s'⁻¹) * s') v) := by
          simp only [uMat, Pi.mul_apply, Subgroup.coe_mul, Units.val_mul]
      _ = uMat (γ v) := by rw [hg]
  rw [hγv, ← zx_eq, ← zx_eq] at h4
  have h5 : RealObj.ZhatO (RealObj.ZX X u u' 1 γ v) = (L * ptMat w * U).map (ψ v) := hZ v
  rw [Matrix.map_mul, Matrix.map_mul, zhatO_eq, h4] at h5
  have hPs : (P v).map star = L.map (ψ v) := by
    ext i j
    simp only [P, Matrix.map_apply, star_star]
  have hPt' : (P' v)ᵀ = sgn D.R.rS * U.map (ψ v) * sgn D.R.rS := Matrix.transpose_transpose _
  rw [hPs, hPt'] at h5
  have h6 : L.map (ψ v) * RealObj.ZhatO (RealObj.ZX X u u' 1 (s * γ * s'⁻¹) v) * U.map (ψ v) =
      L.map (ψ v) * RealObj.ptC X v w * U.map (ψ v) := by
    refine Eq.trans ?_ h5
    rw [zhatO_eq]
    simp only [Matrix.mul_assoc, sgn_sq, Matrix.mul_one]
  exact cancel (by rw [det_lo (isLoUni_map _ hLo)]; exact one_ne_zero)
    (by rw [det_up (isUpUni_map _ hUp)]; exact one_ne_zero) h6

end Glob

section Rat

variable {D : D7} (X : HidaSetting.HidaSetting D) (u u' : D.what₂.Word)
  {what₂ rows' : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

private theorem frame_fvec (t : TermOp.GTerm X u u' (X.Fu u) (X.Fu u') what₂ rows') (b : Fin (D.R.rS + 1)) :
    t.frame.fl.fvec b = t.lin ((X.Fu u').fvec b) := by
  have hiso : t.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t.rep.2.2.1
  unfold TermOp.GTerm.frame TermOp.mapLF
  rw [dif_pos hiso]
  exact snoc_comp t.lin (X.Fu u').e (X.Fu u').z b

private theorem phi_embS (v : InfinitePlace X.B.I.F) (y : D.host.E) :
    X.B.I.φ v (X.ιE.symm y) = embS D (X.pl v) y := by
  rw [X.φ_eq, RingEquiv.apply_symm_apply]

theorem zx_rat (t : TermOp.GTerm X u u' (X.Fu u) (X.Fu u') what₂ rows') (v : InfinitePlace X.B.I.F) :
    RealObj.ZX X u u' 1 t.pt.1 v = (ZhatL (lf D (X.Fu u)) t.frame).map (embS D (X.pl v)) := by
  obtain ⟨M, -, h1, -, h4⟩ := t.rep.2.1
  have h1' : uMat (t.pt.1 v) = (X.B.I.P v)⁻¹ * (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (X.B.I.φ v) *
      X.B.I.P v := h1 v
  have hfam : ∀ (w' : D.what₂.Word) (a : Fin (D.R.rS + 1)),
      RealObj.fam (fun a => HidaSetting.rv X.B.I v (X.eR a)) (HidaSetting.rv X.B.I v (X.zR w')) a =
        HidaSetting.rv X.B.I v (X.crd ((X.Fu w').fvec a)) := by
    intro w' a
    unfold RealObj.fam FlagG.fvec
    rw [X.Fu_e w', X.flagZVector w']
    exact snoc_comp (fun p => HidaSetting.rv X.B.I v (X.crd p)) X.eX (X.zu w') a
  ext a b
  rw [zx_eq]
  show HidaSetting.hJ _ (RealObj.fam _ _ a) (uMat (t.pt.1 v) *ᵥ RealObj.fam _ _ b) = _
  rw [hfam u a, hfam u' b, h1', Pf.Level.rv_mulVec, ← h4, RealObj.InfCut.UnitaryIsometries.hJ_rvX]
  simp only [Matrix.map_apply, ZhatL, Formalism.MainNotions.S.Zhat, brS]
  rw [frame_fvec]
  rfl

theorem zhatO_rat (t : TermOp.GTerm X u u' (X.Fu u) (X.Fu u') what₂ rows') (v : InfinitePlace X.B.I.F) :
    RealObj.ZhatO (RealObj.ZX X u u' 1 t.pt.1 v) =
      (ZhatOM (ZhatL (lf D (X.Fu u)) t.frame)).map (fun x => X.B.I.φ v (X.ιE.symm x)) := by
  rw [zx_rat X u u' t v]
  ext a b
  simp only [RealObj.ZhatO, ZhatOM, Matrix.map_apply, phi_embS X v, map_mul, map_pow, map_neg, map_one]

theorem g_frame (t : TermOp.GTerm X u u' (X.Fu u) (X.Fu u') what₂ rows') :
    t.G = Gval (lf D (X.Fu u)) t.frame :=
  TermDef.Gt_mk (Pf.g_value_function _ _ _) ⟨t.frame, t.rep.2.2.2.2⟩

theorem cell_frame (t : TermOp.GTerm X u u' (X.Fu u) (X.Fu u') what₂ rows') (w : Point D.host.E (D.R.rS + 1))
    (hw : t.toTerm.atPt w) : IsInCell (ZhatOM (ZhatL (lf D (X.Fu u)) t.frame)) w := by
  obtain ⟨F', hrep, -, hc⟩ := hw
  have hmk : TermDef.Rep t.lam (lf D (X.Fu u)) (TermDef.PD D t.lam (lf D (X.Fu u)) u') t.toTerm.cls t.frame :=
    TermDef.rep_mk ⟨t.frame, t.rep.2.2.2.2⟩
  exact (Pf.cell_rep_iff (Pf.cell_function_holds _ _ _) hrep hmk w).1 hc

theorem gv_ne (t : TermOp.GTerm X u u' (X.Fu u) (X.Fu u') what₂ rows') (hG : t.G ≠ 0)
    (w : Point D.host.E (D.R.rS + 1)) (L U : PairVal.MatR D) (hL : IsLoUni L) (hU : IsUpUni U)
    (hLU : ZhatOM (ZhatL (lf D (X.Fu u)) t.frame) = L * ptMat w * U) (γ : X.B.I.Ginf)
    (hγ : RealObj.IsPtRep X u u' w γ) (v : InfinitePlace X.B.I.F) :
    RealObj.Gv (RealObj.Tw u) (RealObj.Tw u') (RealObj.ZX X u u' 1 γ v) ≠ 0 := by
  have hptC : RealObj.ptC X v w = (ptMat w).map (embS D (X.pl v)) := by
    ext i j; simp only [RealObj.ptC, Matrix.map_apply, phi_embS]
  have key : ∀ l (h : l ≤ D.R.rS + 1), RealObj.Dl (RealObj.ZX X u u' 1 γ v) l =
      embS D (X.pl v) (leadMinorE (ZhatL (lf D (X.Fu u)) t.frame) l) := by
    intro l h
    have e1 := dl_zhatO (RealObj.ZX X u u' 1 γ v) h
    rw [hγ v, hptC, dl_map _ _ h] at e1
    have e2 : leadMinorE (ptMat w) l =
        leadMinorE (ZhatL (lf D (X.Fu u)) t.frame) l * sgnP D.host.E D.R.rS l h := by
      rw [← lead_zhatOM _ h, hLU, Pf.leadMinor_uni L (ptMat w) U (fun a c hac => (hL a c).1 hac)
        (fun a => (hL a a).2 rfl) (fun d b hbd => (hU d b).1 hbd) (fun b => (hU b b).2 rfl)]
    rw [e2, map_mul, sgnP_map] at e1
    have hs := localSign_sq ℂ D.R.rS l h
    calc RealObj.Dl (RealObj.ZX X u u' 1 γ v) l
        = RealObj.Dl (RealObj.ZX X u u' 1 γ v) l * (sgnP ℂ D.R.rS l h * sgnP ℂ D.R.rS l h) := by rw [hs, mul_one]
      _ = embS D (X.pl v) (leadMinorE (ZhatL (lf D (X.Fu u)) t.frame) l) * sgnP ℂ D.R.rS l h *
            sgnP ℂ D.R.rS l h := by rw [← mul_assoc, e1]
      _ = _ := by rw [mul_assoc, hs, mul_one]
  have hGv : ((RealObj.Gv (RealObj.Tw u) (RealObj.Tw u') (RealObj.ZX X u u' 1 γ v) : ℝ) : ℂ) =
      embS D (X.pl v) (Gval (lf D (X.Fu u)) t.frame) := by
    unfold RealObj.Gv
    rw [key _ le_rfl, key _ (Nat.le_succ _)]
    simp only [Gval, Gflag, Formalism.MainNotions.S.Dl, ZhatL, map_sub, map_mul, map_natCast, Formalism.BasicNotions.Examples₂.emb_star,
      Complex.mul_conj, Complex.normSq_eq_norm_sq, RealObj.Tw, Tu]
    push_cast
    ring
  intro h0
  apply hG
  rw [g_frame]
  have : embS D (X.pl v) (Gval (lf D (X.Fu u)) t.frame) = 0 := by rw [← hGv, h0, Complex.ofReal_zero]
  exact (map_eq_zero _).mp this

end Rat

section Main

variable {D : D7} (X : HidaSetting.HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word)

theorem liftCell_of (t : TermOp.GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u'))
    (hrel : t.relevant) (hat : ∃ w, t.toTerm.atPt w) :
    ∃ L U : PairVal.MatR D, IsLoUni L ∧ IsUpUni U ∧
      ZhatOM (ZhatL (lf D (X.Fu u)) t.frame) = L * ptMat (PairVal.ptOf t.toTerm) * U ∧
      ∀ v, RealObj.ZhatO (RealObj.ZX X u u' 1 t.pt.1 v) =
        (L * ptMat (PairVal.ptOf t.toTerm) * U).map (fun x => X.B.I.φ v (X.ιE.symm x)) := by
  obtain ⟨w0, hw0⟩ := hat
  have hw : t.toTerm.atPt (PairVal.ptOf t.toTerm) := PairVal.ptOf_spec _ ⟨w0, hw0, hrel⟩
  obtain ⟨L, U, hL, hU, hLU⟩ := cell_frame X u u' t _ hw
  exact ⟨L, U, hL, hU, hLU, fun v => by rw [zhatO_rat, hLU]⟩

theorem realDecompC_of
    (hAt : ∀ t : TermDef.Term D u u' (X.Fu u) (Y.what₂ u), t.G ≠ 0 → t.relevant → ∃ w, t.atPt w) :
    RealDecompC X Y u u' := by
  intro t hrel hG
  obtain ⟨L, U, hL, hU, hLU, hZ⟩ := liftCell_of X Y u u' t hrel (hAt t.toTerm hG hrel)
  obtain ⟨s, hs, s', hs', hpt0⟩ := ptRep_of_cell X u u' t.pt.1 _ L U hL hU hZ
  have hGv := gv_ne X u u' t hG _ L U hL hU hLU _ hpt0
  refine ⟨⟨_, hpt0⟩, fun γ hγ => ?_⟩
  obtain ⟨a, ha, a', ha', hdc⟩ := RealDecompW.ptRep_dc X u u' _ _ γ hpt0 hγ hGv
  have hmul : ∀ (w : D.what₂.Word) {p q : X.B.I.Ginf}, p ∈ X.SinfU w → q ∈ X.SinfU w → p * q ∈ X.SinfU w :=
    fun w p q hp hq => (Pf.SinfSub X.B.I X.eR (X.zR w)).mul_mem hp hq
  refine ⟨s⁻¹ * a⁻¹, hmul u (RealObj.InfCut.sinfU_inv X u hs) (RealObj.InfCut.sinfU_inv X u ha),
    s'⁻¹ * a'⁻¹, hmul u' (RealObj.InfCut.sinfU_inv X u' hs') (RealObj.InfCut.sinfU_inv X u' ha'), ?_⟩
  rw [hdc]
  group

theorem liftDecompC_of_atSome (κ : TermDef.Term D u u' (X.Fu u) (Y.what₂ u) → ℕ)
    (hAt : ∀ t : TermDef.Term D u u' (X.Fu u) (Y.what₂ u), t.G ≠ 0 → t.relevant → ∃ w, t.atPt w) :
    LiftDecompC X Y u u' κ := by
  intro R ρ s hs
  have hG : s.1.G ≠ 0 := realDecomp_G_ne (s := s.1) (h := s.2.1)
  obtain ⟨hex, hall⟩ := realDecompC_of X Y u u' hAt s.1 hs hG
  refine ⟨hex, hall _ ?_⟩
  unfold RealObj.gamW
  rw [dif_pos hex]
  exact hex.choose_spec

end Main

section Pos

variable {D : D7} (X : HidaSetting.HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word)

theorem gv_eq_embedding (w : Point D.host.E (D.R.rS + 1)) (γ : X.B.I.Ginf) (hγ : RealObj.IsPtRep X u u' w γ)
    (v : InfinitePlace X.B.I.F) :
    ((RealObj.Gv (RealObj.Tw u) (RealObj.Tw u') (RealObj.ZX X u u' 1 γ v) : ℝ) : ℂ) =
      embS D (X.pl v) (LocalSplitGroups.Gpt (D.mem u).A.T (D.mem u').A.T w) := by
  have hptC : RealObj.ptC X v w = (ptMat w).map (embS D (X.pl v)) := by
    ext i j; simp only [RealObj.ptC, Matrix.map_apply, phi_embS]
  have key : ∀ l (h : l ≤ D.R.rS + 1), ((‖RealObj.Dl (RealObj.ZX X u u' 1 γ v) l‖ ^ 2 : ℝ) : ℂ) =
      embS D (X.pl v) (LocalSplitGroups.Dmin w l) * conj (embS D (X.pl v) (LocalSplitGroups.Dmin w l)) := by
    intro l h
    have e1 := dl_zhatO (RealObj.ZX X u u' 1 γ v) h
    rw [hγ v, hptC, dl_map _ _ h] at e1
    have hD : leadMinorE (ptMat w) l = LocalSplitGroups.Dmin w l := by
      unfold leadMinorE LocalSplitGroups.Dmin; simp only [dif_pos h]
    rw [hD] at e1
    have hs := localSign_sq ℂ D.R.rS l h
    have e2 : RealObj.Dl (RealObj.ZX X u u' 1 γ v) l = embS D (X.pl v) (LocalSplitGroups.Dmin w l) * sgnP ℂ D.R.rS l h := by
      rw [e1, mul_assoc, hs, mul_one]
    have hn : ‖sgnP ℂ D.R.rS l h‖ ^ 2 = 1 := by
      rw [sq, ← norm_mul, hs, norm_one]
    rw [e2, norm_mul, mul_pow, hn, mul_one, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  unfold RealObj.Gv
  rw [Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_mul, key _ le_rfl, key _ (Nat.le_succ _)]
  simp only [LocalSplitGroups.Gpt, map_sub, map_mul, map_natCast, D.conjF_eq, Formalism.BasicNotions.Examples₂.emb_conj, RealObj.Tw,
    Complex.ofReal_natCast]

theorem gx_pos_of (γ : X.B.I.Ginf) (v : InfinitePlace X.B.I.F) (sc : ℝ) (hsc : sc ≠ 0)
    (h : 0 < RealObj.Gv (RealObj.Tw u) (RealObj.Tw u') (RealObj.ZX X u u' 1 γ v)) :
    0 < RealObj.GX X u u' sc γ v := by
  have hc0 : ∀ k : ℕ, ((sc : ℂ) ^ k)⁻¹ ≠ 0 := fun k =>
    inv_ne_zero (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hsc))
  have hs : ∀ k : ℕ, star (((sc : ℂ) ^ k)⁻¹) = ((sc : ℂ) ^ k)⁻¹ := fun k => by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_inv]
    exact Complex.conj_ofReal _
  have hE : ∀ a b, RealObj.ZX X u u' sc γ v a b =
      ((sc : ℂ) ^ (D.R.rS - a.1))⁻¹ * RealObj.ZX X u u' 1 γ v a b * ((sc : ℂ) ^ (D.R.rS - b.1))⁻¹ := by
    intro a b
    simp only [RealObj.ZX, RealObj.Zhat, RealObj.frm, RealObj.famSc, HidaSetting.hJ, Complex.ofReal_one, one_pow,
      inv_one, one_smul]
    simp only [Matrix.mulVec_smul, star_smul, hs]
    first
    | (simp only [Matrix.smul_dotProduct, Matrix.dotProduct_smul, smul_eq_mul]; ring)
    | (simp only [smul_dotProduct, dotProduct_smul, smul_eq_mul]; ring)
    | (simp; ring)
  have hsub : ∀ l (hl : l ≤ D.R.rS + 1),
      (RealObj.ZX X u u' sc γ v).submatrix (Fin.castLE hl) (Fin.castLE hl) =
        Matrix.diagonal (fun b : Fin l => ((sc : ℂ) ^ (D.R.rS - b.1))⁻¹) *
          (RealObj.ZX X u u' 1 γ v).submatrix (Fin.castLE hl) (Fin.castLE hl) *
            Matrix.diagonal (fun b : Fin l => ((sc : ℂ) ^ (D.R.rS - b.1))⁻¹) := by
    intro l hl
    ext a b
    simp only [Matrix.submatrix_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, hE, Fin.coe_castLE]
  have hDl : ∀ l (hl : l ≤ D.R.rS + 1), RealObj.Dl (RealObj.ZX X u u' sc γ v) l =
      (∏ b : Fin l, ((sc : ℂ) ^ (D.R.rS - b.1))⁻¹) ^ 2 * RealObj.Dl (RealObj.ZX X u u' 1 γ v) l := by
    intro l hl
    simp only [RealObj.Dl, dif_pos hl, hsub l hl, Matrix.det_mul, Matrix.det_diagonal]
    ring
  have hP1 : ∏ b : Fin (D.R.rS + 1), ((sc : ℂ) ^ (D.R.rS - b.1))⁻¹ =
      ∏ b : Fin D.R.rS, ((sc : ℂ) ^ (D.R.rS - b.1))⁻¹ := by
    rw [Fin.prod_univ_castSucc]
    simp
  have hn : 0 < ‖∏ b : Fin D.R.rS, ((sc : ℂ) ^ (D.R.rS - b.1))⁻¹‖ :=
    norm_pos_iff.mpr (Finset.prod_ne_zero_iff.mpr fun b _ => hc0 _)
  have e1 := hDl (D.R.rS + 1) le_rfl
  have e0 := hDl D.R.rS (Nat.le_succ _)
  rw [hP1] at e1
  simp only [RealObj.GX, RealObj.Gv] at h ⊢
  rw [e1, e0, _root_.norm_mul, _root_.norm_mul, _root_.norm_pow]
  have hq := mul_pos (pow_pos hn 4) h
  first
  | linarith
  | nlinarith [hq]

theorem liftGPosC_of (κ : TermDef.Term D u u' (X.Fu u) (Y.what₂ u) → ℕ)
    (hAt : ∀ t : TermDef.Term D u u' (X.Fu u) (Y.what₂ u), t.G ≠ 0 → t.relevant → ∃ w, t.atPt w)
    (hTP : ∀ (t : TermDef.Term D u u' (X.Fu u) (Y.what₂ u)) (w : Point D.host.E (D.R.rS + 1)), t.atPt w →
      LocalSplitGroups.TotPos (LocalSplitGroups.Gpt (D.mem u).A.T (D.mem u').A.T w)) :
    LiftGPosC X Y u u' κ := by
  intro R ρ s hs v
  have hG : s.1.G ≠ 0 := realDecomp_G_ne (s := s.1) (h := s.2.1)
  have hex := (realDecompC_of X Y u u' hAt s.1 hs hG).1
  have hγ : RealObj.IsPtRep X u u' (PairVal.ptOf s.1.toTerm)
      (RealObj.gamW X u u' (PairVal.ptOf s.1.toTerm)) := by
    unfold RealObj.gamW
    rw [dif_pos hex]
    exact hex.choose_spec
  have hw : s.1.toTerm.atPt (PairVal.ptOf s.1.toTerm) := by
    obtain ⟨w, hw⟩ := hAt s.1.toTerm hG hs
    have hx : ∃ w, s.1.toTerm.atPt w ∧ s.1.toTerm.relevant := ⟨w, hw, hs⟩
    unfold PairVal.ptOf
    rw [dif_pos hx]
    exact hx.choose_spec.1
  have hT := hTP s.1.toTerm _ hw (X.pl v)
  have he := congrArg Complex.re (gv_eq_embedding X u u' (PairVal.ptOf s.1.toTerm) _ hγ v)
  rw [Complex.ofReal_re] at he
  refine gx_pos_of X u u' _ v _ (Formalism.MainNotions.LocalModelPeriodLattices.rdE_pos D).ne' ?_
  rw [he]
  exact hT

theorem liftAtSomeC_of (κ : TermDef.Term D u u' (X.Fu u) (Y.what₂ u) → ℕ)
    (hAt : ∀ t : TermDef.Term D u u' (X.Fu u) (Y.what₂ u), t.G ≠ 0 → t.relevant → ∃ w, t.atPt w) :
    LiftAtSomeC X Y u u' κ := by
  intro R ρ s hs
  have hG : s.1.G ≠ 0 := realDecomp_G_ne (s := s.1) (h := s.2.1)
  exact hAt s.1.toTerm hG hs

end Pos

end Formalism.L2.SG.Pf.RowForm.RealDecompL
