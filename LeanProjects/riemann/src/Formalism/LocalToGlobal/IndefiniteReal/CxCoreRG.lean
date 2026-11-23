import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.CxLemmas
import Formalism.LocalToGlobal.IndefiniteForms.PairingConditionOfInverseMatrixIdentity

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.Cx

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV

variable {K : Type} [Field K] [NumberField K] [StarRing K]

namespace CxData

variable {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A) {fc : DefSub A → DefFace Bs} (cr : Crd A fc) (b : Bool)

structure RowHyp : Prop where

  wf : (lv (fc X.zs) b).WF

  h4pos : X.H4pos

  h2 : X.H2 cr b

  ratMu : X.RATmu cr b

  h3 : X.H3 cr b

  h4 : X.H4 cr b

  partsOrth : X.PartsOrth b (fc := fc)

structure LiftHyp : Prop where

  h5 : X.H5 cr b

  ratTh : X.RATth cr b

  kForm : X.KForm b

  ewNorm : X.EWnorm b

  thmA : X.ThmA cr b

  galD : X.GalD cr b

  h3W : X.H3W cr b

  mLat : X.MLat b

theorem XE_specR (hR : RowHyp X cr b) :
    (∀ v, IsUnit (X.XE cr b v).det) ∧ X.XE cr b Bs.v0 = frameOf (X.gramE cr b) :=
  let h := rowXE_spec (Df := lv (fc X.zs) b) hR.wf _ (X.gramE_unit cr b (hR.h2) (hR.h4pos.2.2 b)) X.κ hR.h4pos.1
    (fun j p v => X.lam j Bs.μ0 p v) (fun j p v => hR.h4pos.2.1 j Bs.μ0 p v)
  ⟨h.1, h.2.1⟩

theorem scal_rowsR (hR : RowHyp X cr b) (t : Bs.Tup) (v : InfinitePlace K)
    (htv : t = Bs.μ0 ∨ v = Bs.v0) (p : Bs.Ix) :
    IsScalarOn ((lv (fc X.zs) b).XQ t) (X.data cr b).XE v ((X.data cr b).ι t) ((X.data cr b).Qpart t p)
      ((X.data cr b).κ v * ∏ j, (X.data cr b).lam j t p v) := by
  intro x hx y
  have hx' : X.iC cr b t (cpt Bs.v0.embedding x) ∈ X.EEp p := by
    have h : (X.rowMat cr b t).mulVec x ∈ X.Ep cr b p := hx
    rwa [mem_Ep, key_row X cr b (hR.h2) (hR.ratMu)] at h
  by_cases hv : v = Bs.v0
  · subst hv
    change Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin ((lv (fc X.zs) b).dQ Bs.μ0))) (X.XE cr b) Bs.v0 ((X.rowMat cr b t).mulVec x) ((X.rowMat cr b t).mulVec y) = _
    rw [majAt_gram_smul (X.XE cr b) Bs.v0 (fun i => X.iC cr b Bs.μ0 (Pi.single i 1))
      (li_of_lin_injective (by rw [lin_basis]; exact (hR.h2).1)) _ (inv_pos.mpr (hR.h4pos.2.2 b))
      (X.XE_specR cr b hR).2, lin_basis,
      key_row X cr b (hR.h2) (hR.ratMu), key_row X cr b (hR.h2) (hR.ratMu), (hR.h4) t p x hx' y]
    have hn : (X.nP b : ℂ) ≠ 0 := by exact_mod_cast (hR.h4pos.2.2 b).ne'
    push_cast
    field_simp
    dsimp only [CxData.data]
    ring
  · rcases htv with rfl | h
    · change Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin ((lv (fc X.zs) b).dQ Bs.μ0))) (X.XE cr b) v ((X.rowMat cr b Bs.μ0).mulVec x) ((X.rowMat cr b Bs.μ0).mulVec y) = _
      rw [X.rowMat_base cr b (hR.h2), Matrix.one_mulVec, Matrix.one_mulVec]
      have hxQ : x ∈ (lv (fc X.zs) b).Qp Bs.μ0 p := ((hR.h3) p x).2 hx'
      exact rowXE_part (lv (fc X.zs) b) hR.wf _ (X.gramE_unit cr b (hR.h2) (hR.h4pos.2.2 b)) X.κ hR.h4pos.1
        (fun j p v => X.lam j Bs.μ0 p v) (fun j p v => hR.h4pos.2.1 j Bs.μ0 p v) v hv
        (fun p q hpq x hx y hy => (hR.partsOrth) v hv p q hpq x hx y hy) p x hxQ y
    · exact absurd h hv

theorem scal_liftsR (hR : RowHyp X cr b) (hF : LiftHyp X cr b) (j : Bs.J) (t : Bs.Tup) (v : InfinitePlace K)
    (htv : t = Bs.μ0 ∨ v = Bs.v0) (p : Bs.Ix) :
    IsScalarOn ((lv (fc X.zs) b).XT j t) ((X.data cr b).XW j) v ((X.data cr b).θ j t) ((X.data cr b).Zpart j t p)
      ((X.data cr b).lam j t p v) := by
  intro x hx y
  have hx' : X.tC cr b j t (cpt Bs.v0.embedding x) ∈ X.Wp j p := by
    have h : (X.liftMat cr b j t).mulVec x ∈ X.WpK b j p := hx
    rwa [mem_WpK, key_lift X cr b (hF.h5) (hF.ratTh)] at h
  change Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin (X.dW b j))) (X.XW b j) v ((X.liftMat cr b j t).mulVec x) ((X.liftMat cr b j t).mulVec y) = _
  rw [majAt_gram (X.XW b j) v (X.bW b j v) ((hF.kForm) j v).1 rfl]
  by_cases hv : v = Bs.v0
  · subst hv
    have hn : ((X.nP b : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (hR.h4pos.2.2 b).ne'
    have he := (hF.ewNorm) j (X.wC b j Bs.v0 (cpt Bs.v0.embedding ((X.liftMat cr b j t).mulVec x)))
      (X.wC b j Bs.v0 (cpt Bs.v0.embedding ((X.liftMat cr b j t).mulVec y)))
    change ⟪X.w0C b j (cpt Bs.v0.embedding ((X.liftMat cr b j t).mulVec x)),
      X.w0C b j (cpt Bs.v0.embedding ((X.liftMat cr b j t).mulVec y))⟫_ℂ = _ at he
    rw [key_lift X cr b (hF.h5) (hF.ratTh), key_lift X cr b (hF.h5) (hF.ratTh),
      (hF.thmA) j t p x hx' y] at he
    change ⟪X.wC b j Bs.v0 (cpt Bs.v0.embedding ((X.liftMat cr b j t).mulVec x)),
      X.wC b j Bs.v0 (cpt Bs.v0.embedding ((X.liftMat cr b j t).mulVec y))⟫_ℂ = _
    apply mul_left_cancel₀ hn
    rw [← he]
    dsimp only [CxData.data]
    push_cast
    ring
  · rcases htv with rfl | h
    · exact (hF.galD) j v hv p x hx' y
    · exact absurd h hv

def rowsOfR (hR : RowHyp X cr b) (hF : LiftHyp X cr b) (hpos : (lv (fc X.zs) b).Pos) (hprov : (lv (fc X.zs) b).Proviso)
    (htypes : (lv (fc X.zs) b).Types) (hh0 : X.H0) (hl1d : (X.data cr b).DimensionsOfPartsAgree) : IndefRows (lv (fc X.zs) b) where
  toIndefData := X.data cr b
  pos := hpos
  proviso := hprov
  types := htypes
  h0 := hh0
  frames := ⟨(X.XE_specR cr b hR).1, fun j v => frame_gram_unit _ ((hF.kForm) j v).1, hF.mLat⟩
  l1a := by
    refine ⟨fun p => ?_, fun j p => ?_⟩
    · change ((lv (fc X.zs) b).Qp Bs.μ0 p).map (X.rowMat cr b Bs.μ0).mulVecLin = X.Ep cr b p
      rw [X.rowMat_base cr b (hR.h2), Matrix.mulVecLin_one, Submodule.map_id]
      ext x
      rw [mem_Ep]
      exact (hR.h3) p x
    · change ((lv (fc X.zs) b).Zp j Bs.μ0 p).map (X.liftMat cr b j Bs.μ0).mulVecLin = X.WpK b j p
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        rw [Matrix.mulVecLin_apply, mem_WpK, key_lift X cr b (hF.h5) (hF.ratTh)]
        exact ((hF.h3W) j p x).1 hx
      · intro hy
        obtain ⟨x, rfl⟩ := (X.liftMat_bij cr b (hF.kForm) (hF.ewNorm) (hR.h4pos.2.2 b) (hF.h5) (hF.ratTh) j Bs.μ0).2 y
        refine ⟨x, ?_, rfl⟩
        rw [mem_WpK, key_lift X cr b (hF.h5) (hF.ratTh)] at hy
        exact ((hF.h3W) j p x).2 hy
  l1c := ⟨fun t => X.rowMat_bij cr b (hR.h2) (hR.ratMu) t,
    fun j t => X.liftMat_bij cr b (hF.kForm) (hF.ewNorm) (hR.h4pos.2.2 b) (hF.h5) (hF.ratTh) j t, hR.h4pos.1,
    fun j t p v => hR.h4pos.2.1 j t p v, fun t v htv p => X.scal_rowsR cr b hR t v htv p,
    fun j t v htv p => X.scal_liftsR cr b hR hF j t v htv p⟩
  l1d := hl1d

def colsOfR (hR : RowHyp X cr true) (hpos : (lv (fc X.zs) true).Pos) (hh0 : X.H0) (Y : CxCol (fc := fc) X)
    (N : IndefNum Bs) (hl6 : (X.data cr true).L6 N) (hl1b : (X.colOf cr Y).PairingFactorsThroughPeriods) (hl1e : (X.colOf cr Y).L1e) :
    IndefColsR (lv (fc X.zs) true) (fc X.zs).Dc (fc X.zs).Sp N where
  toIndefData := X.data cr true
  pos := hpos
  h0 := hh0
  frames := (X.XE_specR cr true hR).1
  l1a := fun p => by
    change ((lv (fc X.zs) true).Qp Bs.μ0 p).map (X.rowMat cr true Bs.μ0).mulVecLin = X.Ep cr true p
    rw [X.rowMat_base cr true hR.h2, Matrix.mulVecLin_one, Submodule.map_id]
    ext x
    rw [mem_Ep]
    exact hR.h3 p x
  l1c := ⟨fun t => X.rowMat_bij cr true hR.h2 hR.ratMu t, hR.h4pos.1, fun j t p v => hR.h4pos.2.1 j t p v,
    fun t v htv p => X.scal_rowsR cr true hR t v htv p⟩
  l6 := hl6
  col := X.colOf cr Y
  l1b := hl1b
  l1e := hl1e

def cxPkgR (cf : ConvFace Bs) (Y : CxCol (fc := fc) X) (C CH : ℝ) (hst : X.zs.Stable) (hin : X.zs.InBlock)
    (hR0 : X.RowHyp cr false) (hF0 : X.LiftHyp cr false) (hpos : ∀ b, (lv (fc X.zs) b).Pos)
    (hprov : (lv (fc X.zs) false).Proviso) (htypes : (lv (fc X.zs) false).Types) (hh0 : X.H0)
    (hl1d : (X.data cr false).DimensionsOfPartsAgree) (hl3 : (X.data cr false).L3 ((fc X.zs).Z.num C CH))
    (hon : (X.data cr false).ON ((fc X.zs).Z.num C CH)) (hR1 : X.RowHyp cr true)
    (hl6 : (X.data cr true).L6 ((fc X.zs).Z.num C CH)) (hl1b : (X.colOf cr Y).PairingFactorsThroughPeriods) (hl1e : (X.colOf cr Y).L1e)
    (huntw : (X.data cr false).Untwisted ((fc X.zs).Z.num C CH))
    (hpass : Passage ((fc X.zs).Z.num C CH) (X.data cr false) (X.data cr true))
    (hfun0 : (X.data cr false).FUN ((fc X.zs).Z.num C CH)) (hconv : IndefConv Bs X.μ cf)
    (hB : HeckeAll cf (X.data cr false)) (hCc : HeckeRows cf (X.data cr true)) : IndefPkgR A fc cf C CH where
  Zs := X.zs
  stable := hst
  inBlock := hin
  core :=
    { base := { toIndefRows := X.rowsOfR cr false hR0 hF0 (hpos false) hprov htypes hh0 hl1d, l3 := hl3, on := hon }
      cols := X.colsOfR cr hR1 (hpos true) hh0 Y _ hl6 hl1b hl1e
      extra := { untw := huntw, level := ⟨rfl, rfl, rfl⟩, passage := hpass, fun0 := hfun0 } }
  conv := hconv
  heckeB := hB
  heckeC := hCc

end CxData

end Formalism.IndefR.Cx
