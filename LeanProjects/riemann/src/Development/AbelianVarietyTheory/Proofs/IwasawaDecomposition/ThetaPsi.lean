import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnlocalizedSaturatedState
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.SignAtBasePlaceEqEmbedding

noncomputable section

namespace GlobalTheory.HeightCounting.Up

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain GlobalTheory.HeightCounting

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure CopyN (D : D7) {D' : D7} (N : TwNew D') (ι : D.what₂.LL →+* D'.what₂.LL) (e : ↥D'.LL0 ≃+* ↥D.LL0) : Prop where
  cp : GlobalTheory.TwInputs.Move.CopyTw D N.toD7 ι e
  ThetaPsi : HEq D.ntw.ThetaPsi N.tw.ThetaPsi
  topO : HEq D.ntw.topO N.tw.topO
  finLam : HEq D.ntw.finLam N.tw.finLam
  jL : HEq D.ntw.jL N.tw.jL
  s2 : HEq D.ntw.s2 N.tw.s2
  lamG : HEq D.ntw.lamG N.tw.lamG
  Xv : HEq D.ntw.Xv N.tw.Xv
  qs : HEq D.ntw.qs N.tw.qs
  res : HEq D.ntw.res N.tw.res
  eLL0 : ∀ g g', HEq g g' → e (N.ex.eLL0 g') = D.nexp.eLL0 g
  twPsi : HEq D.nexp.twPsi N.ex.twPsi
  twDel : HEq D.nexp.twDel N.ex.twDel
  eH : HEq D.nexp.eH N.ex.eH

theorem CopyN.refl (D : D7) : CopyN D (⟨D.ntw, D.nexp, D.nStage_trivialCharacter_coeff_eq, D.nth, D.ntwbr, D.ntwbr_ind⟩ : TwNew D) (RingHom.id _) (RingEquiv.refl _) where
  cp := GlobalTheory.TwInputs.Move.CopyTw.refl D
  ThetaPsi := HEq.rfl
  topO := HEq.rfl
  finLam := HEq.rfl
  jL := HEq.rfl
  s2 := HEq.rfl
  lamG := HEq.rfl
  Xv := HEq.rfl
  qs := HEq.rfl
  res := HEq.rfl
  eLL0 _ _ h := by cases h; rfl
  twPsi := HEq.rfl
  twDel := HEq.rfl
  eH := HEq.rfl

theorem CopyN.carried {D D' : D7} {N : TwNew D'} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0} (h : CopyN D N ι e) :
    Carried D N.toD7 := by
  refine ⟨h.cp.toSameExport, fun i i' hi x x' hx => ?_⟩
  have hx' : x = e x' := Subtype.ext (D.what₂.embLL.injective
    (hx.trans ((congrArg N.toD7.what₂.embLL (h.cp.LL0 x')).symm.trans (h.cp.embLL _))))
  subst hx'
  exact ⟨h.cp.emb0 i i' hi x', h.cp.emb0b i i' hi x'⟩

end GlobalTheory.HeightCounting.Up

end
