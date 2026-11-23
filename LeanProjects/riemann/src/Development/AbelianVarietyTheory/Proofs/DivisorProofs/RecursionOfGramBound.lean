import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Formalism.LocalToGlobal.IndefiniteReal.PrimitivePackageFullHecke
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovolumePerRankLeNegSlopeScaledStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftFormsFramesMajorantNormEqPeterssonStatement

set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open GlobalTheory.CovTop GlobalTheory.BigTop

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CovTop

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ}

theorem recAt_of_gramAt (p : PtAt ex Csz) (i : Fin D.R.m) (hp : p.Rows) (hg : GramAt p i) : RecAt p i := by
  have hR := complex_data_conditions_base_level_of_primitive_links hp.ok hp.sep p.charW hp.prim
  have hD : (p.S false).dW i = (p.S false).D :=
    (primRows3 hp.ok hp.sep p.R p.F p.charW hp.prim).dW_eq (hR.wf false) i
  have hpos : 0 < (p.S false).D := (primRows3 hp.ok hp.sep p.R p.F p.charW hp.prim).D_pos
  obtain ⟨hU, hN⟩ := GlobalTheory.T.liftForms_frames_majorantNorm_eq_petersson p.R p.F false i (RealDat3.kForm_of hp.prim.unif false)
  have hn1 : (1 : ℝ) ≤ RealDat.nP p.F.lv2 false := by
    unfold RealDat.nP
    exact_mod_cast Nat.one_le_iff_ne_zero.2 Nat.card_pos.ne'
  have hs0 : 0 < (Real.sqrt (RealDat.nP p.F.lv2 false))⁻¹ := inv_pos.2 (Real.sqrt_pos.2 (by linarith))
  have hs1 : (Real.sqrt (RealDat.nP p.F.lv2 false))⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (Real.one_le_sqrt.2 hn1)
  have hli : LinearIndependent D.what₂.LL (p.R.toRealDat.bL p.F.lv2 false i) :=
    (Module.finBasis D.what₂.LL (p.R.toRealDat.WL p.F.lv2 false i)).linearIndependent.map'
      (p.R.toRealDat.WL p.F.lv2 false i).subtype (Submodule.ker_subtype _)
  have hsp : ∀ x ∈ latGood p.R.toRealDat p.F.lv2 i,
      x ∈ Submodule.span D.what₂.LL (Set.range (p.R.toRealDat.bL p.F.lv2 false i)) := by
    intro x hx
    have hxW : x ∈ p.R.toRealDat.WL p.F.lv2 false i := ⟨hx.1.2, hx.2⟩
    have e : Submodule.span D.what₂.LL (Set.range (p.R.toRealDat.bL p.F.lv2 false i)) = p.R.toRealDat.WL p.F.lv2 false i := by
      have := (Module.finBasis D.what₂.LL (p.R.toRealDat.WL p.F.lv2 false i)).span_eq
      have h2 := congrArg (Submodule.map (p.R.toRealDat.WL p.F.lv2 false i).subtype) this
      rw [Submodule.map_span, ← Set.range_comp, Submodule.map_subtype_top] at h2
      exact h2
    rw [e]; exact hxW
  have key := GlobalTheory.T.covolumePerRank_le_neg_slope_scaled D.what₂.LL _ (nrmR p.R.toRealDat i) hg.1 (latGood p.R.toRealDat p.F.lv2 i) _ (show 0 < (p.S false).dW i from hD.symm ▸ hpos)
    (p.R.toRealDat.bL p.F.lv2 false i) hli hsp ((p.S false).XW i) _ hs0 hs1 hU hN (hp.prim.mLat i)
  unfold RecAt
  rw [← hD]
  exact key

theorem rec_of_gram : Gram → Rec := fun h =>
  Closed.imp h fun _ _ _ ⟨C, hC, x0, h⟩ =>
    ⟨C, hC, x0, fun x hx hle ι p hp i => recAt_of_gramAt p i hp.1 (h x hx hle ι p hp i)⟩

end GlobalTheory.CovTop

end
