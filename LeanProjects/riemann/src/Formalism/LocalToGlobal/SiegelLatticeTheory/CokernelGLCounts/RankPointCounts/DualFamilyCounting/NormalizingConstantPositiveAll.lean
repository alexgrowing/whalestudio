import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcAllC
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RowFormAllOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Rescale
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AmpValAll
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataXDens
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataTies
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocVolPrim
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataPos
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdConvHoldsGen
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CovolumeFrames.StepSize
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.LocFramePrim

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.NcAllC

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.LocVol
  Formalism.L2.SG.MassDataConc Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory Formalism.L2.SG.PoincareAmplitudeLowerBounds
  Formalism.L2.SG.DataInst Formalism.L2.SG.CntLocal NumberField

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 4000000 in
variable [Fact PI.AprimeInfW.GaugeVolUD] [Fact Formalism.L2.SG.Pf.WB.RhsWLim] [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in
theorem normalizing_constants_all (hCov : Formalism.L2.SG.Pf.NcReal.JX.CovolRef) (hSW : PI.VolStabS.MassDataS.SWXS) : NormalizingConstantPositiveAll := by
  intro D T u u' X0 C Th Q i0 i0' νq Lsp ϖ hne hSt hCT hdet hk hcong hi hPR hNu hϖ
  have hK2 := Formalism.L2.SG.Closed.level_subgroup_properties T.X
  have hV : 0 < T.X.volK2 := ENNReal.toReal_pos (ne_of_gt hK2.2.2.1) (ne_of_lt hK2.2.2.2)
  have hH : Formalism.L2.SG.TypedSets.HypX T.X T.hb (T.Y.FN u) (T.Y.FN u') u u' :=
    ⟨T.measTie, hCT.1, T.Y.FN_fund u, T.Y.FN_fund u'⟩
  have hStd : StdHyp T.X.B.I.cm.sig T.X.B.I.J T.ψ :=
    ⟨MassDataVolumesW.stepCM T.X, MassDataVolumesW.stepHerm T.X, T.ψ_char, T.ψ_std⟩
  have hlat : ∃ L : Submodule (NumberField.RingOfIntegers T.X.B.I.E) (Fin T.X.B.I.n → T.X.B.I.E),
      Submodule.IsLattice T.X.B.I.E L ∧
      (L : Set (Fin T.X.B.I.n → T.X.B.I.E)) = (T.X.B.I.L : Set (Fin T.X.B.I.n → T.X.B.I.E)) :=
    ⟨T.X.B.I.L, ⟨T.X.B.I.L_fg, T.X.B.I.L_span⟩, rfl⟩
  have hdet' : (gramE T.X.B.I.cm.sig T.X.B.I.J (tupH (frameOf T.X u'))).det ≠ 0 :=
    Formalism.L2.SG.Pf.Rescale.standard_gram_nondegenerate T.X.B.I.F T.X.B.I.E T.X.B.I.cm.sig T.X.B.I.n T.X.B.I.J _ _ _
      (fun x => star_star x) hStd.2.1 (Formalism.L2.SG.Pf.Rescale.frame_stdX T.X u')
  have hPC := Formalism.L2.SG.Pf.ProdConvCut2.prodConvAll_holds D T u u' hne hSt
  have hL := locTieX_of T.X T.ψ u (T.locCompat u) (Formalism.L2.SG.Pf.LocVolPrim.primX T.X u locFramePrim)
  have hL' := locTieX_of T.X T.ψ u' (T.locCompat u') (Formalism.L2.SG.Pf.LocVolPrim.primX T.X u' locFramePrim)
  have hTF := Formalism.L2.SG.Pf.typFacts_holds T.X T.hb u u'
  have hsd := Formalism.L2.SG.Pf.MassDataX.densNonnegAll_holds D T u u' Lsp ϖ
  have hQ := Formalism.L2.SG.Pf.MassDataPos.quotVolPosC_of T.X T.hb T.Y u u' X0 T.ψ (T.Y.tO u u')
    (supDens Lsp T.Y.δ ϖ u u' (T.X.Fu u) (T.Y.what₂ u) / ∏' p, alpD u u' p) 0 1
    (Formalism.L2.SG.PairVal.vRdef D u u' (T.X.Fu u) (T.Y.what₂ u) T.Y.δ T.Y.M) Q T.Y.M T.Y.δ i0 i0' νq hK2 hV
  have hN := ncTieC_of_closed T.X T.hb T.Y.hK (T.Y.FN u) (T.Y.FN u') u u' X0 T.ψ (T.Y.tO u u')
    (supDens Lsp T.Y.δ ϖ u u' (T.X.Fu u) (T.Y.what₂ u) / ∏' p, alpD u u' p) 0 1
    (Formalism.L2.SG.PairVal.vRdef D u u' (T.X.Fu u) (T.Y.what₂ u) T.Y.δ T.Y.M) Q T.Y.M T.Y.δ i0 i0' νq hCov hSW
    hH T.measCompat hStd hlat hdet' hdet hPC hL hL' hTF hQ hsd le_rfl one_pos hcong (T.Y.rowsOK u)
  have hc0 : 0 < (bCF T.X T.hb T.Y.hK (T.Y.FN u) (T.Y.FN u') u u' X0 T.ψ (T.Y.tO u u')
      (supDens Lsp T.Y.δ ϖ u u' (T.X.Fu u) (T.Y.what₂ u) / ∏' p, alpD u u' p) C Th
      (Formalism.L2.SG.PairVal.vRdef D u u' (T.X.Fu u) (T.Y.what₂ u) T.Y.δ T.Y.M) Q T.Y.M T.Y.δ i0 i0' νq).c0 := by
    have h := Formalism.L2.SG.Pf.poincareConstant_pos T.X T.Y u
    have e : Formalism.L2.SG.PoincareInHH.PoincareSetting.c0X T.X u (T.Y.FN u) = T.X.volK2 *
        ((T.X.muN u (T.Y.FN u)).toReal * (T.X.muH u Set.univ).toReal / (Module.finrank ℂ (T.X.Vpi u) : ℝ)) := by
      unfold Formalism.L2.SG.PoincareInHH.PoincareSetting.c0X; ring
    rw [e] at h
    exact pos_of_mul_pos_right h hV.le
  have hc0' : 0 < (bCF T.X T.hb T.Y.hK (T.Y.FN u) (T.Y.FN u') u u' X0 T.ψ (T.Y.tO u u')
      (supDens Lsp T.Y.δ ϖ u u' (T.X.Fu u) (T.Y.what₂ u) / ∏' p, alpD u u' p) C Th
      (Formalism.L2.SG.PairVal.vRdef D u u' (T.X.Fu u) (T.Y.what₂ u) T.Y.δ T.Y.M) Q T.Y.M T.Y.δ i0 i0' νq).c0' := by
    have h := Formalism.L2.SG.Pf.poincareConstant_pos T.X T.Y u'
    have e : Formalism.L2.SG.PoincareInHH.PoincareSetting.c0X T.X u' (T.Y.FN u') = T.X.volK2 *
        ((T.X.muN u' (T.Y.FN u')).toReal * (T.X.muH u' Set.univ).toReal / (Module.finrank ℂ (T.X.Vpi u') : ℝ)) := by
      unfold Formalism.L2.SG.PoincareInHH.PoincareSetting.c0X; ring
    rw [e] at h
    exact pos_of_mul_pos_right h hV.le
  exact ⟨hN, mul_pos hc0 hc0'⟩

end Formalism.L2.SG.Pf.NcAllC
