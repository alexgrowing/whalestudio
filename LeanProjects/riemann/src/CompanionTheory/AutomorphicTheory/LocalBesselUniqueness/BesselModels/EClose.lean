import Formalism.LocalToGlobal.SiegelLatticeTheory.WeightedGaugeFactors.FactsDS
import CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.EFinal
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.EnergyConvClose

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.S.Pv.ConvG

open scoped InnerProductSpace ENNReal

namespace Formalism.L2.SG.RealObj.EnergyConvJ

namespace BM

set_option maxHeartbeats 400000 in

theorem locQuadGG_G_holds (hI : CompanionTheory.Lime.BM.Inputs2) : LocQuadGG_G := by
  intro D hG X u u' sc hsc v cv hcv g hZ
  obtain ⟨τ, hτ⟩ : ∃ τ, vOf X τ = v := ⟨X.pl v, X.pl.symm_apply_apply v⟩
  subst hτ
  obtain ⟨μS, ν, hloc, h4⟩ := Formalism.L2.SG.RealObj.EnergyFinal.BM.weilPairJ_holds hI hG X τ
  obtain ⟨hs1, hn1, hW1, hi1, h01, -⟩ := hloc u
  obtain ⟨hs2, hn2, hW2, hi2, h02, -⟩ := hloc u'
  have hfin := h4 u u' sc hsc cv hcv g hZ
  have hU := Formalism.L2.S.Pv.SchurTens.unitRep_of_URepOn (X.ds (vOf X τ)).2.2.1
  rw [quad_eq_GG (μ := Formalism.REAL.muG (X.B.I.ε (vOf X τ))) (μS := μS u) (μS' := μS u') (ν := ν u) (ν' := ν u')
    (S := Formalism.L2.SG.Pf.WuDec.Sloc X u (vOf X τ)) (S' := Formalism.L2.SG.Pf.WuDec.Sloc X u' (vOf X τ)) hU
    (X.B.w (vOf X τ)) (X.Wloc_cont u (vOf X τ)) (X.Wloc_cont u' (vOf X τ)) hW1 hW2 hi1 hi2 h01 h02
    (fun a ha => Formalism.L2.SG.Pf.WuDec.inv_mem_Sloc X u (vOf X τ) ha)
    (fun a ha => Formalism.L2.SG.Pf.WuDec.inv_mem_Sloc X u' (vOf X τ) ha)
    (fun s hs x => Formalism.L2.SG.Pf.WuDec.norm_Wloc_inv X u (vOf X τ) hs x)
    (fun s hs x => Formalism.L2.SG.Pf.WuDec.norm_Wloc_inv X u' (vOf X τ) hs x) g] at hfin
  unfold PhiGG at hfin
  exact hfin

end BM

end Formalism.L2.SG.RealObj.EnergyConvJ
