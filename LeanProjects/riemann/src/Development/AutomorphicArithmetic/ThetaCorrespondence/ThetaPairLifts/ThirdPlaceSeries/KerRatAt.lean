import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IteratedDerivativeSubmoduleStable
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ReadComparisonAt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowAtOfRatStep
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LowAtHolds
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwAdm
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RatHyp0AtPointStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.InGeoGeoHalfStatement

set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT Formalism.IndefR.Datum GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.OnCmp
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries GlobalTheory.ConjTwist GlobalTheory.FlatVecSum GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels
open GlobalTheory.BigOn.Exp.SerBase
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.BigOn.Exp.SerBase
open GlobalTheory.RealGeo GlobalTheory.Unframe GlobalTheory.UnframePt in
theorem kerRatAt_alt : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt →
    GlobalTheory.SerStd.SeriesRatS → _root_.GlobalTheory.BigOn.Exp.SerBase.KernelRationalAt := by
  intro hP hA hR hS
  refine (_root_.GlobalTheory.BigOn.Exp.lowAt_holds_alt.and _root_.GlobalTheory.BigOn.Exp.twAdm_alt).imp fun Fm x hx i p hp hM w hw j hLT => ?_
  obtain ⟨l1, l2⟩ := hLT
  have h0 := _root_.GlobalTheory.T.ratHyp0_of_bad_prime_mem_S0 Fm x hx i p hp hM _ l2.2.2 l1 j
  obtain ⟨c', w', hw', hfr, B', hv⟩ := exists_framed_half hP h0.size (GlobalTheory.Core5.of_core h0.core) (geoHalf p) h0.unif
    (_root_.GlobalTheory.T.inGeo_half_of_ratHyp0 hP Fm x hx i p hp hM _ j h0)
  obtain ⟨S', YS', -⟩ := GlobalTheory.T.seriesRationality_back_from_movedReadings p.R p.cG p.Sx p.nexp w' hw'
  letI iA : Algebra (setCE p.T c').Q.c.F (Fm.D x i).what₂.LL := p.alg
  have hV' : (setCE p.T c').V ((j : ℕ) + 1) (setCE p.T c').σ₀ = Wc (Fm.D x i) j :=
    B'.fw.laws.spaceW _ ⟨Nat.le_add_left _ _, j.2⟩ _ (setCE p.T c').toCore.good_σ₀
  have hU' : (fullHeckeRealDatMovedReadings p.R w').toRealDat.LUnif := GlobalTheory.T.uniformisationLaws_centralMovedReadings p.R.toRealDat w' hw' h0.unif
  have hG : (fullHeckeRealDatMovedReadings p.R w').toRealDat.IsGrp (F2 p) :=
    ⟨h0.core.grp.red_R, h0.core.grp.red_L, h0.core.grp.levels, h0.core.grp.record, h0.core.grp.chiW⟩
  have c := h0.core
  have hF : (fullHeckeRealDatMovedReadings p.R w').toRealDat.IsFam := { c.fam with }
  have hMo : (fullHeckeRealDatMovedReadings p.R w').toRealDat.IsModels := { c.models with }
  have hCh : (fullHeckeRealDatMovedReadings p.R w').toRealDat.IsChain := { c.chain with }
  have hTh : (fullHeckeRealDatMovedReadings p.R w').toRealDat.IsThP := { c.thP with }
  have hC : GlobalTheory.Hk3.Core (fullHeckeRealDatMovedReadings p.R w').toRealDat (F2 p) := ⟨c.lev, hG, hF, hMo, hCh, hTh⟩
  have hph : (fun k => cj (twAt (Fm.D x i).what₂.embLL p.P.A3.A.v0) ((fullHeckeRealDatMovedReadings p.R w').phs k)) = fun _ => (1 : ℂ) :=
    funext fun k => by
      show cj (twAt (Fm.D x i).what₂.embLL p.P.A3.A.v0) (p.R.phs k) = 1
      rw [p.phsOne k, map_one]
  have hRat : RatHyp (setCE p.T c') (fullHeckeRealDatMovedReadings p.R w') (F2 p) B'.κ B'.v₀ B'.O ((Fm.ex x hx i).nch.twI w) j hV' := by
    refine ⟨h0.size, h0.host, h0.std, B'.fw.laws, hC, hU', ⟨B'.fw⟩,
      ⟨B'.fw.laws, B'.fw.alg_eq, B'.fw.kap, B'.fw.hv₀, B'.fw.chiR, B'.fw.x0⟩, h0.io, h0.guard, h0.fin, B'.pins j, ?_,
      hfr j hV', h0.galois, h0.small, h0.inUse, h0.low⟩
    rw [hph]
    exact B'.phase j hU'
  intro χ ξR ω φ hK h hh y hy u hu
  have hK' : KerDat (fullHeckeRealDatMovedReadings p.R w').toRealDat j ((fullHeckeRealDatMovedReadings p.R w').C.delAt (Formalism.EigenvalueLevelCeiling.plc ((Fm.D x i).plEq w))) χ ξR
      (placesOver (fullHeckeRealDatMovedReadings p.R w').toRealDat ((fullHeckeRealDatMovedReadings p.R w').mu ((Fm.D x i).plEq w)) (ownAt (Fm.D x i) ((Fm.D x i).plEq w)))
      ω φ := ⟨hK.chr, hK.fin, hK.triv, hK.tame, hK.pl, hK.off, hK.ram, hK.res, hK.weil, hK.vec⟩
  have hy' : InCoefLat (fullHeckeRealDatMovedReadings p.R w').toRealDat j h y := hy
  obtain ⟨x', hx'⟩ := kerRat_framed (T := setCE p.T c') hP hA hR hS YS' hRat (fun k => p.phsOne k) ((Fm.D x i).plEq w) hK' hh
    hy' u (by rw [hv]; exact hu)
  exact ⟨(p.R.FW j).ρ (w' j (sg0 _ p.P.A3.A)) x', hx'⟩
end GlobalTheory.BigOn.Exp.SerBase
end
end
