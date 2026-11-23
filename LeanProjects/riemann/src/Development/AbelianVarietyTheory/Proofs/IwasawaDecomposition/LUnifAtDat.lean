import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HoldsUIff
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.Divisibility.LiftLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeometricHalfCoreFormsUniformisationIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PbEqOfPins
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEquivariantUnitConstantsGoodEmbeddingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LUnifOfRhoGeoEquivAll
import Formalism.LocalToGlobal.IndefiniteReal.LinksW
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Host GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Top.Bl

open Formalism.IndefR.FWT Formalism.L2.Pj Formalism.IndefR.Mult

set_option maxHeartbeats 1000000 in

theorem lUnif_atDat : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Hk3.HoweUnram →
    GlobalTheory.Mem.Top.Bl.AtDat fun _ B f T w Z hX Wt z => z.R.toRealDat.LUnif := by
  intro _ _ _
  refine StepW.of_all fun K B f T w _ _ _ Z hX Wt z _ _ hEx hIn => ?_
  have hch := z.pins.char
  have hC : GlobalTheory.RealGeo.PreChar z.R.toRealDat :=
    ⟨hch.base.lev, hch.base.grp.red_R, hch.base.grp.red_L, hch.base.grp.record, hch.base.fam, hch.base.models,
      RealDat.chain_of_weak hch.base.chain hEx, RealDat.thP_of_weak hch.base.thP hEx⟩
  have hχ : z.R.toRealDat.grp_chiW := hch.base.grp.chiW
  have ht : TieIn z.core z.R.toRealDat z.geo.κ z.geo.v₀ :=
    ⟨z.geo.fw.laws, z.geo.fw.alg_eq, z.geo.fw.kap, z.geo.fw.hv₀, z.geo.fw.chiR, z.geo.fw.x0⟩
  have hp : z.core.pb = z.R.toRealDat.C.P.pb :=
    GlobalTheory.PinsFixHalf.pb_eq_of_pins z.core z.R.toRealDat z.geo.κ z.geo.v₀ z.geo.O hC.lev z.geo.fw.laws z.geo.pins
  have hx := GlobalTheory.T.exists_equivariant_unit_constants_goodEmbedding z.core z.R.toRealDat z.geo.κ z.geo.v₀ z.geo.O hC.lev ht hp z.geo.pins
  have hU := hIn.jUnif
  intro i σ
  exact ⟨(GlobalTheory.TiedUnif.indep_span_of_tie z.geo.fw hC.models.HW z.geo.bar hU i σ).1,
    (GlobalTheory.TiedUnif.indep_span_of_tie z.geo.fw hC.models.HW z.geo.bar hU i σ).2,
    GlobalTheory.TiedUnif.rhoIs_of_eqAt z.geo.fw hC.models.HW hC.models.gW hχ z.geo.bar z.geo.rhoGeo hU i σ
      (fun h hV => z.geo.equivAll i _ h hV (hx i _ h hV))
      fun h hV => z.geo.equivAll i _ (good_resC z.core h) hV (hx i _ (good_resC z.core h) hV)⟩

end GlobalTheory.Mem.Top.Bl
