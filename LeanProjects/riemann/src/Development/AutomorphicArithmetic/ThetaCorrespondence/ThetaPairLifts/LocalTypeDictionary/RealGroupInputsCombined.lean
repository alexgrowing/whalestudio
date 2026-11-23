import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RealGroupInputsCombined
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedMultiplicityOne
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RealGroupInputsCombinedStatement

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Fc.RL.LamLinked
set_option maxHeartbeats 2000000 in
theorem isotRank_of_wit_alt (h1 : GlobalTheory.Published.WeilRepresentationUnitaryPair) (h2 : GlobalTheory.Published.DiscreteSeriesExists)
    (h3 : GlobalTheory.Published.HarishChandraFinite) (h4 : GlobalTheory.Published.CuspRapidDecay)
    (a1 : GlobalTheory.Published.HarishChandraAnalyticity) (a2 : GlobalTheory.Published.DiscreteSeriesClassification) (a5 : GlobalTheory.Published.CuspTraceClass)
    (a6 : GlobalTheory.Published.DixmierMalliavinFactorisation) (a7 : GlobalTheory.Published.FlathFactorisation)
    (a12 : GlobalTheory.Published.ZelevinskyPolynomialRing) (a13 : GlobalTheory.Published.GeometricLemma) (hG : GlobalTheory.Published.GreenCuspidal)
    {𝒮 : Slots} {K : Ctx} (q : WPt 𝒮 K) (hH : Formalism.IndefR.Links.HostHyp (q.w.st q.Z).toD7)
    (hp : ∃ L : SizeData₂ (q.w.st q.Z).toD7, Nonempty (ParameterChoice' (q.w.st q.Z).toD7 L)) :
    Formalism.BasicNotions.Rows.IsotRank (q.w.st q.Z).toD7.what₂ := by
  have hGS : Formalism.L2.DIV.GoodStable q.x.what₂.r.z.Xg := by
    have hI := GlobalTheory.DimPartsCompare.TameTie.idemTie hG
      (GlobalTheory.DimPartsCompare.tameTie_of_typesTrue (D := (q.w.st q.Z).toD7) q.x.what₂.grp).2.1
    refine GlobalTheory.Mem.R3.GoodDual.goodStable_of_coeff (q.w.st q.Z).B.embLL q.x.what₂.r.z.Xg q.x.what₂.r.z.good.irr fun g => ?_
    apply (q.w.st q.Z).B.embLL.injective
    rw [q.x.what₂.r.z.good.2, q.x.what₂.r.z.good.2, map_inv, GlobalTheory.Mem.R3.GoodDual.goodIdempotent_coeff_inv_eq_coeff hI]
  have hT : TypesTrue (q.w.st q.Z).toD7.ntypes q.x.what₂.r.z.R.C.P q.x.what₂.r.z.R.C.W := by
    rw [q.x.what₂.r.z.lev.C, q.w.C_eq]
    exact q.x.what₂.grp
  have hME := _root_.GlobalTheory.T.twisted_multiplicity_one a1 a2 h4 h3 a5 a6 a7 a12 a13 hG q.x.what₂.r.z.R q.x.what₂.r.z.F q.x.what₂.r.intersectionNumber_baseChange.ok
    q.x.what₂.r.z.pins.char q.x.what₂.exAt hH hp q.B.ccK_top q.x.what₂.r.z.pins.keep.guard
    (GlobalTheory.LiftRows.Inh.goodTypes_of_typesTrue q.x.what₂.r.z.pins.char.base.lev hT)
  exact GlobalTheory.Mem.R3.isotRank_of_multEq h1 h2 h3 h4 _ _ _ _ _ _ _ q.x.what₂.r.z.R q.x.what₂.r.z.F q.x.what₂.r.z.cG _ q.x.what₂.r.Y q.x.what₂.r.z.pins
    q.x.what₂.r.intersectionNumber_baseChange hH hGS (GlobalTheory.CuspDec.cuspDecomp h3 h4 _) hME
end GlobalTheory.Fc.RL.LamLinked
namespace GlobalTheory.Fc.RL
end GlobalTheory.Fc.RL
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
end
