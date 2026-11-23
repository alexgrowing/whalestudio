import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntertwinersAndLiftsExistAtChoicesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvInjOfIsModelsOfTie
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JEvExistsAndJEvBar
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GeoAct
import Formalism.LocalToGlobal.IndefiniteReal.RealTB
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FireAtRealisation

theorem fire : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (Rc : Formalism.L2.RecT ex) (P : RowSideFamily ex) (Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)) (Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)) (Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3) (S : Formalism.L2.SG.SpectralTiesReal.STiesR Rc) (B : RealTB Rc P Dcf Spf Zscf S), B.Q.Rl.toRealDat.ExAt ∧ JEvBar B.T B.Q.Rl.toRealDat B.κ ∧ GeoAct B.T B.Q.Rl.toRealDat B.κ B.v₀ ∧ EvInj B.T B.Q.Rl.toRealDat B.v₀ := by
  intro h1 h2 h3 h4 D L hT Gi Gl K Y cX ex Rc P Dcf Spf Zscf S B
  have c := B.Q.charW.base
  exact ⟨GlobalTheory.T.intertwinersAndLifts_exist_at_choices h1 h2 h3 h4 D _ _ _ _ _ _ c.lev c.fam c.models c.grp.record B.Q.host c.chain c.thP,
    GlobalTheory.ConjReading.jEvBar B.T _ B.κ B.v₀ B.O c.lev c.models B.fw B.pins,
    GlobalTheory.GeometricAction.geoAct B.T _ B.κ B.v₀ B.O c.lev c.models B.fw B.pins B.equivAll,
    GlobalTheory.EvalAtUnitVectorFinal.evInj_of_isModels_of_tie B.T _ B.κ B.v₀ c.models B.fw⟩

end GlobalTheory.FireAtRealisation
