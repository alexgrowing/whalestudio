import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeometricHalfCoreFormsUniformisationIntegral

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TieMK

theorem act_mem_MK : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz), p.Rows → GlobalTheory.CovTop.RecTied D L →
    ∀ (i : Fin D.R.m) (g : p.P.Gp) f, f ∈ (p.R.toRealDat.FW i).MK → (p.R.toRealDat.FW i).ρ g f ∈ (p.R.toRealDat.FW i).MK := by
  intro D L hT Gi Gl Kc Y0 cX ex Csz p _ _ i g f hf
  exact ((GlobalTheory.RealGeoIn.mkStable_of_rhoGeo p.fw p.pins p.rhoGeo i) g f).2 hf

end GlobalTheory.TieMK
