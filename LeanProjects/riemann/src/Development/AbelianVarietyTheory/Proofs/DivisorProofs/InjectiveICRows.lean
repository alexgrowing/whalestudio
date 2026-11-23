import Development.AbelianVarietyTheory.Definitions.Divisors.TieTest
import Formalism.LocalToGlobal.IndefiniteReal.CxLemmas
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2 Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Indef Formalism.IndefR.Cx GlobalTheory.BigTop GlobalTheory.BigTop.Fun
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.BigTop.Fun

theorem iC_base_factor_of_rows : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), p.Rows → Function.Injective ((p.R.toCx3 p.F).iC p.F.cr false p.P.A3.fam3.base3.μ0) ∧ ∀ (t : Tup p) (y : Fin ((Df p).dQ t) → D.what₂.LL), (p.R.toCx3 p.F).iC p.F.cr false p.P.A3.fam3.base3.μ0 (cpt p.P.A3.fam3.base3.v0.embedding (((p.S false).ι t).mulVec y)) = (p.R.toCx3 p.F).iC p.F.cr false t (cpt p.P.A3.fam3.base3.v0.embedding y) := by
  intro D L hT Gi Gl Kc Y cX ex Csz p hp
  have hCx := Formalism.IndefR.Links.complex_data_conditions_base_level_of_primitive_links hp.ok hp.sep p.charW hp.prim
  have h2 := (hCx.what₂ false).1
  have hr := hCx.ratMu false
  refine ⟨h2.1, fun t y => ?_⟩
  have hspec := relMat_spec ((p.R.toCx3 p.F).iC p.F.cr false p.P.A3.fam3.base3.μ0)
    ((p.R.toCx3 p.F).iC p.F.cr false t)
    (fun k => by rw [← (h2.2.1 t).2]; exact LinearMap.mem_range_self _ _)
  show (p.R.toCx3 p.F).iC p.F.cr false p.P.A3.fam3.base3.μ0
      (cpt p.P.A3.fam3.base3.v0.embedding ((kMat p.P.A3.fam3.base3.v0.embedding ((p.R.toCx3 p.F).rowMatC p.F.cr false t)).mulVec y)) = _
  rw [cpt_mulVec, kMat_map _ (hr t)]
  exact hspec _

end GlobalTheory.BigTop.Fun

end
