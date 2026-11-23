import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveICRows
import Development.AbelianVarietyTheory.Definitions.Divisors.TieTest
import Formalism.LocalToGlobal.IndefiniteReal.CxLemmas
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2 Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Indef Formalism.IndefR.Cx GlobalTheory.BigTop GlobalTheory.BigTop.Fun
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.injective_iC_rows : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), p.Rows → Function.Injective ((p.R.toCx3 p.F).iC p.F.cr false p.P.A3.fam3.base3.μ0) ∧ ∀ (t : Tup p) (y : Fin ((Df p).dQ t) → D.what₂.LL), (p.R.toCx3 p.F).iC p.F.cr false p.P.A3.fam3.base3.μ0 (cpt p.P.A3.fam3.base3.v0.embedding (((p.S false).ι t).mulVec y)) = (p.R.toCx3 p.F).iC p.F.cr false t (cpt p.P.A3.fam3.base3.v0.embedding y) := by
  first | exact @GlobalTheory.BigTop.Fun.iC_base_factor_of_rows | exact GlobalTheory.BigTop.Fun.iC_base_factor_of_rows | (intros; apply GlobalTheory.BigTop.Fun.iC_base_factor_of_rows <;> assumption)
