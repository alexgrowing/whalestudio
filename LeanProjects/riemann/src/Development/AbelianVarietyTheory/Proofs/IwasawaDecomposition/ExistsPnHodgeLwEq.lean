import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLUBRangeOfMatch
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAutomorphismOrthogonalPointStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagComponentFramePointRelationStatement
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.TrueGeo GlobalTheory.ShFam.Pad GlobalTheory.ProjVar GlobalTheory.ProjVar.Var GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.DeKeyTrue GlobalTheory.Toroidal

noncomputable section

open CategoryTheory

namespace GlobalTheory.ShFam.DeKeyTrue

theorem pn_cast_met {D : D7} {Y : GlobalTheory.ProjVar.Var D.what₂.LL} {σ : D.what₂.LL →+* ℂ} {Δ Δ' : Y.Dv} (e : Δ = Δ')
    (m : (cxSt D.what₂.LL).Met Y σ Δ) (f : (cxSt D.what₂.LL).FnC Y σ) (p : Y.pts σ) :
    (geoTrue D.what₂.LL).pn Y σ Δ' (e ▸ m) f p = (cxSt D.what₂.LL).pn Y σ Δ m f p := by
  subst e; rfl

end GlobalTheory.ShFam.DeKeyTrue
