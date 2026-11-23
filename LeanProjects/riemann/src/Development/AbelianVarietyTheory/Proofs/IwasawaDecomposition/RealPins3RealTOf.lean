import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TwArgs
import Formalism.LocalToGlobal.IndefiniteReal.NonzeroIndexPlaceIndepConstants
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ComplexSidePlacesIffMemNonzeroIndexPlaces
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.Mem.R3

set_option maxHeartbeats 4000000 in

theorem realPins3_realTOf : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl) (L : SizeData₂ (w.st Z).toD7) (hT : GatTies (w.st Z).toD7) (Gi : Formalism.MainNotions.G.Inst (w.st Z).toD7 L) (Gl : Formalism.MainNotions.G.LatInst (w.st Z).toD7) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX (w.st Z).toD7) (cX : ExtraC) (ex : Extra (w.st Z).toD7 L hT Gi Gl Kc Yd cX) (t : RowsT K w Z Wt ex.p0) (a : TwArgs ex t) (Rc : Formalism.L2.RecT ex) (S : Formalism.L2.SG.SpectralTiesReal.STiesR Rc) (y : RealIn a.x Rc S), HEq (a.Zsc (zsOf t.r.z.R t.r.z.F)).F0 (F0K K.s (w.D Z)) → RealPins3 (realTOf y) := by
  intro K B f T w Z Wt L hT Gi Gl Kc Yd cX ex t a Rc S y h
  rw [Pins3.realPins3_iff]

  have hr := t.r.z.twisted_places_eq_complex_side_of_eq_nonzero_index (F0K K.s (w.D Z)) t.exact.symm t.r.z.R.kap a.lam a.err a.Dc a.Sp a.Zsc 0 0 (eq_of_heq h)
  show ∀ v, v ∈ a.x.R.twPl ↔ (a.x.R.toCx3 a.x.F).W1 a.x.F.cr (a.x.R.num a.x.F 0 0) v
  clear y h

  obtain ⟨Dc, Sp, Zsc, lam, err, lam_eq, x, pack, _⟩ := a
  dsimp only at hr ⊢
  obtain ⟨G, grp, fin, Pl0, I0, T0, A3, core, alg, R, F, cG, _⟩ := x
  dsimp only at pack ⊢
  cases pack
  exact hr

end GlobalTheory.Mem.R3
