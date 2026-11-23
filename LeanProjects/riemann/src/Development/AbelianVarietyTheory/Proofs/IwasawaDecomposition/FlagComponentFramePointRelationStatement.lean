import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagComponentFramePointRelation
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLUBRangeOfMatch
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigenframeGenericAffineOpen
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.TrueGeo GlobalTheory.ShFam.Pad GlobalTheory.ProjVar GlobalTheory.ProjVar.Var GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.DeKeyTrue GlobalTheory.Toroidal
open CategoryTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_component_frame_point_relation : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β} {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} (C : FlagCpt Z e) {σ : F →+* ℂ} {σ' : c.F →+* ℂ} (ψ : ℂ →+* ℂ) (p : C.Y.pts σ) (g : C.FrameAt p) (y : FrPt Xo c (CAt σ')) (ex : Ix Dw → ℤ) (h : Rul Xo c), ψ.comp ψ = RingHom.id ℂ → σ' = ψ.comp (GlobalTheory.ShFam.embOf e σ) → C.Carries p.1 g → (C.down p).1 = spMap ψ ≫ (cxPt Z y).1 → (cxFrame Z y).IsMap ψ g → ex none = 0 → h ∈ GlobalTheory.AllWt.secZ Xo c ex → IsCoord C p.1 g (fun z => -ex (some z)) (C.val h) (ψ (Formalism.L2.PjFree.toC (evR Xo c h y))) := by
  first | exact @GlobalTheory.ShFam.CoordLift.isCoord_val | exact GlobalTheory.ShFam.CoordLift.isCoord_val | (intros; apply GlobalTheory.ShFam.CoordLift.isCoord_val <;> assumption)
