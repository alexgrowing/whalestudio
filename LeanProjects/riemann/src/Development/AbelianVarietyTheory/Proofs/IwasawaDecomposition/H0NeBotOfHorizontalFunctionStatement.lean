import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.H0NeBotOfHorizontalFunction
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Matrix CategoryTheory.Obj Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.H0_divOf_ne_bot_of_horFn : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (F : Type) [Field F] [NumberField F] (e : F ≃+* c.F) (C : FlagCpt Z e) (τ : E →+* ℂ) (h : CxFr Z σ → ℂ), τ (H.rt : E) = H.rt0 → HorFn τ h → (C.Y.H0 (divOf C (expo Dw (detSym Dw (fun _ => false) none τ))) ≠ ⊥ ∧ C.Y.H0 (-divOf C (expo Dw (detSym Dw (fun _ => false) none τ))) ≠ ⊥) := by
  first | exact @GlobalTheory.ShFam.Hor.Sec.H0_ne_bot_of_horFn | exact GlobalTheory.ShFam.Hor.Sec.H0_ne_bot_of_horFn | (intros; apply GlobalTheory.ShFam.Hor.Sec.H0_ne_bot_of_horFn <;> assumption)
