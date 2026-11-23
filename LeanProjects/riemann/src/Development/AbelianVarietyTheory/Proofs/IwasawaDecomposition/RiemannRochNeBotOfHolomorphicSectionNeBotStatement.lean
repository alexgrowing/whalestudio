import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RiemannRochNeBotOfHolomorphicSectionNeBot
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Matrix CategoryTheory.Obj Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.H0_ne_bot_of_holSec_ne_bot : ∀ (F : Type) [Field F] (Y : GlobalTheory.ProjVar.Var F) (σ : F →+* ℂ) (R : AnRead Y.str σ Y.dim) (D : Y.Dv), R.holSec (Y.lb D) ≠ ⊥ → Y.H0 D ≠ ⊥ := by
  first | exact @GlobalTheory.ShFam.Hor.riemannRoch_ne_bot_of_holomorphicSection_ne_bot | exact GlobalTheory.ShFam.Hor.riemannRoch_ne_bot_of_holomorphicSection_ne_bot | (intros; apply GlobalTheory.ShFam.Hor.riemannRoch_ne_bot_of_holomorphicSection_ne_bot <;> assumption)
