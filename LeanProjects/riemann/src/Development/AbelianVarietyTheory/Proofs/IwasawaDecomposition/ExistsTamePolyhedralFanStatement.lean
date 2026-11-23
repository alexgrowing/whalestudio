import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTamePolyhedralFan
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SiegelAtOfKnownTheorem
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tame_polyhedral_fan : ∀ (g : ℕ) (φ : InvFun ℤ), IsPolFan id g φ → ∃ φs : InvFun ℤ, IsPolFan id g φs ∧ IsTame φs ∧ AgreesPsd g φs φ := by
  first | exact @GlobalTheory.PolFan.TameZ.exists_tame | exact GlobalTheory.PolFan.TameZ.exists_tame | (intros; apply GlobalTheory.PolFan.TameZ.exists_tame <;> assumption)
