import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagSpaceComponentSmoothProjectiveConnected
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyCuspFrame
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagSpace_component_smooth_projective_connected : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed Xo c → IsVariety₀ T.X Z := by
  first | exact @GlobalTheory.VarFlag.isVariety₀_flag | exact GlobalTheory.VarFlag.isVariety₀_flag | (intros; apply GlobalTheory.VarFlag.isVariety₀_flag <;> assumption)
