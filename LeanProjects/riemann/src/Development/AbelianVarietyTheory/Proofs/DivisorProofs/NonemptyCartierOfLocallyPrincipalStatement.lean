import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyCartierOfLocallyPrincipal
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyCuspFrame
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_cartier_of_locally_principal' : ∀ (Y : Scheme.{0}) (I : Y.IdealSheafData), (∀ y : Y, ∃ (W : Y.affineOpens) (a : Γ(Y, W.1)), y ∈ W.1 ∧ a ∈ nonZeroDivisors Γ(Y, W.1) ∧ I.ideal W = Ideal.span {a}) → Nonempty (Cartier I) := by
  first | exact @GlobalTheory.CompHS.nonempty_cartier_of_locally_principal | exact GlobalTheory.CompHS.nonempty_cartier_of_locally_principal | (intros; apply GlobalTheory.CompHS.nonempty_cartier_of_locally_principal <;> assumption)
