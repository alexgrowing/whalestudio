import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PhiDivisorAdd
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.phi_divisor_add : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (φ₁ φ₂ : InvFun (𝓞 E)) (D₁ D₂ : GlobalTheory.EffCartierData Z.X), IsPhiDiv φ₁ Z D₁ → IsPhiDiv φ₂ Z D₂ → IsPhiDiv (comb 1 φ₁ 1 φ₂) Z (D₁.add D₂) := by
  first | exact @GlobalTheory.TorRef.AddDiv.isPhiDiv_add | exact GlobalTheory.TorRef.AddDiv.isPhiDiv_add | (intros; apply GlobalTheory.TorRef.AddDiv.isPhiDiv_add <;> assumption)
