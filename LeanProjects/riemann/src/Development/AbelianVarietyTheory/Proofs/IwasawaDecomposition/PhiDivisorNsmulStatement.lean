import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PhiDivisorNsmul
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.phi_divisor_nsmul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (φ : InvFun (𝓞 E)) (D₁ : GlobalTheory.EffCartierData Z.X) (n : ℕ), IsPhiDiv φ Z D₁ → IsPhiDiv (comb n φ 0 φ) Z (D₁.nsmul n) := by
  first | exact @GlobalTheory.TorRef.PhiNsmul.isPhiDiv_nsmul_self | exact GlobalTheory.TorRef.PhiNsmul.isPhiDiv_nsmul_self | (intros; apply GlobalTheory.TorRef.PhiNsmul.isPhiDiv_nsmul_self <;> assumption)
