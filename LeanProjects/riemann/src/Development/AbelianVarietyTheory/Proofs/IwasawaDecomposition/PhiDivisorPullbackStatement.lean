import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PhiDivisorPullback
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.phi_divisor_pullback : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O O' : Type) [CommRing O] [CommRing O'] (β : O →+* c.F) (β' : O' →+* c.F) (X : Model Xo c β) (Z : Model Xo c β') (π : Z.X ⟶ X.X) (ψ : InvFun (𝓞 E)) (DX : GlobalTheory.EffCartierData X.X) (h : DX.KeepsRegular π), Z.j ≫ π = X.j → Nonempty (SABMap Z.t X.t π) → IsPhiDiv ψ X DX → IsPhiDiv ψ Z (DX.pull π h) := by
  first | exact @GlobalTheory.TorRef.isPhiDiv_pull | exact GlobalTheory.TorRef.isPhiDiv_pull | (intros; apply GlobalTheory.TorRef.isPhiDiv_pull <;> assumption)
