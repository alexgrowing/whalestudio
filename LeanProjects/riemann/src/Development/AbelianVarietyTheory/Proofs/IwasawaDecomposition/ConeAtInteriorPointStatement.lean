import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConeAtInteriorPoint
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasConesIff
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coneAt_interior_point : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} (φ : InvFun (𝓞 E)) (Y : Model Xo c (RingHom.id c.F)) (w : Xo.XF c), GlobalTheory.GenFan.ConeAt (ConeO H φ) Y (Y.j w) := by
  first | exact @GlobalTheory.GenFan.coneAt_j | exact GlobalTheory.GenFan.coneAt_j | (intros; apply GlobalTheory.GenFan.coneAt_j <;> assumption)
