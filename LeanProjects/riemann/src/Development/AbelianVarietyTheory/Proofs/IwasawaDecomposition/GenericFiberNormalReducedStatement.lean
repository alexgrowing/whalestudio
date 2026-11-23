import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GenericFiberNormalReduced
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_fiber_normal_reduced : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)),
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (gen Y) ∧ IsReduced (gen Y) ∧ IsLocallyNoetherian (gen Y) := by
  first | exact @GlobalTheory.GenFibre.gen_normal_reduced_noetherian | exact GlobalTheory.GenFibre.gen_normal_reduced_noetherian | (intros; apply GlobalTheory.GenFibre.gen_normal_reduced_noetherian <;> assumption)
