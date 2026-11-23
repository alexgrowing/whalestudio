import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormalNoetherianGenericFiber
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normal_noetherian_generic_fiber : ∀ (R K : Type) [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K] (N : Scheme.{0}) (g : N ⟶ Sp R),
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme N → IsLocallyNoetherian N →
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (pullback g (spMap (algebraMap R K))) ∧
      IsLocallyNoetherian (pullback g (spMap (algebraMap R K))) := by
  first | exact @GlobalTheory.GenFibre.normal_genericFibre | exact GlobalTheory.GenFibre.normal_genericFibre | (intros; apply GlobalTheory.GenFibre.normal_genericFibre <;> assumption)
