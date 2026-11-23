import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsIsoFiniteBirationalNormal
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIso_finite_birational_normal : ∀ (V S T : Scheme.{0}) (e : S ⟶ T) (jS : V ⟶ S) (jT : V ⟶ T), IsFinite e → IsReduced S →
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme T → IsLocallyNoetherian T → IsOpenImmersion jS → IsOpenImmersion jT →
    jS ≫ e = jT → Dense (Set.range jS) → Dense (Set.range jT) → e ⁻¹' Set.range jT = Set.range jS → IsIso e := by
  first | exact @GlobalTheory.FiniteBirationalIso.main | exact GlobalTheory.FiniteBirationalIso.main | (intros; apply GlobalTheory.FiniteBirationalIso.main <;> assumption)
