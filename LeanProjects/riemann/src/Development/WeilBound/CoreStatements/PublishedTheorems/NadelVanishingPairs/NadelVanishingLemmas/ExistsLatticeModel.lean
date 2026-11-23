import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CechFam
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.FiniteCohPushforwardIffOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSubsingletonCohTwistTensLbPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLatticeModel
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.LogDR

theorem _root_.GlobalTheory.T.exists_lattice_model : ∀ (X : Scheme.{0}) [IsIntegral X] {V : Type} [AddCommGroup V] [Module X.functionField V] (M : X → AddSubgroup V), (∀ y (f : X.functionField) (v : V), RegAt y f → v ∈ M y → f • v ∈ M y) → ∃ F : X.Modules, Nonempty (LatModel M F) := by
  first | exact @_root_.GlobalTheory.LogDR.exists_latModel | exact _root_.GlobalTheory.LogDR.exists_latModel | (intros; apply _root_.GlobalTheory.LogDR.exists_latModel <;> assumption)
