import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsZeroOfInvOfNotRegularNormal
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_zero_of_inv_of_not_regular_normal : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → ∀ (x : X) (f : X.functionField), ¬ RegAt x f → ∃ z : X, z ⤳ x ∧ ZeroAt z f⁻¹ := by
  first | exact @GlobalTheory.NormalPole.exists_zeroAt_inv | exact GlobalTheory.NormalPole.exists_zeroAt_inv | (intros; apply GlobalTheory.NormalPole.exists_zeroAt_inv <;> assumption)
