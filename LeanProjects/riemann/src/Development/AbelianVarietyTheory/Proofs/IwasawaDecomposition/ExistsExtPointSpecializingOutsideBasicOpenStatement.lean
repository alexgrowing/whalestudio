import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExtPointSpecializingOutsideBasicOpen
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ext_point_specializing_outside_basicOpen : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (N : TrueGeo.Model Y) (W : N.X.Opens) (z : N.X) (g : Γ(N.X, W)), z ∈ W → g ≠ 0 → z ∉ N.X.basicOpen g → ∃ (v : HeightOneSpectrum (𝓞 F)) (e : Ext v) (y : AlgPt Y) (yt : Sp e.O ⟶ N.X), spMap e.O.subtype ≫ yt = y.1 ≫ N.j ∧ ⊤ ≤ yt ⁻¹ᵁ W ∧ yt (IsLocalRing.closedPoint e.O) ∉ N.X.basicOpen g ∧ N.j (below y.1) ∈ N.X.basicOpen g := by
  first | exact @GlobalTheory.TrueGeo.HorizPt.main | exact GlobalTheory.TrueGeo.HorizPt.main | (intros; apply GlobalTheory.TrueGeo.HorizPt.main <;> assumption)
