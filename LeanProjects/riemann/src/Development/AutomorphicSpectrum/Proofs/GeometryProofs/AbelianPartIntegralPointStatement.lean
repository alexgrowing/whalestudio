import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianPartIntegralPoint
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
import Development.AutomorphicSpectrum.Statements.GeometryStatements.NineGeoU
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelian_part_integral_point : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (L : Type) [Field L] [NumberField L] (z : Sp (𝓞 L) ⟶ 𝔐.X) (P : AbPart 𝔐.t (spMap (algebraMap (𝓞 L) L) ≫ z)) (V : Type) [AddCommGroup V] [Module L V] [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] (MV : LieModel P.tK.G (𝟙 (Sp L)) V) (A : LinPt E L (CMType H) V), 1 ≤ D.p + D.q → (∀ r : ℕ, r.Prime → (r : ℤ) ∣ discr E → r ∈ S) → (∀ p ∈ S, HT.HTFree 𝔐 p) → 𝔐.IsLinPtOf z P MV A → ∀ s, ∃ 𝔞 : Ideal (𝓞 L), 𝔞 ≠ ⊥ ∧ 𝔞 • 𝔐.FibLat (𝔐.V s) z P MV ≤ A.eig s ∧ 𝔞 • A.eig s ≤ 𝔐.FibLat (𝔐.V s) z P MV ∧ Real.log (Ideal.absNorm 𝔞) / Module.finrank ℚ L ≤ 2 * (∑ p ∈ S, Real.log (p : ℝ) / ((p : ℝ) - 1)) + 2 * Real.log (hostRd E) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.abelian_part_integral_point | exact GlobalTheory.CompanionTheory.Relay.abelian_part_integral_point | (intros; apply GlobalTheory.CompanionTheory.Relay.abelian_part_integral_point <;> assumption)
