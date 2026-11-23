import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.InteriorPointLatticeData
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
import Development.AutomorphicSpectrum.Statements.GeometryStatements.NineGeoU
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.interior_point_lattice_data : ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (z : Sp ℂ ⟶ 𝔐.X), 1 ≤ D.p + D.q → 𝔐.Interior z → Top.Given → ∀ (A₀ : Type) (v : A₀ → (epsAt z ⟶ 𝔐.t.G)), (∀ i, IsTanAt 𝔐.t.G z (v i)) → ∃ (g : ℕ) (Λ : Type) (_ : AddCommGroup Λ) (_ : Module (𝓞 E) Λ) (R : RiemLat E g Λ) (x : A₀ → Fin g → ℂ), FibreLatVec 𝔐.t z R x v ∧ (∀ i j, HodgeIP 𝔐.t.G 𝔐.t.PP.L z (v i) (v j) (Real.pi * R.ip (x i) (x j))) ∧ ∀ σ, 𝔐.LabVal z id σ → ∀ s, Module.finrank ℂ (eigSp R.B (σ s)) = labelRk D s := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.FibreEx.exists_riemLat_of_interior | exact GlobalTheory.CompanionTheory.Ar.Cusp.FibreEx.exists_riemLat_of_interior | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.FibreEx.exists_riemLat_of_interior <;> assumption)
