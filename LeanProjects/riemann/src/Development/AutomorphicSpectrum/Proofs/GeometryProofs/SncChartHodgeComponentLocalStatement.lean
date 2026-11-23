import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SncChartHodgeComponentLocal
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
import Development.AutomorphicSpectrum.Statements.GeometryStatements.NineGeoU
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.snc_chart_hodge_component_local : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (n : ℕ) (Bd : Set ((Σ k, J k) → ℂ)) (χ : SncChart (mCoordIdeal y) n Bd) (t₀ : Fin n → ℂ) (cc : (k : K) → J k) (f : Ω) (I : Type) [Finite I] (s : I → 𝔐.Li) (z₀ : Sp ℂ ⟶ 𝔐.X), (∀ (z : Sp ℂ ⟶ 𝔐.X) w, CoordsAt 𝔐.ξ y z w → (w ∈ Bd ↔ ¬ 𝔐.Interior z)) → t₀ ∈ Metric.ball (0 : Fin n → ℂ) 1 → CoordsAt 𝔐.ξ y z₀ (χ.γ t₀) → InFrameDomain y cc f (χ.γ t₀) → (∀ i, ∃ v : epsAt z₀ ⟶ 𝔐.t.G, 𝔐.M.ValAt z₀ (s i) v) → ∃ (a₀ : ℕ) (π : Equiv.Perm (Fin n)) (ρ : ℝ) (σ : KA l →+* ℂ) (C : Flat.BdryChart Xo σ n a₀) (jj : Sp C.R ⟶ 𝔐.X) (m : SABMap C.t 𝔐.t jj) (sc : I → Fin C.g → C.R), 0 < ρ ∧ ∀ u ∈ Metric.ball (0 : Fin n → ℂ) 1, t₀ + (ρ : ℂ) • (u ∘ π) ∈ Metric.ball (0 : Fin n → ℂ) 1 ∧ InFrameDomain y cc f (χ.γ (t₀ + (ρ : ℂ) • (u ∘ π))) ∧ CoordsAt 𝔐.ξ y (spMap (C.ψ u) ≫ jj) (χ.γ (t₀ + (ρ : ℂ) • (u ∘ π))) ∧ (χ.γ (t₀ + (ρ : ℂ) • (u ∘ π)) ∉ Bd ↔ u ∈ Flat.punct n a₀ 1) ∧ ∀ i, ∃ v : epsAt (spMap (C.ψ u) ≫ jj) ⟶ 𝔐.t.G, 𝔐.M.ValAt (spMap (C.ψ u) ≫ jj) (s i) v ∧ v.left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap (C.ψ u)) ≫ (C.M.pt (sc i)).left ≫ m.φ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SncBdry.exists_bdryChart_at | exact GlobalTheory.CompanionTheory.Ar.SncBdry.exists_bdryChart_at | (intros; apply GlobalTheory.CompanionTheory.Ar.SncBdry.exists_bdryChart_at <;> assumption)
