import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BoundaryChartHodgeMap
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
import Development.AutomorphicSpectrum.Statements.GeometryStatements.NineGeoU
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.boundary_chart_hodge_map : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (σ : KA l →+* ℂ) (n a : ℕ) (C : Flat.BdryChart Xo σ n a) (jj : Sp C.R ⟶ 𝔐.X) (m : SABMap C.t 𝔐.t jj) (B₀ : Set (Fin n → ℂ)) (e : Flat.FamExp C.t.G C.M B₀ C.ψ) (b : Fin n → ℂ) (Bb : 𝓞 E →+* Module.End ℂ (Fin C.g → ℂ)) (Hm : Matrix (Fin C.g) (Fin C.g) ℂ), 1 ≤ D.p + D.q → b ∈ B₀ → 𝔐.Interior (spMap (C.ψ b) ≫ jj) → C.IsRiem b Hm → (∀ a' x, e.ex b (Bb a' x) = e.ex b x ≫ C.t.act.act a') → ∃ (A : Over (Sp ℂ)) (_ : GrpObj A) (φ : A.left ⟶ 𝔐.t.G.left) (u : HolUnif A (𝔐.t.PP.L.pull φ) C.g) (χ : u.Λ → ℂ), IsGrpPullback A 𝔐.t.G (spMap (C.ψ b) ≫ jj) φ ∧ u.IsAH Hm χ ∧ (∀ x, (u.ex x).left ≫ φ = (e.ex b x).left ≫ m.φ) ∧ (∀ x, x ∈ u.Λ ↔ x ∈ e.per b) ∧ (∀ (x : Fin C.g → ℂ) (v : Sp (DualNumber ℂ) ⟶ C.t.G.left), IsDerivAt0 (fun x => (e.ex b x).left) x v → ∃ v' : epsR ℂ ⟶ A, v'.left ≫ φ = v ≫ m.φ ∧ u.IsDiff x v') ∧ ∀ a' a'' : 𝓞 E, (a'' : E) = IsCMField.complexConj E (a' : E) → ∀ x x', hermForm Hm (Bb a' x) x' = hermForm Hm x (Bb a'' x') := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.ChartUnif.exists_unif_of_interior | exact GlobalTheory.CompanionTheory.Ar.Cusp.ChartUnif.exists_unif_of_interior | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.ChartUnif.exists_unif_of_interior <;> assumption)
