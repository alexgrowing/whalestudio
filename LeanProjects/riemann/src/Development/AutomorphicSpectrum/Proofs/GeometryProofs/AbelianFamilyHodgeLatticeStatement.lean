import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianFamilyHodgeLattice
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
import Development.AutomorphicSpectrum.Statements.GeometryStatements.NineGeoU
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelian_family_hodge_lattice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (R : Type) [CommRing R] (t : SAB H (Sp R)) (jj : Sp R ⟶ 𝔐.X) (m : SABMap t 𝔐.t jj) (g n : ℕ) (M : LieModel t.G (𝟙 (Sp R)) (Fin g → R)) (B₀ : Set (Fin n → ℂ)) (ψ : (Fin n → ℂ) → (R →+* ℂ)) (e : Flat.FamExp t.G M B₀ ψ) (b : Fin n → ℂ) (Bb : 𝓞 E →+* Module.End ℂ (Fin g → ℂ)) (lab : CMType H ⊕ CMType H) (r : ℕ) (s : Fin r → 𝔐.Li) (sc : Fin r → Fin g → R) (σ : CMType H ⊕ CMType H → (𝓞 E →+* ℂ)), b ∈ B₀ → (∀ a' x, e.ex b (Bb a' x) = e.ex b x ≫ t.act.act a') → 𝔐.LabVal (spMap (ψ b) ≫ jj) id σ → (∀ h : genPt 𝔐.ξ ⤳ centre (spMap (ψ b) ≫ jj), (𝔐.V lab).IsFrameAt s ⟨centre (spMap (ψ b) ≫ jj), h⟩) → (∀ i, ∃ v : epsAt (spMap (ψ b) ≫ jj) ⟶ 𝔐.t.G, 𝔐.M.ValAt (spMap (ψ b) ≫ jj) (s i) v ∧ v.left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap (ψ b)) ≫ (M.pt (sc i)).left ≫ m.φ) → LinearIndependent ℂ (fun i k => ψ b (sc i k)) ∧ Submodule.span ℂ (Set.range fun i k => ψ b (sc i k)) = eigSp Bb (σ lab) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.ChartEig.values_eig | exact GlobalTheory.CompanionTheory.Ar.Cusp.ChartEig.values_eig | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.ChartEig.values_eig <;> assumption)
