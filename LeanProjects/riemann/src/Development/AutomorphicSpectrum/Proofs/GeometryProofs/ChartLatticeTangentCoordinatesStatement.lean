import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChartLatticeTangentCoordinates
import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ContDiffUncentre
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_lattice_tangent_coordinates : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (n a : ℕ) (C : Flat.BdryChart Xo σ n a) (X : Scheme.{0}) (t : SAB H X) (h : Sp C.R ⟶ X) (m : SABMap C.t t h) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel t.G ξ Li) (N : ℕ) (b : Fin N → Li) (x : Fin N → Fin C.g → C.R) (z : Fin n → ℂ) (Hm : Matrix (Fin C.g) (Fin C.g) ℂ) (w : Fin N → (epsAt (spMap (C.ψ z) ≫ h) ⟶ t.G)), C.IsRiem z Hm → (∀ k, M.ValAt _ (b k) (w k)) → (∀ k, (w k).left = spMap (dualMap (C.ψ z)) ≫ (C.M.pt (x k)).left ≫ m.φ) → M.GramAt t.PP.L (spMap (C.ψ z) ≫ h) b (Matrix.of fun i j => (Real.pi : ℂ) * ((fun e => C.ψ z (x j e)) ⬝ᵥ Hm *ᵥ star (fun e => C.ψ z (x i e)))) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.RiemGram.gramAt_of_isRiem | exact GlobalTheory.CompanionTheory.Ar.RiemGram.gramAt_of_isRiem | (intros; apply GlobalTheory.CompanionTheory.Ar.RiemGram.gramAt_of_isRiem <;> assumption)
