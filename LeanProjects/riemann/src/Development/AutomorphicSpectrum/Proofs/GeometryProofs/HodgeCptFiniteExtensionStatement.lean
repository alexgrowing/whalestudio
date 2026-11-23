import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptFiniteExtension
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.TwTan
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_cpt_finite_extension : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω Ω' : Type) [Field Ω] [Field Ω'] (i : Ω →+* Ω') (K K' : Type) [Fintype K] [Fintype K'] (J : K → Type) (J' : K' → Type) [∀ k, Fintype (J k)] [∀ k, Fintype (J' k)] (y : (Σ k, J k) → Ω) (y' : (Σ k, J' k) → Ω') (A : HodgeCpt Y S y) (A' : HodgeCpt Y S y') (h : A'.X ⟶ A.X) (j : A.Li →+ A'.Li) (m : SABMap A'.t A.t h) (κ : K → K') (v : (Σ k, J k) → (Σ k, J' k)) (Fl : A.Flag), AI.I1.IsBlockMap κ v → (∀ q, y' (v q) = i (y q)) → GlobalTheory.CompanionTheory.Ar.Dominates A'.ξ A.ξ h i → A'.f = h ≫ A.f → A'.m.φ = m.φ ≫ A.m.φ → A'.cst = i.comp A.cst → IsExtOver i j → (∀ w, (A'.M.pt (j w)).left ≫ m.φ = spMap (dualMap i) ≫ (A.M.pt w).left) → (∀ s, A'.V s = (A.V s).pull A'.ξ h j) → ∀ Fl' : A'.Flag, (∀ s k, Fl'.b s k = j (Fl.b s k)) → ∀ r (e₀ : Ω) (L : HermLine J) (L' : HermLine J'), Fl.IsHodgeLine r e₀ L → AI.I4.IsPullHerm κ v L L' → Fl'.IsHodgeLine r (i e₀) L' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HodgePull.hodgeLine_pull | exact GlobalTheory.CompanionTheory.Ar.HodgePull.hodgeLine_pull | (intros; apply GlobalTheory.CompanionTheory.Ar.HodgePull.hodgeLine_pull <;> assumption)
