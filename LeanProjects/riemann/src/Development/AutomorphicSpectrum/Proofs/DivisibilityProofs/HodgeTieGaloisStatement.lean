import Mathlib
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.HodgeTieGalois
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpPair
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
import Development.AutomorphicSpectrum.Statements.GeometryStatements.PadicIntegersHenselianFiniteResidue
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
open MvPolynomial AlgebraicGeometry CategoryTheory NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (IsPullHerm imageZ blockFnField)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_tie_galois : CmpPair → TwistAut → ∀ (II : IntersectionSystem), IsFullIntersectionSystem II → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [DecidableEq (CMType H)] (T : Top.RootTower (CMType H) (D.p + D.q)) (S : ℕ → Finset ℕ) (n : ℕ) (tie : ∀ B k, HodgeTie Y (S B) n (T.M B k)), IsGalois ℚ E → Mono (spMap β) → T.Conv II → (∀ B k k', ∀ p ∈ S B, (tie B k').A.R p = (tie B k).A.R p) → (∀ (B : ℕ) (Φ : Xo.X ≅ Xo.X), Φ.hom ≫ Xo.s = Xo.s → ∃ π : Equiv.Perm T.Comp, ∀ k, IsImageCpt Φ (tie B k).A (tie B (π k)).A) → T.PropA II := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cmp.HodgeA.propA_of_hodgeTower | exact GlobalTheory.CompanionTheory.Ar.Cmp.HodgeA.propA_of_hodgeTower | (intros; apply GlobalTheory.CompanionTheory.Ar.Cmp.HodgeA.propA_of_hodgeTower <;> assumption)
