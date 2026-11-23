import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTiesDistinctGeneric
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpPair
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
import Development.AutomorphicSpectrum.Statements.GeometryStatements.PadicIntegersHenselianFiniteResidue
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
open MvPolynomial AlgebraicGeometry CategoryTheory NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (IsPullHerm imageZ blockFnField)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_ties_distinct_generic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (n : ℕ) (C : Type) [Fintype C] (M : C → Top.RootModel (CMType H) (D.p + D.q)) (tie : ∀ k, HodgeTie Y S n (M k)), Mono (spMap β) → Function.Injective (fun k => genPt (tie k).A.ξ₀) → (∀ q : Y.X, (∀ q' : Y.X, q' ⤳ q → q' = q) → ∃ k, genPt (tie k).A.ξ₀ = q) → ∀ Φ : Xo.X ≅ Xo.X, Φ.hom ≫ Xo.s = Xo.s → ∃ π : Equiv.Perm C, ∀ k, IsImageCpt Φ (tie k).A (tie (π k)).A := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cmp.PermCpt.exists_perm_isImageCpt | exact GlobalTheory.CompanionTheory.Ar.Cmp.PermCpt.exists_perm_isImageCpt | (intros; apply GlobalTheory.CompanionTheory.Ar.Cmp.PermCpt.exists_perm_isImageCpt <;> assumption)
