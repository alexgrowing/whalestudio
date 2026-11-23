import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsEffectiveWeightSection
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatLineGenerator
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CardComapMulFinsumEqFinsumFibres
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_effective_weight_section : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)), Top.IsGlobal Xo l c Y → 1 ≤ D.p → 1 ≤ D.q → ∀ (G : RefGeo Y), Nonempty G.An → ∀ ν : RootIx D → ℤ, (∀ τ (i k : Fin (D.p + D.q)), i < k → ν (τ, k) < ν (τ, i)) → ∃ (k q' : ℕ) (s : G.Ω), 0 < k ∧ 0 < q' ∧ s ≠ 0 ∧ G.IsEff (fun r => (k * q' : ℕ) * ν r) q' s := by
  first | exact @GlobalTheory.CompanionTheory.Ar.ExRefEff.exists_eff | exact GlobalTheory.CompanionTheory.Ar.ExRefEff.exists_eff | (intros; apply GlobalTheory.CompanionTheory.Ar.ExRefEff.exists_eff <;> assumption)
