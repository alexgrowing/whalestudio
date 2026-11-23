import Mathlib
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AnalyticFibreIsotropicPointsInjectiveRoots
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsBaseClassLevelAdapted
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.AnChartAsm
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.analyticFibre_isotropic_points_injective_roots : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (x : Frame X.Ψ r) (L : Lt E r) (y : FrPt Xo c ℂ) (A : AnFib X bas idx e x L y), IsSympl X bas → x ∈ X.dom → SelfD X L → ∀ (n N : ℕ) (Λ : Lt E n), 0 < N → (∀ (Jx : Type) (u : Jx → Matrix (Fin n) (Fin r) E), (∀ i, u i ∈ tens Λ L ∧ ∀ b, ∃ u' ∈ L, N • u i b = (2 : ℕ) • u') → (∀ i i', (∀ b, ∃ u' ∈ L, u i b - u i' b = N • u') → i = i') → (∀ i, InZh Xo (⟨Λ⟩ : GenLat E n) N (fun b => A.ex (pv X idx x ((N : E)⁻¹ • u i b)))) ∧ GeoInj Xo y.x (fun i b => A.ex (pv X idx x ((N : E)⁻¹ • u i b)))) ∧ ∀ mk : Dw.La →ₗ[𝓞 E] (Fin r → E), IsMark l L mk → A.Marked mk → l.M ∣ N → ∀ Y : (Fin n → LevQ Dw l) → Matrix (Fin n) (Fin r) E, IsRoots l L mk N Y → ∀ q b, A.ex (pv X idx x ((N : E)⁻¹ • Y q b)) ^ N = levPt Xo y.x (levRep (q b)) ∧ (∃ j : ℕ, KilledBy Xo (l.Mb ^ j) (A.ex (pv X idx x ((N : E)⁻¹ • Y q b)))) ∧ ∃ u ∈ L, (N ^ 2 : ℕ) • ((N : E)⁻¹ • Y q b) = (2 : ℕ) • u := by
  first | exact @GlobalTheory.Dict.points_inZh_geoInj_roots | exact GlobalTheory.Dict.points_inZh_geoInj_roots | (intros; apply GlobalTheory.Dict.points_inZh_geoInj_roots <;> assumption)
