import Mathlib
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FourierTranslatesVacuumRootsLevelPoints
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
theorem _root_.GlobalTheory.T.fourier_translates_vacuum_roots_levelPoints : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ w : E, IsIntegral ℤ w → w + cc w = 1 → ∀ (L : Lt E r) (mk : Dw.La →ₗ[𝓞 E] (Fin r → E)), SelfD X L → IsMark l L mk → ∀ Λ ∈ Vset E n l.M, ∀ N : ℕ, NOK Λ N l.M → ∀ Y : (Fin n → LevQ Dw l) → Matrix (Fin n) (Fin r) E, IsRoots l L mk N Y → ∀ p : TF n g, IsSB p → (∀ u ∈ tens Λ L, epsW X w u • heisG X bas u p = p) → ∀ u ∈ tens Λ ((Ideal.span {2} * conjI (Mfr l)) • L), ∑ᶠ q, cexp (-(2 * Real.pi * I * ((∑ b, EF X (u b) (Y q b) : ℚ) : ℂ))) • heisG X bas (Y q) p = ((Nat.card (Fin n → LevQ Dw l) : ℕ) : ℂ) • heisG X bas u (projA X bas w (tens Λ (idq (Mfr l) (conjI (Mfr l)) L)) p) := by
  first | exact @GlobalTheory.Dict.poisson_roots | exact GlobalTheory.Dict.poisson_roots | (intros; apply GlobalTheory.Dict.poisson_roots <;> assumption)
