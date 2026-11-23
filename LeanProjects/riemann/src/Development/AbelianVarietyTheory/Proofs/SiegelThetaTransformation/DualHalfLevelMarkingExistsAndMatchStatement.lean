import Mathlib
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DualHalfLevelMarkingExistsAndMatch
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
theorem _root_.GlobalTheory.T.dual_half_level_marking_exists_and_match : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (r : ℕ) (X : Data E r) (L : Lt E r) (mk : Dw.La →ₗ[𝓞 E] (Fin r → E)) (ζ : ℂ), SelfD X L → IsMark l L mk → IsPrimitiveRoot ζ l.M → (∃ δ : Dw.La →ₗ[𝓞 E] (Fin r → E), IsDual X l ζ L mk δ) ∧ (∀ δ : Dw.La →ₗ[𝓞 E] (Fin r → E), IsDual X l ζ L mk δ → L ≤ LinearMap.range δ ⊔ Mfr l • L ∧ (∀ a, δ a ∈ Mfr l • L ↔ a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La)) ∧ (∀ ga : GL (Fin r) E, IsUn X ga → IsMark l (mapL ga L) (mvMap ga mk) ∧ IsDual X l ζ (mapL ga L) (mvMap ga mk) (mvMap ga δ)) ∧ ∀ mk' δ' : Dw.La →ₗ[𝓞 E] (Fin r → E), IsMark l L mk' → IsDual X l ζ L mk' δ' → (∀ a, δ a - δ' a ∈ Mfr l • L) → ∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La), ∃ u ∈ L, mk a = mk' a + l.M • u) ∧ conjI (Mfr l) = l.Mb ∧ Mfr l * l.Mb = Ideal.span {(l.M : 𝓞 E)} ∧ ∀ n N : ℕ, 0 < N → ∃ Y : (Fin n → LevQ Dw l) → Matrix (Fin n) (Fin r) E, IsRoots l L mk N Y := by
  first | exact @GlobalTheory.Dict.DualMark.dual_marking | exact GlobalTheory.Dict.DualMark.dual_marking | (intros; apply GlobalTheory.Dict.DualMark.dual_marking <;> assumption)
