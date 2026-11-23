import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsCompletedIsometryInducingHalfLevelAutomorp
import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ThetaLeMsupOfSetC
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.WeightedPrimeSumBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LatOfLamSt
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.FormTies
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_completed_isometry_inducing_half_level_automorphism : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (γ : LaMod Dw l ≃ₗ[𝓞 E] LaMod Dw l), ∃ g : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sim Dw, (∀ n, g.ν n = 1) ∧ (∀ x, (l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)).mkQ (g.f l.M x) = γ ((l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)).mkQ x)) ∧ ∀ N : ℕ, 0 < N → Nat.Coprime N l.M → ∀ x, Dw.ModN N (g.f N x - x) := by
  first | exact @GlobalTheory.LevelIsometry.exists_isometry_inducing | exact GlobalTheory.LevelIsometry.exists_isometry_inducing | (intros; apply GlobalTheory.LevelIsometry.exists_isometry_inducing <;> assumption)
