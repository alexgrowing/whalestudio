import Mathlib
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RootsLevelPointsSameVacuumTranslates
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsBaseClassLevelAdapted
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.ThetaSpanAdjoint
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict GlobalTheory.Phase GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.roots_levelPoints_same_vacuum_translates : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (n : ℕ), IsSympl X bas → Even n → ∀ L : Lt E r, SelfD X L → ∀ mk : Dw.La →ₗ[𝓞 E] (Fin r → E), IsMark l L mk → ∀ h : Matrix (Fin n) (Fin n) E, ccT h * h = 1 → ∀ Λ ∈ Vset E n l.M, ∀ Λ' ∈ Vset E n l.M, Moves h Λ Λ' → ∀ N N' : ℕ, (⟨Λ⟩ : GenLat E n).LevOK N l.M → (⟨Λ'⟩ : GenLat E n).LevOK N' l.M → ∀ Y Y' : (Fin n → LevQ Dw l) → Matrix (Fin n) (Fin r) E, IsRoots l L mk N Y → IsRoots l L mk N' Y' → (∃ e : (Fin n → LevQ Dw l) ≃ (Fin n → LevQ Dw l), ∀ q, LevMoves h q (e q)) ∧ ∀ q q', LevMoves h q q' → ∀ u : TF n g, IsVac X bas (H.w0 : E) (tens Λ' L) u → heisG X bas (Y' q') u = heisG X bas (h * Y q) u := by
  first | exact @GlobalTheory.Dict.RootsMove.roots_move | exact GlobalTheory.Dict.RootsMove.roots_move | (intros; apply GlobalTheory.Dict.RootsMove.roots_move <;> assumption)
