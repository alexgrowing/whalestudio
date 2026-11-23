import Mathlib
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SelfDualLatticeDiagonalUnitaryPatchedStandard
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selfDual_lattice_diagonal_unitary_patched_standard : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n r M : ℕ) (𝔍 𝔞 : Ideal (𝓞 E)) (α : 𝓞 E), 0 < M → (M : 𝓞 E) ∈ 𝔍 → IsCoprime 𝔍 (conjI 𝔍) → α ≠ 0 → Ideal.span {α} = 𝔍 * 𝔞 → IsCoprime 𝔞 (Ideal.span {(M : 𝓞 E)}) → ∀ h : Matrix (Fin n) (Fin n) E, h = Matrix.diagonal (fun k : Fin n => if (k : ℕ) < r then 1 else cc (α : E) / (α : E)) → ccT h * h = 1 ∧ ∀ Λ ∈ Vset E n M, ∃ Λ' ∈ Vset E n M, ∃ Λ'' ∈ Vset E n 1, Moves h Λ Λ'' ∧ (𝔍 * conjI 𝔍) • Λ'' ≤ Λ' ∧ (𝔍 * conjI 𝔍) • Λ' ≤ Λ'' := by
  first | exact @GlobalTheory.Dict.Patch.main | exact GlobalTheory.Dict.Patch.main | (intros; apply GlobalTheory.Dict.Patch.main <;> assumption)
