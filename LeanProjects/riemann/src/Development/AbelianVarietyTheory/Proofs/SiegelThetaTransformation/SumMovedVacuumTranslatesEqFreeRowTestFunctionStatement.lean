import Mathlib
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SumMovedVacuumTranslatesEqFreeRowTestFunction
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
theorem _root_.GlobalTheory.T.sum_moved_vacuum_translates_eq_freeRow_testFunction : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ (D : SW.Level X) (hn : r ≤ n) (M : ℕ) (𝔐 𝔍 𝔞 : Ideal (𝓞 E)) (α : 𝓞 E), 0 < M → (M : 𝓞 E) ∈ D.𝔪 → D.𝔪 = 𝔐 * 𝔍 → IsCoprime 𝔐 𝔍 → α ≠ 0 → Ideal.span {α} = 𝔍 * 𝔞 → IsCoprime 𝔞 (Ideal.span {(M : 𝓞 E)}) → ∀ v₀ : Lt E r → TF n g, (∀ L ∈ D.lats, IsVac X bas D.w (tens (stdL E n) (D.sh L)) (v₀ L)) → ∀ h : Matrix (Fin n) (Fin n) E, h = Matrix.diagonal (fun k : Fin n => if (k : ℕ) < r then 1 else cc (α : E) / (α : E)) → ∀ Λ ∈ Vset E n M, ∀ Λ' ∈ Vset E n M, ∀ Λ'' ∈ Vset E n 1, Moves h Λ Λ'' → (𝔍 * conjI 𝔍) • Λ'' ≤ Λ' → (𝔍 * conjI 𝔍) • Λ' ≤ Λ'' → ∃ t : ℂ, t ≠ 0 ∧ ∀ L ∈ D.lats, ∃ s : Finset (Matrix (Fin n) (Fin r) E), D.phi bas hn v₀ L Λ = ∑ y ∈ s, D.dat hn y • heisG X bas y (unitv (projA X bas D.w (tens Λ (D.sh L)) (v₀ L))) ∧ ∑ y ∈ s, D.dat hn y • heisG X bas (h * y) (unitv (projA X bas D.w (tens Λ'' (D.sh L)) (v₀ L))) = t • phiF bas D 𝔐 hn v₀ L Λ' := by
  first | exact @GlobalTheory.Dict.SumFree.sum_free | exact GlobalTheory.Dict.SumFree.sum_free | (intros; apply GlobalTheory.Dict.SumFree.sum_free <;> assumption)
