import Mathlib
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.VacuumMultiplierTrivialPrincipalCongruence
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
theorem _root_.GlobalTheory.T.vacuumMultiplier_trivial_principalCongruence : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ (H : Host E) (Dw : Datum H) (φ : Dw.La →ₗ[𝓞 E] (Fin r → E)), r = Dw.p + Dw.q → Function.Injective φ → Submodule.span E (Set.range φ) = ⊤ → (∀ a b, ((Dw.EF a b : ℤ) : ℚ) = EF X (φ a) (φ b)) → ∀ L : Lt E r, SelfD X L → ∀ (M : ℕ), 3 ≤ M → ∀ ga : GL (Fin r) E, IsUn X ga → mapL ga L = L → (∀ u ∈ L, ∃ u' ∈ L, (ga : Matrix (Fin r) (Fin r) E) *ᵥ u = u + M • u') → ∀ v : TF n g, IsVac X bas (H.w0 : E) (tens (stdL E n) L) v → wG X bas idx ga v = v := by
  first | exact @GlobalTheory.VacMult.wG_vac_eq | exact GlobalTheory.VacMult.wG_vac_eq | (intros; apply GlobalTheory.VacMult.wG_vac_eq <;> assumption)
