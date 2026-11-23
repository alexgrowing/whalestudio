import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlagDomainDataPrincipalCongruenceLevel
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.UnitaryHaarVolume
open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.LevGeo
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_flagDomainData_principalCongruenceLevel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (M : ℕ) (X0 : Data E r) (Λ : Submodule (𝓞 E) (Fin r → E)), 3 ≤ M → Λ.FG → Submodule.span E (Λ : Set (Fin r → E)) = ⊤ → ∃ X : Data E r, X.Gm = X0.Gm ∧ X.Ψ = X0.Ψ ∧ X.p0 = X0.p0 ∧ X.Λ = Λ ∧ ∀ γ, γ ∈ X.Γ ↔ IsUStab X0.Gm Λ γ ∧ ∀ x ∈ Λ, ∃ y ∈ Λ, (γ : Matrix (Fin r) (Fin r) E).mulVec x - x = M • y := by
  first | exact @GlobalTheory.PrincData.exists_princ_data | exact GlobalTheory.PrincData.exists_princ_data | (intros; apply GlobalTheory.PrincData.exists_princ_data <;> assumption)
