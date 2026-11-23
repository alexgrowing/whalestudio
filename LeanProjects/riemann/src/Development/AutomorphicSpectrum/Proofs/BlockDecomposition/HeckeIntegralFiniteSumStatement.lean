import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeIntegralFiniteSum
import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf
open GlobalTheory.BCT PositivityTheory.Rg.BcB.G8.Fin
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_integral_finite_sum : ∀ (H : Type) [Group H] (K L : Subgroup H) (u : H → ℂ), L ≤ K → L.relIndex K ≠ 0 → (∀ l ∈ L, ∀ x, u (x * l) = u x) → hint K u = ((L.relIndex K : ℕ) : ℂ)⁻¹ * ∑ᶠ p : H ⧸ L, u p.out := by
  first | exact @GlobalTheory.CompanionTheory.HintLevelPt.hint_eq_level_of_forall | exact GlobalTheory.CompanionTheory.HintLevelPt.hint_eq_level_of_forall | (intros; apply GlobalTheory.CompanionTheory.HintLevelPt.hint_eq_level_of_forall <;> assumption)
