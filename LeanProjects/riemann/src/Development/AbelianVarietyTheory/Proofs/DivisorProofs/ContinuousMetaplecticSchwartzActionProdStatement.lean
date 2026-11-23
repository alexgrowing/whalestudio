import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousMetaplecticSchwartzActionProd
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.MetaplecticRepresentation
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IteratedLineDerivMemWeylAlg
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsEqTransposeMulDiagonalMul
open MeasureTheory Matrix Complex GlobalTheory.RealWeil
open scoped Real SchwartzMap ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_metaplectic_schwartz_action_prod : ∀ (l : Type) [Fintype l] [DecidableEq l] (G : Type) [Group G] [TopologicalSpace G] (pr : G →* Matrix.symplecticGroup l ℝ) (om : G →* (L2 l ≃ₗᵢ[ℂ] L2 l)) (omS : G →* (Sch l →L[ℂ] Sch l)), Continuous pr → (∀ f : L2 l, Continuous fun g => om g f) → (∀ (g : G) (w : l ⊕ l → ℝ) (f : L2 l), om g (rho w f) = rho ((pr g : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ w) (om g f)) → (∀ (g : G) (f : Sch l), om g (f.toLp 2) = (omS g f).toLp 2) → Continuous fun x : G × Sch l => omS x.1 x.2 := by
  first | exact @GlobalTheory.RealWeil.continuous_omS_prod | exact GlobalTheory.RealWeil.continuous_omS_prod | (intros; apply GlobalTheory.RealWeil.continuous_omS_prod <;> assumption)
