import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WeightedHomogeneousComponentMemOfGLSchemeSubmodu
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodTopBot
import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.WeylDualWeylLatticesAgreeOfLowestAlcove
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weightedHomogeneousComponent_mem_of_GLSchemeSubmodule : ∀ (k : Type) [Field k] (N : ℕ) (lam : DomWeight N) (M : Submodule k (MvPolynomial (Fin N × Fin N) k)), GlobalTheory.Published.IsGLSubmodule k N lam M → ∀ μ : Fin N → ℕ, ∀ f ∈ M, weightedHomogeneousComponent (rowW N N) μ f ∈ M := by
  first | exact @GlobalTheory.Alc.weightedHomogeneousComponent_mem_of_isGLSubmodule | exact GlobalTheory.Alc.weightedHomogeneousComponent_mem_of_isGLSubmodule | (intros; apply GlobalTheory.Alc.weightedHomogeneousComponent_mem_of_isGLSubmodule <;> assumption)
