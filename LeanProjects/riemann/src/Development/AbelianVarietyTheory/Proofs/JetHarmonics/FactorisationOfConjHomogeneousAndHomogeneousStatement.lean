import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FactorisationOfConjHomogeneousAndHomogeneous
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.factorisation_of_conjHomogeneous_and_homogeneous : ∀ (T Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] (l : T → Wp) (l' : T → Wq) (J : T → T → (Wq →L[ℂ] Wp) → (Wq →L[ℂ] Wp)) (A : T → Wq → Wq → Wp) (Bb : T → Wp → Wq → Wp), (∀ y a c (t : ℂ), A y (t • a) c = star t • A y a c) → (∀ x b c (t : ℂ), Bb x (t • b) c = t • Bb x b c) → (∀ x y X c, J x y X c = A y (ContinuousLinearMap.adjoint X (l x)) c) → (∀ x y X c, J x y X c = Bb x (X (l' y)) c) → ∃ OO : Wq →L[ℂ] Wp, ∀ x y X, J x y X = ⟪l x, X (l' y)⟫_ℂ • OO := by
  first | exact @GlobalTheory.factorisation_of_two_partial_integrations | exact GlobalTheory.factorisation_of_two_partial_integrations | (intros; apply GlobalTheory.factorisation_of_two_partial_integrations <;> assumption)
