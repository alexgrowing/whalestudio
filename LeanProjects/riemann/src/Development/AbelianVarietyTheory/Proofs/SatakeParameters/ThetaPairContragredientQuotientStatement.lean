import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaPairContragredientQuotient
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsParahoricVec
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_pair_contragredient_quotient : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r n : ℕ) (μ : kˣ →* ℂˣ) (V : Type) [AddCommGroup V] [Module ℂ V] (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GL (Fin r) k) V) (π : Representation ℂ (GL (Fin n) k) W), IsSmoothChar μ → IsAdmissible π → ThetaPair μ σ π → OmQuot μ σ (contra π) := by
  first | exact @GlobalTheory.ThetaGL.omQuot_contra_of_thetaPair | exact GlobalTheory.ThetaGL.omQuot_contra_of_thetaPair | (intros; apply GlobalTheory.ThetaGL.omQuot_contra_of_thetaPair <;> assumption)
