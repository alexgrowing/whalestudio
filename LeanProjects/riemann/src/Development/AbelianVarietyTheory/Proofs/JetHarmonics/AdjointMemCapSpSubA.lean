import Mathlib
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DifferentialOperatorBracket
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DiagonalTransferAction
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.QminorIntertwiningApply
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntertwinerDOpOfStabiliser
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open Formalism.REAL (qdet GlRel IsHW)
namespace GlobalTheory

theorem adjoint_mem_CapSp_subA : ∀ (V₁ : Type) [NormedAddCommGroup V₁] [InnerProductSpace ℂ V₁] [FiniteDimensional ℂ V₁] (V₂ : Type) [NormedAddCommGroup V₂] [InnerProductSpace ℂ V₂] [FiniteDimensional ℂ V₂] (n r : ℕ) (z : (Fin (2 * r + (n + 1) + 1) → ℂ)) (π₁ : Mx (n + 1) r → (V₁ →L[ℂ] V₁)) (π₂ : Mx (n + 1) r → (V₂ →L[ℂ] V₂)) (B : Fin (n + 1) → (Fin (2 * r + (n + 1) + 1) → ℂ)) (T : V₂ →L[ℂ] V₁) (μ : Fin n → ℂ), IsRepW (n + 1) r z π₁ → IsRepW (n + 1) r z π₂ → (∀ h ∈ UWset (n + 1) r z, ∀ v, ‖π₁ h v‖ = ‖v‖) → (∀ h ∈ UWset (n + 1) r z, ∀ v, ‖π₂ h v‖ = ‖v‖) → IsFrameOf (n + 1) r [z] B → (∀ h ∈ UWset (n + 1) r z, h *ᵥ B (Fin.last n) = B (Fin.last n) → T.comp (π₂ h) = (π₁ h).comp T) → ∀ v ∈ CapSp (subA (EB π₁ B)) μ, ContinuousLinearMap.adjoint T v ∈ CapSp (subA (EB π₂ B)) μ := by
  intro V₁ _ _ _ V₂ _ _ _ n r z π₁ π₂ B T μ h₁ h₂ hu₁ hu₂ hB hT v hv
  have hB' : IsFrameOf (n + 1) r [z, B (Fin.last n)] (fun a : Fin n => B a.castSucc) := by
    refine ⟨fun a => hB.1 _, fun a b => ?_, fun a x hx => ?_⟩
    · rw [hB.2.1]
      simp only [Fin.castSucc_inj]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with hx | hx
      · exact hB.2.2 _ x (by simp [hx])
      · rw [hx, hB.2.1, if_neg (Fin.castSucc_lt_last a).ne]
  have hlie := GlobalTheory.intertwiner_EB_of_stabiliser V₂ V₁ (n + 1) r n z (B (Fin.last n)) π₂ π₁ T
    (fun a : Fin n => B a.castSucc) h₂ h₁ hB' (fun h hh he w => by
      have := congrArg (fun S : V₂ →L[ℂ] V₁ => S w) (hT h hh he)
      simpa using this)
  have hlie' : ∀ (a b : Fin n) (w : V₂),
      T (EB π₂ B a.castSucc b.castSucc w) = EB π₁ B a.castSucc b.castSucc (T w) := hlie
  have hadj : ∀ (a b : Fin n) (w : V₁),
      (ContinuousLinearMap.adjoint T).toLinearMap (subA (EB π₁ B) a b w) =
        subA (EB π₂ B) a b ((ContinuousLinearMap.adjoint T).toLinearMap w) := by
    intro a b w
    apply ext_inner_right ℂ
    intro y
    show inner ℂ (ContinuousLinearMap.adjoint T (EB π₁ B a.castSucc b.castSucc w)) y =
      inner ℂ (EB π₂ B a.castSucc b.castSucc (ContinuousLinearMap.adjoint T w)) y
    rw [ContinuousLinearMap.adjoint_inner_left,
      Formalism.FourierDecayAlt.P5.Kfp.EB_adj h₁.1 h₁.2 hu₁ hB, Formalism.FourierDecayAlt.P5.Kfp.EB_adj h₂.1 h₂.2 hu₂ hB,
      ContinuousLinearMap.adjoint_inner_left, hlie']
  rw [mem_CapSp] at hv ⊢
  intro w
  have hq := qminor_intertwine V₂ V₁ n n (subA (EB π₂ B)) (subA (EB π₁ B))
    (ContinuousLinearMap.adjoint T).toLinearMap hadj id id w v
  have hq' : ContinuousLinearMap.adjoint T (qdet (subA (EB π₁ B)) w v) =
      qdet (subA (EB π₂ B)) w (ContinuousLinearMap.adjoint T v) := hq
  rw [← hq', hv w, map_smul]

end GlobalTheory
