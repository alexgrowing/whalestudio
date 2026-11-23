import Mathlib
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DifferentialOperatorBracket
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.QminorIntertwiningApply
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliDetFrameIndep
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntertwinerDOpOfStabiliser
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open Formalism.REAL (qdet GlRel IsHW)
namespace GlobalTheory

theorem isType_of_irreducible_stable : ∀ (Y : Type) [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [FiniteDimensional ℂ Y] (k r : ℕ) (z : (Fin (2 * r + k + 1) → ℂ)) (π : Mx k r → (Y →L[ℂ] Y)) (B : Fin k → (Fin (2 * r + k + 1) → ℂ)) (S : Submodule ℂ Y) (u : ℕ → ℝ), inWb k r z → 0 < Tz k r z → IsRepW k r z π → (∀ h ∈ UWset k r z, ∀ v, ‖π h v‖ = ‖v‖) → IsFrameOf k r [z] B → Stab (EB π B) S → S ≠ ⊥ → (∀ S' : Submodule ℂ Y, S' ≤ S → Stab (EB π B) S' → S' = ⊥ ∨ S' = S) → (∀ (w : ℂ), ∀ y ∈ S, qdet (EB π B) w y = (∏ i ∈ Finset.Icc 1 k, (w - (k : ℂ) / 2 + 1 / 2 + (u i : ℂ))) • y) → ∃ πS : Mx k r → (S →L[ℂ] S), IsType k r z πS u ∧ ∀ h ∈ UWset k r z, ∀ y : S, ((πS h y : S) : Y) = π h y := by
  intro Y _ _ _ k r z π B S u hz hT hπ hn hB hS hne hirr hcap
  have hst : ∀ h ∈ UWset k r z, ∀ v ∈ S, π h v ∈ S :=
    Formalism.FourierDecayAlt.P.lie_stabilizer Y k r z π B hz hT hπ hB S hS
  have hfr0 : ∀ {m : ℕ} (C : Fin m → (Fin (2 * r + k + 1) → ℂ)), IsFrameOf k r [z] C → IsFrameOf k r [z, 0] C := by
    intro m C hC
    refine ⟨hC.1, hC.2.1, fun a v hv => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl
    · exact hC.2.2 a _ (by simp)
    · simp [herm]
  let πS : Mx k r → (S →L[ℂ] S) := fun h => (S.orthogonalProjection).comp ((π h).comp S.subtypeL)
  have hcoe : ∀ h ∈ UWset k r z, ∀ y : S, ((πS h y : S) : Y) = π h y := by
    intro h hh y
    have := Submodule.orthogonalProjection_mem_subspace_eq_self (K := S) ⟨π h y, hst h hh y y.2⟩
    exact congrArg Subtype.val this
  have hrep : IsRepW k r z πS := by
    refine ⟨⟨?_, fun a _ b hb => ?_⟩, ?_⟩
    · ext y
      simp [πS, hπ.1.1]
    · ext y
      have h1 := hcoe b hb y
      simp only [πS, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply] at h1 ⊢
      rw [h1, hπ.1.2 a ‹_› b hb]
      rfl
    · exact continuousOn_const.clm_comp (hπ.2.clm_comp continuousOn_const)
  refine ⟨πS, ⟨Submodule.nontrivial_iff_ne_bot.2 hne, hrep.1, hrep.2, ?_, ?_, ?_⟩, hcoe⟩
  · intro h hh v
    rw [Submodule.coe_norm, Submodule.coe_norm, hcoe h hh, hn h hh]
  · intro S'' hS''
    have hstab : Stab (EB π B) (S''.map S.subtype) := by
      refine Formalism.FourierDecayAlt.P.stabilizer_lie_algebra Y k r k z 0 π B hπ (hfr0 B hB) _ ?_
      rintro h hh - _ ⟨y, hy, rfl⟩
      exact ⟨πS h y, hS'' h hh y hy, hcoe h hh y⟩
    rcases hirr _ (Submodule.map_subtype_le S S'') hstab with h | h
    · left
      exact Submodule.map_injective_of_injective S.injective_subtype (by rw [h, Submodule.map_bot])
    · right
      exact Submodule.map_injective_of_injective S.injective_subtype (by rw [h, Submodule.map_subtype_top])
  · intro B' hB' w v
    rw [(Formalism.FourierDecayAlt.P.frame_general_linear S k r k z πS B' hrep hB').2 w v]
    apply Subtype.ext
    have h1 := GlobalTheory.intertwiner_EB_of_stabiliser S Y k r k z 0 πS π S.subtypeL B' hrep hπ (hfr0 B' hB') (fun h hh _ v => hcoe h hh v)
    have h2 := GlobalTheory.qminor_intertwine Y S k k (EB π B') (EB πS B') S.subtype h1 id id w v
    have h3 := GlobalTheory.capelli_det_frame_indep Y k r z π B B' hz hT hπ hB hB' w
    refine h2.trans ?_
    have h4 := hcap w v v.2
    rw [h3] at h4
    exact h4

end GlobalTheory
