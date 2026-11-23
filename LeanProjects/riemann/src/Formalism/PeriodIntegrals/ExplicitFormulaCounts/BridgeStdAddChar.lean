import Formalism.UnipotentAdelicQuotients.StdAdditiveCharExists
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.StdCharTR

open NumberField

namespace PI.Bridge

theorem bridge_stdAddChar : HeckeCharacterZeroLocus.StdAdditiveCharExists := by
  have h := stdCharTR
  unfold PI.StdCharTR.Target at h
  unfold HeckeCharacterZeroLocus.StdAdditiveCharExists
  intro F _ _ hF
  obtain ⟨ψ, hψ, hinf⟩ := h F hF
  unfold Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCharAF at hψ
  obtain ⟨hc, hn, hk, x₀, hx₀⟩ := hψ

  refine ⟨ψ.compAddMonoidHom (-(AddMonoidHom.id _)), ?_, ?_, ?_, ?_, ?_⟩
  · change Continuous (fun x => ψ (-x))
    exact hc.comp continuous_neg
  · intro x
    change ‖ψ (-x)‖ = 1
    exact hn _
  · intro a
    change ψ (-(algebraMap F _ a)) = 1
    rw [← map_neg]
    exact hk (-a)
  · refine ⟨-x₀, ?_⟩
    change ψ (- -x₀) ≠ 1
    rw [neg_neg]
    exact hx₀
  · intro x
    change ψ (-_) = _
    rw [AddChar.map_neg_eq_inv, Complex.exp_neg, ← hinf x]
    rfl

end PI.Bridge
