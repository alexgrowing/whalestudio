import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StInjectiveHolomorphicOpen
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StInvarianceOfDomain
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

namespace InjectiveHolomorphicOpen

theorem finrank_eq (k : ℕ) :
    Module.finrank ℝ (Fin k → ℂ) = Module.finrank ℝ (Fin (2 * k) → ℝ) := by
  simp [Module.finrank_pi_fintype, Complex.finrank_real_complex, mul_comm]

theorem proof (hID : InvarianceOfDomain.Statement) : InjectiveHolomorphicOpen.Statement := by
  intro k U f hU hf hinj
  let e : (Fin k → ℂ) ≃L[ℝ] (Fin (2 * k) → ℝ) := ContinuousLinearEquiv.ofFinrankEq (finrank_eq k)
  have hU' : IsOpen (e '' U) := e.toHomeomorph.isOpenMap U hU
  have hcont : ContinuousOn (fun y => e (f (e.symm y))) (e '' U) := by
    refine e.continuous.comp_continuousOn (hf.continuousOn.comp e.symm.continuous.continuousOn ?_)
    rintro _ ⟨x, hx, rfl⟩
    simpa using hx
  have hinj' : Set.InjOn (fun y => e (f (e.symm y))) (e '' U) := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨x', hx', rfl⟩ h
    simp only [ContinuousLinearEquiv.symm_apply_apply] at h
    rw [hinj hx hx' (e.injective h)]
  have himage : (fun y => e (f (e.symm y))) '' (e '' U) = e '' (f '' U) := by
    rw [Set.image_image, Set.image_image]
    simp
  have hopen := hID (2 * k) (e '' U) (fun y => e (f (e.symm y))) hU' hcont hinj'
  rw [himage] at hopen
  have hpre : e ⁻¹' (e '' (f '' U)) = f '' U := Set.preimage_image_eq _ e.injective
  rw [← hpre]
  exact hopen.preimage e.continuous

end InjectiveHolomorphicOpen

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
