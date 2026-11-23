import Formalism.PeriodIntegrals.EtaHostFacts

noncomputable section

open NumberField Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition

namespace PI.UnitaryGroupMassFormula.HostFieldFacts

theorem roots : PI.EtaHostFacts.Roots := by
  intro R H z hz
  exact H.der.norm_mu z hz

theorem conj : PI.EtaHostFacts.Conj := by
  intro R H
  have hfix : ∀ x : H.E, x ∈ H.F ↔ H.conj x = x := fun x =>
    H.conjE_mem_hostF_iff x
  have hcc : ∀ (φ : H.E →+* ℂ) (x : H.E), φ (H.conj x) = starRingEnd ℂ (φ x) := fun φ x =>
    H.conjE_apply φ x
  let c : H.E →ₐ[H.F] H.E :=
    { (H.conj : H.E →+* H.E) with
      commutes' := fun a => (hfix _).1 a.2 }
  refine ⟨c, ?_, ?_, ?_, ?_⟩
  · intro x
    apply H.φ₀.injective
    show H.φ₀ (H.conj (H.conj x)) = H.φ₀ x
    rw [hcc, hcc]
    simp
  · intro x hx
    exact ⟨⟨x, (hfix x).2 hx⟩, rfl⟩
  · intro φ x
    exact hcc φ x
  · show H.conj H.sqrtMinusD = -H.sqrtMinusD
    have h := H.gal_sqd H.conj
    have hg : H.gal H.conj = R.toFrame.cc := H.gal.apply_symm_apply _
    show H.conj H.sqd = -H.sqd
    rw [h, hg]
    simp [Formalism.HC.Frame.cc, c0]

end PI.UnitaryGroupMassFormula.HostFieldFacts
