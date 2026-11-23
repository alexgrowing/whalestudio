import Formalism.PeriodIntegrals.ExpIntW

noncomputable section

namespace PI.ExpIntWProof

open PI

def StepI : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (f : MvPowerSeries σ ℂ_[p]), CoefWf f → CoefWf (expMv f)

def KeyW : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (x : ℂ_[p]), x ∈ Wp p → ‖x‖ < 1 → x / (p : ℂ_[p]) ∈ Wp p

def StepIII : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (x : ℂ_[p]), InWf x → ‖x‖ ≤ 1 → x ∈ Wp p

theorem expIntW_of_steps (h1 : StepI) (h3 : StepIII) : ExpIntW := by
  intro p _ σ f hf hs
  obtain ⟨h0, hint⟩ := hs
  rw [sub_zero] at h0 hint
  refine ⟨by rw [sub_zero]; exact h0, ?_⟩
  rw [sub_zero]
  intro n
  exact h3 p _ (h1 p σ f hf n) (hint n)

end PI.ExpIntWProof

end
