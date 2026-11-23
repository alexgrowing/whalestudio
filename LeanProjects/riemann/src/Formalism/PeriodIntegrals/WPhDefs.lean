import Formalism.PeriodIntegrals.ThGDefs

namespace PI

namespace WPhDefs

section W

variable {T I J : Type} [Fintype T] [Fintype I] [Fintype J]

noncomputable def qG (s A : ℝ) (x : T → I → J → ℂ) : ℝ := s * (HfG A x x).re

noncomputable def wPhG (s A : ℝ) (p : ℕ) (x : T → I → J → ℂ) : ℂ :=
  if p = 2 then Complex.exp ((Real.pi : ℂ) * Complex.I * (qG s A x : ℂ))
  else Classical.epsilon (fun c : ℂ => ∃ (k : ℕ) (m : ℤ), (p : ℝ) ^ k * qG s A x = (m : ℝ) ∧ c = (-1 : ℂ) ^ m)

noncomputable def WopG (s A : ℝ) (p : ℕ) (x : T → I → J → ℂ) (G : (T → I → J → ℂ) → ℂ) : (T → I → J → ℂ) → ℂ :=
  fun z => wPhG s A p x * UG A x G z

noncomputable def kapG (A : ℝ) (x y : T → I → J → ℂ) : ℂ :=
  Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((HfG A x y).im : ℂ))

def QIntLat (s A : ℝ) (La' : AddSubgroup (T → I → J → ℂ)) : Prop :=
  ∀ x ∈ La', (∃ m : ℤ, qG s A x = m) ∧ (x ≠ 0 → 1 ≤ qG s A x)

end W

end WPhDefs

end PI
