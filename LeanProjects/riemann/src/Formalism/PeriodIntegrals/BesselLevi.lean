import Mathlib
import Formalism.FormalDegreeBessel.StatementG

noncomputable section

open Matrix Formalism.QuantumDeterminants

namespace PI.BesselLevi

def BesselLevi : Prop :=
  ∀ (k r : ℕ) (T : ℝ), 0 < T → ∀ s : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ,
    s ∈ UH (Hpk k r) →
    (∀ (a : Fin r) (i : Fin (2 * r + k + 1)), a.val ≤ i.val → s i (eI k r a) = if i = eI k r a then 1 else 0) →
    (∀ i : Fin (2 * r + k + 1), r ≤ i.val →
      (s *ᵥ (((Real.sqrt T : ℝ) : ℂ) • bvec (wI k r (Fin.last k)))) i =
        (((Real.sqrt T : ℝ) : ℂ) • bvec (wI k r (Fin.last k))) i) →
    s ∈ Sset k r (((Real.sqrt T : ℝ) : ℂ) • bvec (wI k r (Fin.last k)))

end PI.BesselLevi
