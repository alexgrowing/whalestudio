import Formalism.FilteredPoleLength.ReducedBasisBounds.GradedFreeLengthFiltered
import Formalism.FilteredPoleLength.LocalDescentLevels.LevelsChainOfAddOneLe
import Formalism.FilteredPoleLength.LocalDescentLevels.LevelsLengthSum

open Module

namespace Formalism.LatticeBaseChangeAlt

theorem localStepClosed_of (hLT : LeadingTermLength) : LocalStepClosed := by
  intro ι _ ep f ν v νs c' T R I hep hT hc' hv hν O K K₁ V W
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  intro ϖ hϖ M Θ N₁ Z Zm N' e be n th c AA AA' N₁' ρ a a' hM hΘ h1 h2 h3 h4 h5 h6 ha ha' h7 h8 h9
    h10 h11 h12 h13 h14 h15 h16 h17 hcase
  intro Rr Aq _ _ _ _ _ _ _ _ xq nq Fq rq hF0 hFn hFd hFi hFl hsum hres hequiv
  intro A0 _ _ n1 F1 ι1 _ _ deg δ t σ u hG0 hGn hGd hker hsurj hdeg hlead hind hspan hcard hI V'
  obtain ⟨eqv⟩ := hequiv
  set mmz : ι → ℕ := fun z => (max 0 ⌈(ep z : ℝ) * ((T : ℝ) * ν z - (e : ℝ))⌉).toNat with hmmz
  have hL := levelsLengthSum O ι Rr Aq xq mmz nq Fq rq R hF0 hFn hFd hFi hFl hsum
  have hA : Module.length O (↥AA' ⧸ AA.comap AA'.subtype) ≤
      ((R * ∑ z, mmz z * f z : ℕ) : ℕ∞) := by
    rw [eqv.length_eq, hL]
    refine le_of_eq ?_
    simp only [hres]
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun z _ => ?_
    ring
  have hN : Module.length O (↥AA ⧸ N₁'.comap AA.subtype) ≤ ((R * I : ℕ) : ℕ∞) := by
    rw [hspan, hLT O (↥AA) A0 n1 F1 ι1 deg δ t σ u hG0 hGn hGd hker hsurj hdeg hlead hind, hcard, hI]
    push_cast
    exact le_rfl
  exact localLevelsExt ι ep f ν v νs c' T R I hep hT hc' hv hν O K K₁ V W ϖ hϖ M Θ N₁ Z Zm N' e be
    n th c AA AA' N₁' ρ a a' hM hΘ h1 h2 h3 h4 h5 h6 ha ha' h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17
    hcase hA hN V'

end Formalism.LatticeBaseChangeAlt
