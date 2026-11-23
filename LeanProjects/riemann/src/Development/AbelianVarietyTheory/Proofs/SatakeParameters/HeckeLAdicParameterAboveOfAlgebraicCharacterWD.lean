import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.AlgebraicCharacterWD
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HeckeLAdicParameterAbove

namespace GlobalTheory

theorem heckeLAdicParameterAbove_of_algebraicCharacterWD (H : GlobalTheory.Published.AlgebraicCharacterWD) :
    GlobalTheory.Published.HeckeLAdicParameterAbove := by
  intro E Ω _ _ _ _ _ l _ P AI hT ι art hart χ n μ hχ hμ hL w A h O _ _ _ Bw hj ξ hξ rc hrc
  obtain ⟨a, ha, ε, -, L⟩ := hrc
  rw [H E Ω l P AI hT ι art hart χ n μ hχ hμ hL w A h O Bw hj ξ hξ a ha]
  exact (L.one ξ hξ.1).symm

end GlobalTheory
