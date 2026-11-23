import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianLifting

set_option autoImplicit false

namespace GlobalTheory.Published

theorem grothendieckDeformation_of_lifting (P : AbelianDeRham) (L : AbelianLifting) :
    GrothendieckDeformation :=
  fun R _ I κ hκ R₀ _ π hπ hI ↦
    ⟨GrothendieckMessing.canonical_of_abelianDeRham P hκ hπ hI, L R I κ hκ R₀ π hπ hI⟩

end GlobalTheory.Published
