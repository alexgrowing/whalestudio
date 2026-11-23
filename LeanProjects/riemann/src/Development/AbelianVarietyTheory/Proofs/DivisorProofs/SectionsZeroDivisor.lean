import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
open CategoryTheory AlgebraicGeometry GlobalTheory.Cartier GlobalTheory.Cartier.CartierDiv

namespace GlobalTheory.Cartier.CartierDiv

theorem sections_zero_eq_one (X : Scheme.{0}) [IsIntegral X] :
    (0 : CartierDiv X).sections = 1 := by
  ext f
  rw [mem_sections, Submodule.mem_one]
  simp only [regularAt_zero_iff]
  constructor
  · intro h
    obtain ⟨a, ha⟩ := exists_fnOf_eq (X := X) (U := ⊤) trivial fun x _ => h x
    exact ⟨a, by rw [algebraMap_top]; exact ha⟩
  · rintro ⟨a, rfl⟩ x
    rw [algebraMap_top]
    exact regAt_fnOf (U := ⊤) trivial trivial a

end GlobalTheory.Cartier.CartierDiv
