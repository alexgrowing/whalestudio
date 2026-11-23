import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PoincareDeRhamDuality
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianDeRhamStructure
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CubeTheorem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianDeRhamStructureToFree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidOfFreeOfCrystallineDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianDeRhamPoincareDualityOfCubeDual

set_option autoImplicit false

namespace GlobalTheory

theorem abelianDeRham_of_duality (hQ : GlobalTheory.Published.CubeTheorem)
    (hS : GlobalTheory.Published.AbelianDeRhamStructure)
    (hC : GlobalTheory.Published.CrystallineDeRham) (hD : GlobalTheory.Published.DualAbelianScheme)
    (hP : GlobalTheory.Published.PoincareDeRhamDuality) : GlobalTheory.Published.AbelianDeRham := by
  have hF : GlobalTheory.Published.AbelianDeRham.Free := abelianDeRhamStructure_toFree hS
  exact ⟨hF, hS.2.1, hS.2.2,
    GlobalTheory.Published.AbelianDeRham.rigid_of_free_of_crystallineDeRham hF hC,
    GlobalTheory.CubeDual.abelianDeRham_duality hQ hD hP hF⟩

example : GlobalTheory.Published.CubeTheorem → GlobalTheory.Published.AbelianDeRhamStructure →
    GlobalTheory.Published.CrystallineDeRham → GlobalTheory.Published.DualAbelianScheme →
    GlobalTheory.Published.PoincareDeRhamDuality → GlobalTheory.Published.AbelianDeRham :=
  abelianDeRham_of_duality

end GlobalTheory
