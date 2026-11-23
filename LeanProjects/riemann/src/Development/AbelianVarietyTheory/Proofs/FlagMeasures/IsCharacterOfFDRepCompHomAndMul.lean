import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsMirClass
open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

namespace GlobalTheory.GLm

theorem isChar_comp_hom {G M : Type} [Group G] [Group M] (π : G →* M) (χ : M → ℂ)
    (h : IsChar χ) : IsChar (fun x => χ (π x)) := by
  obtain ⟨V, hV⟩ := h
  exact ⟨FDRep.of (V.ρ.comp π), fun x => hV (π x)⟩

theorem isChar_mul_fun {G : Type} [Group G] (α β : G → ℂ) (hα : IsChar α) (hβ : IsChar β) :
    IsChar (fun x => α x * β x) := by
  obtain ⟨V, hV⟩ := hα
  obtain ⟨W, hW⟩ := hβ
  refine ⟨CategoryTheory.MonoidalCategoryStruct.tensorObj V W, fun x => ?_⟩
  rw [FDRep.char_tensor, Pi.mul_apply, hV, hW]

theorem isChar_comp_hom_and_mul :
    (∀ (G M : Type) [Group G] [Group M] (π : G →* M) (χ : M → ℂ),
      IsChar χ → IsChar (fun x => χ (π x))) ∧
    ∀ (G : Type) [Group G] (α β : G → ℂ), IsChar α → IsChar β → IsChar (fun x => α x * β x) :=
  ⟨fun _ _ _ _ π χ h => isChar_comp_hom π χ h, fun _ _ α β hα hβ => isChar_mul_fun α β hα hβ⟩

end GlobalTheory.GLm
