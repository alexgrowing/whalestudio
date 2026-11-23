import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum

set_option autoImplicit false

open CategoryTheory

namespace GlobalTheory.Vert.Flag

variable {X : AlgebraicGeometry.Scheme.{0}} {E : X.Modules} {N : ℕ}

def SameStep (fl fl' : Flag E N) (i : Fin (N + 1)) : Prop :=
  ∃ e : fl.F i ≅ fl'.F i, e.hom ≫ fl'.ι i = fl.ι i

def Adjacent (fl fl' : Flag E N) : Prop :=
  ∃ j : Fin (N + 1), ∀ i, i ≠ j → fl.SameStep fl' i

theorem sameStep_refl (fl : Flag E N) (i : Fin (N + 1)) : fl.SameStep fl i :=
  ⟨Iso.refl _, Category.id_comp _⟩

theorem SameStep.symm {fl fl' : Flag E N} {i : Fin (N + 1)} (h : fl.SameStep fl' i) :
    fl'.SameStep fl i := by
  obtain ⟨e, he⟩ := h
  exact ⟨e.symm, by rw [Iso.symm_hom, ← he, Iso.inv_hom_id_assoc]⟩

theorem adjacent_refl (fl : Flag E N) : fl.Adjacent fl := ⟨0, fun i _ => fl.sameStep_refl i⟩

theorem Adjacent.symm {fl fl' : Flag E N} (h : fl.Adjacent fl') : fl'.Adjacent fl := by
  obtain ⟨j, hj⟩ := h
  exact ⟨j, fun i hi => (hj i hi).symm⟩

end GlobalTheory.Vert.Flag
