import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite

noncomputable section

universe u

abbrev freeModule (Y : Scheme.{u}) (n : ℕ) : Y.Modules :=
  SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin n))

def stdSection (Y : Scheme.{u}) (n : ℕ) (i : Fin n) : Γ(freeModule Y n, ⊤) :=
  (Scheme.Modules.Hom.app (M := structureModule Y)
    (SheafOfModules.ιFree (R := Y.ringCatSheaf) (ULift.up i)) ⊤).hom (1 : Γ(Y, ⊤))

def FreeSheafBasis.Statement : Prop :=
  ∀ (Y : Scheme.{u}) (n : ℕ), IsBasisOn (freeModule Y n) ⊤ (stdSection Y n)

theorem FreeSheafBasis.objects_inhabited :
    Nonempty ((freeModule SpecZ 2 : SpecZ.Modules) ≅ freeModule SpecZ 2) ∧
      Nonempty (Fin 2 → Γ(freeModule SpecZ 2, ⊤)) :=
  ⟨⟨Iso.refl _⟩, ⟨stdSection SpecZ 2⟩⟩

end

end GroundTheory.Heights₂.Heights.Model
