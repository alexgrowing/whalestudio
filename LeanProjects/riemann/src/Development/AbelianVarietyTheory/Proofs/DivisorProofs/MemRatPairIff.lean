import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl

noncomputable section

open NumberField

namespace GlobalTheory.WeilUnitaryTransport

def ratPair (F : Type) [Field F] [NumberField F] (κ : Type) :
    AddSubgroup ((κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F)) :=
  ((AddMonoidHom.compLeft (algebraMap F (AdeleRing (𝓞 F) F)).toAddMonoidHom κ).prodMap
    (AddMonoidHom.compLeft (algebraMap F (AdeleRing (𝓞 F) F)).toAddMonoidHom κ)).range

theorem mem_ratPair_iff {F : Type} [Field F] [NumberField F] {κ : Type}
    (w : (κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F)) :
    w ∈ ratPair F κ ↔ ∃ y z : κ → F,
      w = (fun i => algebraMap F (AdeleRing (𝓞 F) F) (y i), fun i => algebraMap F (AdeleRing (𝓞 F) F) (z i)) := by
  constructor
  · rintro ⟨⟨y, z⟩, rfl⟩
    exact ⟨y, z, rfl⟩
  · rintro ⟨y, z, rfl⟩
    exact ⟨(y, z), rfl⟩

end GlobalTheory.WeilUnitaryTransport

end
