import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointShiftSt

set_option autoImplicit false

noncomputable section

open NumberField

namespace GlobalTheory.IdxTensor

def dets (F : Type) [Field F] [NumberField F] (p : ℕ) (L : Submodule (𝓞 F) (Fin p → F)) : Submodule (𝓞 F) F :=
  Submodule.span (𝓞 F) {d | ∃ y : Fin p → Fin p → F, (∀ i, y i ∈ L) ∧ d = (Matrix.of y).det}

example (F : Type) [Field F] [NumberField F] (p : ℕ) :
    (1 : F) ∈ dets F p (Submodule.span (𝓞 F) (Set.range fun a => (Pi.single a (1 : F) : Fin p → F))) :=
  Submodule.subset_span ⟨fun a => Pi.single a 1, fun i => Submodule.subset_span ⟨i, rfl⟩, by
    rw [show (Matrix.of fun a : Fin p => (Pi.single a (1 : F) : Fin p → F)) = 1 from by
      ext i j; simp [Matrix.one_apply, Pi.single_apply, eq_comm], Matrix.det_one]⟩

end GlobalTheory.IdxTensor

end
