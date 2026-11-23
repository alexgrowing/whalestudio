import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsHermPairSelf

noncomputable section

namespace GlobalTheory.ColumnForm

variable {V : Type} [AddCommGroup V] [Module ℂ V]

def IsProj {X : Type} [AddCommGroup X] (u : Representation ℂ (Multiplicative X) V) (L : AddSubgroup X) (χ : L → ℂ)
    (E : Module.End ℂ V) : Prop :=
  IsAvg u L χ E ∧ ∀ y, (∀ x : L, u (Multiplicative.ofAdd (x : X)) y = χ x • y) → E y = y

theorem isProj_bot {X : Type} [AddCommGroup X] (u : Representation ℂ (Multiplicative X) V) :
    IsProj u ⊥ (fun _ => 1) 1 := ⟨isAvg_bot u, fun _ _ => rfl⟩

end GlobalTheory.ColumnForm

end
