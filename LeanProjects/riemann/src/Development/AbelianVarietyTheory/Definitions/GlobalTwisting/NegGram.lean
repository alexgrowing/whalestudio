import Mathlib
import Formalism.LocalRingCardinality.DataSpaces

noncomputable section

open Formalism.BasicNotions NumberField

namespace GlobalTheory.NegSpace

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def neg (W : HSpace E) : HSpace E :=
  { W with
    hT := -W.hT
    herm := ⟨fun x y => by simpa using W.herm.eq x y⟩
    nondeg := ⟨fun x h => W.nondeg.1 x fun y => by simpa using h y,
      fun x h => W.nondeg.2 x fun y => by simpa using h y⟩
    sig := fun τ => ((W.sig τ).2, (W.sig τ).1)
    baseLattice_isUnimodular := by
      have h := W.baseLattice_isUnimodular
      have e : Formalism.HermitianLatticesTheory.dual (-W.hT) W.L0 = Formalism.HermitianLatticesTheory.dual W.hT W.L0 := by
        ext y
        simp [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf]
      unfold Formalism.HermitianLatticesTheory.IsUnimodular at h ⊢
      rw [e]; exact h }

theorem neg_rank (W : HSpace E) : (neg W).rank = W.rank := rfl

theorem neg_gram (W : HSpace E) : (neg W).gram = -W.gram := rfl

theorem neg_sig (W : HSpace E) (τ : E →+* ℂ) : (neg W).sig τ = ((W.sig τ).2, (W.sig τ).1) := rfl

end GlobalTheory.NegSpace
