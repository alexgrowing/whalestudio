import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam

noncomputable section

namespace GlobalTheory.Hk3.HoweDuality

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

def intMat (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (a b : ℕ) :
    AddSubgroup (Matrix (Fin a) (Fin b) L) where
  carrier := {u | ∀ i j, u i j ∈ Formalism.UG.intL L}
  zero_mem' := fun _ _ => (Formalism.UG.intL L).zero_mem
  add_mem' := fun ha hb i j => (Formalism.UG.intL L).add_mem (ha i j) (hb i j)
  neg_mem' := fun ha i j => (Formalism.UG.intL L).neg_mem (ha i j)

def intVec (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (a : ℕ) : AddSubgroup (Fin a → L) where
  carrier := {u | ∀ i, u i ∈ Formalism.UG.intL L}
  zero_mem' := fun _ => (Formalism.UG.intL L).zero_mem
  add_mem' := fun ha hb i => (Formalism.UG.intL L).add_mem (ha i) (hb i)
  neg_mem' := fun ha i => (Formalism.UG.intL L).neg_mem (ha i)

theorem mem_intMat {a b : ℕ} (u : Matrix (Fin a) (Fin b) L) : u ∈ intMat L a b ↔ ∀ i j, u i j ∈ Formalism.UG.intL L := Iff.rfl

theorem mem_intVec {a : ℕ} (u : Fin a → L) : u ∈ intVec L a ↔ ∀ i, u i ∈ Formalism.UG.intL L := Iff.rfl

def latIdx {a b : ℕ} (x : Matrix (Fin a) (Fin b) L) : ℕ :=
  Nat.card (Set.range fun u : intVec L b => (QuotientAddGroup.mk (Matrix.mulVec x (u : Fin b → L)) : (Fin a → L) ⧸ intVec L a))

end GlobalTheory.Hk3.HoweDuality

end
