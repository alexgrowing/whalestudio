import Mathlib

namespace GlobalTheory.EtC

def IsExcisionNbhd (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] (f : A) : Prop :=
  Algebra.Etale A A' ∧ (∀ a' : A', ∃ a : A, a' - algebraMap A A' a ∈ Ideal.span {algebraMap A A' f}) ∧
    ∀ a : A, algebraMap A A' a ∈ Ideal.span {algebraMap A A' f} → a ∈ Ideal.span {f}

theorem isExcisionNbhd_self (A : Type) [CommRing A] (f : A) : IsExcisionNbhd A A f :=
  ⟨inferInstance, fun a' => ⟨a', by simp⟩, fun a h => by simpa using h⟩

end GlobalTheory.EtC
