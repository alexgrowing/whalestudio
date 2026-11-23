import Mathlib
import Formalism.PeriodIntegrals.CharIdem

open CategoryTheory

namespace PI.CharIdemW

open PI.CharIdem

def Central : Prop :=
  ∀ (G : Type) [Group G] [Fintype G] (V : FDRep ℂ G) (x : MonoidAlgebra ℂ G),
    charIdem V * x = x * charIdem V

def Scalar : Prop :=
  ∀ (G : Type) [Group G] [Fintype G] (V W : FDRep ℂ G), Simple V → Simple W →
    (Nonempty (V ≅ W) → act W (charIdem V) = 1) ∧
    (IsEmpty (V ≅ W) → act W (charIdem V) = 0)

def MulEq : Prop :=
  ∀ (G : Type) [Group G] [Fintype G] (V W : FDRep ℂ G), Simple V → Simple W →
    (Nonempty (V ≅ W) → charIdem V * charIdem W = charIdem W) ∧
    (IsEmpty (V ≅ W) → charIdem V * charIdem W = 0)

theorem charIdem_of (hC : Central) (hS : Scalar) (hM : MulEq) : PI.CharIdem.CharIdem := by
  intro G _ _ V W hV hW
  refine ⟨(hS G V V hV hV).1 ⟨Iso.refl V⟩, (hS G V W hV hW).2, ?_, hC G V, (hM G V W hV hW).2⟩
  exact (hM G V V hV hV).1 ⟨Iso.refl V⟩

end PI.CharIdemW
