import Mathlib

namespace Bl.FirstBlockLemmaE

theorem goal1 :
  ∀ {L : Type} [inst : Field.{0} L] [NumberField.{0} L] (x : L) (c : Int),
  Eq.{1} (HPow.hPow.{0, 0, 0} x 2) (HAdd.hAdd.{0, 0, 0} x (Int.cast.{0} c)) →
    Exists.{1} fun (X : NumberField.RingOfIntegers.{0} L) ↦
      And (Eq.{1} (NumberField.RingOfIntegers.val.{0} X) x)
        (Eq.{1} (HPow.hPow.{0, 0, 0} X 2) (HAdd.hAdd.{0, 0, 0} X (Int.cast.{0} c))) := by
  intro L _ _ x c h
  have hi : IsIntegral ℤ x := by
    refine ⟨Polynomial.X ^ 2 - (Polynomial.X + Polynomial.C c), ?_, ?_⟩
    · monicity!
    · simp only [Polynomial.eval₂_sub, Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_X, Polynomial.eval₂_C, h]
      simp
  refine ⟨⟨x, hi⟩, rfl, ?_⟩
  apply NumberField.RingOfIntegers.coe_injective
  exact h

end Bl.FirstBlockLemmaE
