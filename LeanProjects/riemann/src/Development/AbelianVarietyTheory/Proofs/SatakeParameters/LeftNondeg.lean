import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition

noncomputable section
open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory.PD
open GlobalTheory.EtC

def Hyps : Prop :=
  A1 ∧ A2 ∧ A3 ∧ A4 ∧ A5 ∧ DivisorNaturality ∧ DivisorRingCompatibility ∧ DivisorSupportCondition ∧ DivisorAdditivity ∧ A7 ∧ A8 ∧ A9 ∧ A10 ∧ A11 ∧
  B1 ∧ B2 ∧ B3 ∧ B4 ∧ B5 ∧ DivisorPicardCompatibility ∧ B6h1 ∧ B7 ∧ C1 ∧ C2 ∧ C3 ∧ C4 ∧ C5 ∧ D1 ∧ D2 ∧ D3 ∧
  E1 ∧ E2 ∧ E3 ∧ E4 ∧ E6

def LeftNondeg (q : ℕ) (E : Spc) (d : ℕ) (n i : ℤ) : Prop :=
  ∀ a : Ht q E n i, a ≠ 0 → ∃ b : Ht q E (2 * d - n) (d - i), cup q a b ≠ 0

end GlobalTheory.PD

end
