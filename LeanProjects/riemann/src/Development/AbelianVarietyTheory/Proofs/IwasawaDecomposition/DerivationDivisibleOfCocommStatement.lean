import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DerivationDivisibleOfCocomm
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.IsOpenPart
open Formalism.MainNotions.DIV.Cons (intO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.derivation_divisible_of_cocomm : ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C] [CharZero C] (p : ℕ) [Fact p.Prime], ‖(p : C)‖ = (p : ℝ)⁻¹ → ∀ (A : Type) [CommRing A] [Bialgebra ↥(intO C) A] [Coalgebra.IsCocomm ↥(intO C) A] [Module.Finite ↥(intO C) A] [Module.Free ↥(intO C) A] (q : ↥(intO C)), q ≠ 0 → ∀ D : A →ₗ[↥(intO C)] ↥(intO C), (∀ a b : A, q ∣ D (a * b) - Coalgebra.counit (R := ↥(intO C)) a * D b - Coalgebra.counit (R := ↥(intO C)) b * D a) → (∀ u : A, IsGroupLikeElem ↥(intO C) u → q ∣ D u) → ∀ c : ↥(intO C), ‖(c : C)‖ ≤ (p : ℝ) ^ (-(1 / ((p : ℝ) - 1))) → ∀ a : A, q ∣ c * D a := by
  first | exact @GlobalTheory.GroupLikeDerivation.dvd_mul_of_groupLike | exact GlobalTheory.GroupLikeDerivation.dvd_mul_of_groupLike | (intros; apply GlobalTheory.GroupLikeDerivation.dvd_mul_of_groupLike <;> assumption)
