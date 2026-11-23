import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthAddMonoidHomFiniteGroupFractionQuotientLe
import Mathlib
import Formalism.CharacterColumnKernels.StatementRho
open Formalism.NG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.length_addMonoidHom_finite_group_fractionQuotient_le : ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra ℤ_[l] O] (M : Type) [AddCommGroup M] [Module O M] (eM : M ≃ₗ[O] KO O)
    (A : Type) [AddCommGroup A] [Finite A],
    Module.length O (A →+ M) ≤
      Module.length O (O ⧸ Ideal.span {(l : O)}) * (padicValNat l (Nat.card A) : ℕ∞) := by
  first | exact @GlobalTheory.HomLen.length_addMonoidHom_le | exact GlobalTheory.HomLen.length_addMonoidHom_le | (intros; apply GlobalTheory.HomLen.length_addMonoidHom_le <;> assumption)
