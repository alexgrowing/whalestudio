import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeReferenceFrame.PPAssemble

noncomputable section

open NumberField Formalism.MainNotions.S

namespace PI.ScRefExists.Sk

def WBasis : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (p r k : ℕ) (e f : Fin r → Fin I.n → I.E) (M : ℕ),
    p.Prime → IsPrincipalIdealRing (Ap I p) → I.n = 2 * r + k + 1 →
    (∀ a b, hG I (e a) (e b) = 0) → (∀ a b, hG I (f a) (f b) = 0) →
    (∀ a b, hG I (e a) (f b) = if a = b then 1 else 0) →
    Nat.Coprime M p → (∀ a, M • e a ∈ I.L ∧ M • f a ∈ I.L) →
    ∃ w : Fin (k + 1) → Fin I.n → I.E,
      (∀ i, w i ∈ LA I p ∧ ∀ a, hG I (e a) (w i) = 0 ∧ hG I (f a) (w i) = 0) ∧
      LinearIndependent I.E w ∧
      ∀ x ∈ LA I p, (∀ a, hG I (e a) x = 0 ∧ hG I (f a) x = 0) →
        x ∈ Submodule.span (Ap I p) (Set.range w)

end PI.ScRefExists.Sk
