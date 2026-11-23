import Formalism.PieriBlockIdeals.StatementLA

noncomputable section

namespace Formalism.CohomologicalDescent.LA

def InclZTwist : Prop :=
  ∀ (r : ℕ) (ν : Fin r → ℕ) (c l e : ℕ), Antitone ν → l.Prime →
    (InclZ r r le_rfl (fun a => ν a + c) l e ↔ InclZ r r le_rfl ν l e)

def ExZTwist : Prop :=
  ∀ (r : ℕ) (ν : Fin r → ℕ) (c l : ℕ), Antitone ν → l.Prime →
    exZ r r le_rfl (fun a => ν a + c) l = exZ r r le_rfl ν l

def ExZTranslate : Prop :=
  ∀ (r : ℕ) (U : Fin r → ℤ) (c l : ℕ), StrictAnti U → (∀ a, 0 ≤ U a) → l.Prime →
    exZ r r le_rfl (nuOf (fun a => U a + (c : ℤ))) l = exZ r r le_rfl (nuOf U) l

end Formalism.CohomologicalDescent.LA
