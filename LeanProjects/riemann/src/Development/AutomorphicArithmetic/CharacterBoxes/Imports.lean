import Development.AutomorphicArithmetic.CoprimeRanks.SecondSetNoRelation

noncomputable section

namespace UpperTheory.Top

open Formalism.BasicNotions Formalism.HC HostParam.Seam

def admitted (R : Ranks) (H0 : HostAx R.toFrame) : Prop :=
  ∀ (b : ℕ) (c : Choices R.toFrame H0.toHostRaw), FieldRows H0.toHostRaw b →
    (4 * R.t * R.r + 1 < H0.q ∧ 4 * R.t * R.r + 1 < H0.d) →
    ∃ D : Host R, D.toHostAx = H0 ∧ D.splitBound = b ∧ HEq (HostNF.ofHost D).ch c

end UpperTheory.Top

end
