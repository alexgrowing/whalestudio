import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Statements
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.AlgebraMapMemChartRingLine
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

def TwistTilde.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (E : Type v) [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
    (M : FinGradedSub (S := S) (x := x) E) (Q : FinGradedSub (S := S) (x := x) Ω),
    ∃ P : FinGradedSub (S := S) (x := x) E,
      (∀ c : ℤ, P.piece c = Submodule.span S {z | ∃ (a b : ℤ) (q : Ω) (m : E), q ∈ Q.piece a ∧
        m ∈ M.piece b ∧ a + b = c ∧ z = q • m}) ∧
      ∀ I, ((M.tildeSys 0).twist (Q.tildeSys 0)).sub I = P.tilde 0 I

end

end GroundTheory.Heights₂.Heights.Kleiman
