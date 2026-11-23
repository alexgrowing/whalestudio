import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GenericPointSectionHypotheses
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

def ClaimSeq.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (T : StepData k x),
    ∃ Jg : FinGradedSub (S := k) (x := x) Ω,
      (∀ c : ℤ, Jg.piece c = Submodule.span k {z | ∃ (f : Poly k N) (e : ℕ), f ∈ T.J ∧
        f.IsHomogeneous e ∧ (e : ℤ) = c ∧ z = aeval x f}) ∧
      ∀ (b : ℕ) (c : ℤ) (I : Chart x) (z : Ω),
        z ∈ ((Jg.tildeSys 0).twist ((T.L.pow (b + 1)).twist (twistSys k x c))).sub I ↔
          ∃ y ∈ ((T.L.pow b).twist (twistSys k x (c + T.c₁))).sub I, z = T.si * y

end

end GroundTheory.Heights₂.Heights.Kleiman
