import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsHalfSubMulLogOmLe

open NumberField Formalism.BasicNotions GlobalTheory.CovHt GlobalTheory.Mean4O

namespace GlobalTheory.FrameDegSize

theorem bound_of_value :
    (OnObj fun D O _ _ _ _ => ∀ (c : O.Y.Comp) (τ : D.what₂.Tau),
      haveI : NeZero D.host.d := ⟨D.host.hyp.2.1.ne_zero⟩
      GlobalTheory.ShFam.Pad.degFrame O.s O.Φ O.met.hm c τ =
        ((O.S.Dw.p : ℝ) - O.S.Dw.q) / 2 * (GlobalTheory.CM.logOm D.host.E (chiK D)).re) →
    OnObj fun D O _ _ _ _ => ∀ (c : O.Y.Comp) (τ : D.what₂.Tau),
      |GlobalTheory.ShFam.Pad.degFrame O.s O.Φ O.met.hm c τ| ≤ 7 * O.Y.N * (Real.log D.host.rdE + |dlogL D 1|) := by
  intro hv D O hO hf A T H h c τ
  rw [hv D O hO hf A T H h c τ]
  have key := abs_half_sub_mul_logOm_le D O.S.Dw.p O.S.Dw.q
  have hN : ((O.S.Dw.p : ℝ) + O.S.Dw.q) = (O.Y.N : ℝ) := by
    show ((O.S.Dw.p : ℝ) + O.S.Dw.q) = (O.N : ℝ)
    exact_mod_cast O.S.rank_eq
  rw [hN] at key
  exact key

end GlobalTheory.FrameDegSize
