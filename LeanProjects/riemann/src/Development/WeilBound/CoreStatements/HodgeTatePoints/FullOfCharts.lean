import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.AssemblyBase
import Development.WeilBound.CoreStatements.HodgeTatePoints.ExistsLineBundleTwistMulOf
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PClaimVanish
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PVeryAmpleNefPlusAmple

namespace PositivityTheory.HtPt.KtwS

open GroundTheory.Heights₂.Heights.Kleiman

universe u v w

theorem LineTwist.full_of_charts : LineTwist.Statement.{u, w} :=
  fun _ _ _ _ _ _ _ Q₁ Q₂ => ⟨KThm.lbTwist Q₁ Q₂, rfl⟩

theorem TwistAlg.full_of_charts : TwistAlg.Statement.{u, w} := by
  intro S _ Ω _ _ N x M p q m m' b₁ b₂ h
  refine SubSystem.ext_sub fun I => ?_
  obtain ⟨i, hi⟩ := I.2.1
  rw [KThm.sub_twist, KThm.sub_pow, KThm.sub_pow, KThm.sub_pow, KThm.sub_twistMul M p m I hi,
    KThm.sub_twistMul M q m' I hi, mul_pow, mul_pow, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul,
    KThm.span_zpow_pow I hi, KThm.span_zpow_pow I hi, KThm.span_zpow_pow I hi, mul_mul_mul_comm,
    ← pow_add, KThm.span_zpow_mul I hi]
  have e1 : p * (q * b₁ + b₂) = q * (p * b₁) + p * b₂ := by ring
  have e2 : m * ((q * b₁ + b₂ : ℕ) : ℤ) = m' * ((p * b₁ : ℕ) : ℤ) + m * (b₂ : ℤ) := by
    push_cast
    linear_combination (b₁ : ℤ) * h
  rw [e1, e2]

theorem StepTwo.assembled (hRed : StepTwo.Reduce.Statement.{u, v, w})
    (hRL : RestrLenRestrict.Statement.{u, w}) (hRQ : PrimeFiltration.RestrictQuot.Statement.{u, w})
    (hS : TwistSplit.Statement.{u, w}) : StepTwo.Statement.{u, v, w} :=
  StepTwo.proof hRed LineTwist.full_of_charts TwistAlg.full_of_charts RestrictTwist.full
    (NefRestrict.assembled hRL) StepData.JProper.full SubvarDrop.full PrimeFiltration.Point.full
    PrimeFiltration.Restrict.full hRQ (TwistVanish.assembled hS)

theorem ClaimVanish.assembled (hRed : StepTwo.Reduce.Statement.{u, w, w})
    (hRL : RestrLenRestrict.Statement.{u, w}) (hRQ : PrimeFiltration.RestrictQuot.Statement.{u, w})
    (hS : TwistSplit.Statement.{u, w}) (hCS : ClaimSeq.Statement.{u, w}) : ClaimVanish.Statement.{u, w} :=
  ClaimVanish.proof (StepTwo.assembled hRed hRL hRQ hS) (TwistVanish.assembled hS) hCS

end PositivityTheory.HtPt.KtwS
