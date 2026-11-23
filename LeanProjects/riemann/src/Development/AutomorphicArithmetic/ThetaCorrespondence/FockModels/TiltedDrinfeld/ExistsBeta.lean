import Development.WeilBound.RepresentationTheoryGL.PeriodRingBases.FixedBaseSurjectivity.GaloisPeriodCyclotomic
import Development.WeilBound.RepresentationTheoryGL.PeriodRingBases.BaseThetaVanishing.BaseThZero
import Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.TiltedDrinfeld.TieQB
import Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.TiltedDrinfeld.CoeUntiltIterateLFlat

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace UpperTheory.Lit.Drps

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GroundTheory.PAdicHodge DeRhamPotentiallySemistable.DRPst

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P}

theorem exists_beta (T : LocTied6 l P AI) : ∃ β : ℚ_[l], ∀ g : GQ l,
    T.eB ((GlobalTheory.Pst.kummer P g : ℚ_[l]) • P.tB) =
      period_ring_base.qB l (period_ring_base.κ g) * period_ring_base.t l +
        (period_ring_base.σB g (period_ring_base.qB l β * period_ring_base.t l) - period_ring_base.qB l β * period_ring_base.t l) := by
  obtain ⟨a, b, ht, hr⟩ := Kum.exists_rel AI T
  have h1 : T.eB P.tB = period_ring_base.qB l (a : ℚ_[l]) * period_ring_base.t l := by
    apply period_ring_base.base_ι_inj l
    rw [map_mul, period_ring_base.base_ι_q, period_ring_base.period_image_eq, period_ring_base.BaseA.ι_eq, ← PositivityTheory.LocInh.tie_ι T, ht, map_mul,
      DeRhamTwist.Twist.tQ_eq]
    rfl
  refine ⟨(b : ℚ_[l]), fun g => ?_⟩
  have h2 : period_ring_base.κ g + period_ring_base.χ g * (b : ℚ_[l]) = b + a * (GlobalTheory.Pst.kummer P g : ℚ_[l]) := by
    have := congrArg (fun z : ℤ_[l] => (z : ℚ_[l])) (hr g)
    simp only [PadicInt.coe_add, PadicInt.coe_mul] at this
    exact this
  have h3 := congrArg (period_ring_base.qB l) h2
  simp only [map_add, map_mul] at h3
  rw [Algebra.smul_def, map_mul, period_ring_base.DualB.tie_qB T, h1, map_mul, period_ring_base.base_σ_q, period_ring_base.galois_period_cyclotomic]
  linear_combination (-(period_ring_base.t l)) * h3

end UpperTheory.Lit.Drps
