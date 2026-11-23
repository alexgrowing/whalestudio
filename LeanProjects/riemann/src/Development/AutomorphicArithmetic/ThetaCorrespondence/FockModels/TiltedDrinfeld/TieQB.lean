import Development.WeilBound.RepresentationTheoryGL.PeriodRingBases.PeriodRingUnits.DieudonneManinBasisModification
import Development.WeilBound.CoreStatements.CrystallinePeriodRings.MaximalIdealEqSpanT

noncomputable section

namespace period_ring_base.DualB

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GroundTheory.PAdicHodge

variable {l : ℕ} [Fact l.Prime]

theorem qB_eq (q : ℚ_[l]) : PositivityTheory.LocInh.qB l q = period_ring_base.qB l q :=
  RingHom.congr_fun (IsLocalization.ringHom_ext (nonZeroDivisors ℤ_[l]) (S := ℚ_[l])
    (j := PositivityTheory.LocInh.qB l) (k := period_ring_base.qB l)
    (RingHom.ext fun z => by
      simp only [RingHom.comp_apply]
      rw [show (algebraMap ℤ_[l] ℚ_[l] z) = (z : ℚ_[l]) from rfl, PositivityTheory.LocInh.qB_coe]
      exact (IsLocalization.lift_eq (M := nonZeroDivisors ℤ_[l]) (isUnit_zB l) z).symm)) q

variable {P : LocPrime l} {AI : LocAinf l P} (T : LocTied6 l P AI)

theorem tie_qB (q : ℚ_[l]) : T.eB (algebraMap ℚ_[l] P.R.B q) = period_ring_base.qB l q :=
  (PositivityTheory.LocInh.tie_q T q).trans (qB_eq q)

theorem tie_σB (g : GQ l) (b : P.R.B) : T.eB (P.actQ g b) = period_ring_base.σB g (T.eB b) := T.actB g b

end period_ring_base.DualB
