import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsConeComponents
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsConeChart
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.LocalMultRadical
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PRadicalBaseChange
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PGenericFibreIdeal
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar ptsIntegral ptsIntegralAt pot)

theorem complexFibreIdeal_isRadical {n d : ℕ} {P : Ideal (MRing (PBlk n))} (hP : IsArithVar P d) :
    (complexFibreIdeal P).IsRadical := by
  have hprime : (ObjectsChow.genericIdeal P).IsPrime :=
    (ObjectsChow.GenericFibreIdeal.proof n d P hP).1.isPrime
  have hcomp : (MvPolynomial.map (algebraMap ℚ ℂ)).comp (MvPolynomial.map (Int.castRingHom ℚ)) =
      (MvPolynomial.map (Int.castRingHom ℂ) : MvPolynomial (Fin n) ℤ →+* MvPolynomial (Fin n) ℂ) := by
    refine RingHom.ext fun p => ?_
    rw [RingHom.comp_apply, MvPolynomial.map_map,
      (RingHom.ext_int _ _ : (algebraMap ℚ ℂ).comp (Int.castRingHom ℚ) = Int.castRingHom ℂ)]
  have hmap : complexFibreIdeal P =
      (ObjectsChow.genericIdeal P).map (MvPolynomial.map (algebraMap ℚ ℂ)) := by
    rw [complexFibreIdeal, ObjectsChow.genericIdeal, Ideal.map_map, hcomp]
  rw [hmap]
  exact RadicalBaseChange.proof ℚ ℂ (algebraMap ℚ ℂ) (Fin n) _ hprime.isRadical

theorem ConeIntegralPts.proof (hC : ConeIntegralComponents.Statement)
    (hW : ConeIntegralChart.Statement) : ConeIntegralPts.Statement := by
  intro n e S hS P u hP hu
  have hrad := complexFibreIdeal_isRadical hP
  have hΨ := ReciprocityTheory.ChartRestriction.G.Geo.goodProjExists Unit (PBlk n) P e hP
  have hpts : ptsIntegral P (pot fun _ : Fin e => IndefiniteRowSideFullHecke.ArithBezout.hermLine S hS)
      (IndefiniteRowSideFullHecke.ArithBezout.logFormNorm S hS u) =
      ptsIntegralAt P hΨ.choose (pot fun _ : Fin e => IndefiniteRowSideFullHecke.ArithBezout.hermLine S hS)
        (IndefiniteRowSideFullHecke.ArithBezout.logFormNorm S hS u) := by
    unfold ptsIntegral
    rw [dif_pos hΨ]
  rw [hpts, ← hW n e S hS P u hΨ.choose hP hu hΨ.choose_spec, ← hC n e _ P u hP hu, cycleIntegral]
  refine Finset.sum_congr rfl fun W hWm => ?_
  rw [fundCycle_apply_of_isRadical hrad hWm, Nat.cast_one, one_mul]

end GroundTheory.Heights₂.Heights
