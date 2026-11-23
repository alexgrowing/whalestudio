import Mathlib
import Development.WeilBound.CoreStatements.PeriodRingComparison.CrystallinePeriodRings.GammaEqDpow
import Development.WeilBound.CoreStatements.PeriodRingComparison.CrystallinePeriodRings.AcrisNAlgebraMapAinf
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.Period
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.Embedding
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.DeRhamMap
import Development.WeilBound.CoreStatements.CrystallinePeriodRings.ExistsMapEqOfPowMul

noncomputable section

open GroundTheory.PAdicHodge

namespace Cmp6

variable (l : ℕ) [Fact l.Prime]

def cP : Reformulated.AutPerF.BdRPlus l (OC l) ≃+* Formalism.Per6.BdRp l :=
  Reformulated.AutPerF.BdRPlus.mapEquiv l (e l)

theorem cP_apply (y : Reformulated.AutPerF.BdRPlus l (OC l)) :
    cP l y = Reformulated.AutPerF.BdRPlus.map l (e l).toRingHom y := rfl

theorem comparison_algebraMap_ainf (a : Reformulated.AutPerF.Ainf l (OC l)) :
    cP l (algebraMap _ (Reformulated.AutPerF.BdRPlus l (OC l)) a) = Formalism.Per6.aD l a := by
  rw [cP_apply, Reformulated.AutPerF.BdRPlus.map_algebraMap_ainf, ainfMap_eq]
  rfl

theorem awayEquiv_awayMap (z : Localization.Away ((l : ℕ) : OC l)) :
    IsPerfectoidField.awayEquiv (K := ℂ_[l]) l (Reformulated.AutPerF.awayMap l (e l).toRingHom z) =
      Reformulated.AutPerF.IsUnitBall.awayEquiv (PadicComplexInt l) l z := by
  have h : (IsPerfectoidField.awayEquiv (K := ℂ_[l]) l).toRingEquiv.toRingHom.comp
      (Reformulated.AutPerF.awayMap l (e l).toRingHom) =
      (Reformulated.AutPerF.IsUnitBall.awayEquiv (PadicComplexInt l) l).toRingEquiv.toRingHom := by
    refine IsLocalization.ringHom_ext (Submonoid.powers ((l : ℕ) : OC l)) (RingHom.ext fun x => ?_)
    simp only [RingHom.comp_apply]
    rw [Reformulated.AutPerF.awayMap_algebraMap]
    change IsPerfectoidField.awayEquiv (K := ℂ_[l]) l (algebraMap (NC l) _ (e l x)) =
      Reformulated.AutPerF.IsUnitBall.awayEquiv (PadicComplexInt l) l (algebraMap (OC l) _ x)
    rw [AlgEquiv.commutes, Reformulated.AutPerF.IsUnitBall.awayEquiv_algebraMap]
    rfl
  exact RingHom.congr_fun h z

theorem θD_cP (y : Reformulated.AutPerF.BdRPlus l (OC l)) :
    Formalism.Per6.θD l (cP l y) = Reformulated.AutPerF.BdRPlus.thetaC l (PadicComplexInt l) y := by
  change IsPerfectoidField.awayEquiv (K := ℂ_[l]) l
      (Reformulated.AutPerF.BdRPlus.theta l (NC l) (Reformulated.AutPerF.BdRPlus.map l (e l).toRingHom y)) = _
  rw [Reformulated.AutPerF.BdRPlus.theta_map, Reformulated.AutPerF.BdRPlus.thetaC_apply]
  exact awayEquiv_awayMap l _

end Cmp6
