import Development.AutomorphicArithmetic.ThetaCorrespondence.CrystallineComparison.Bridge
import Development.AutomorphicArithmetic.ThetaCorrespondence.CrystallineComparison.IsCrisDRAToBdRPlusIff
import Development.AutomorphicArithmetic.ThetaCorrespondence.CrystallineComparison.IsCrisDRAIff
import Development.WeilBound.CoreStatements.PeriodRingComparison.CrystallinePeriodRings.Assembly

noncomputable section

namespace Formalism.BasicNotions.CmpTie.Incl

open GroundTheory.PAdicHodge

variable (l : ℕ) [Fact l.Prime]

theorem incl_native
    (hι : ∀ x : Reformulated.AutPerF.Acris l (Cmp6.OC l),
      Cmp6.cP l (Reformulated.AutPerF.Acris.toBdRPlus l (Cmp6.OC l) x) = ACris.iota ℂ_[l] l (Cmp6.cA l x))
    (f : Reformulated.AutPerF.Bcris l (Cmp6.OC l) →+* Reformulated.AutPerF.BdR l (Cmp6.OC l)) :
    IsCrisDRF f ↔ Formalism.Per6.IsCrisDR l (((Cmp6.cD l).toRingHom.comp f).comp (Cmp6.cBc l).symm.toRingHom) := by
  rw [isCrisDRF_iff, ← isCrisDRA_toBdRPlus_iff]
  exact isCrisDRA_iff (Cmp6.cA l) (Cmp6.cBc l) (Cmp6.cP l) (Cmp6.cD l) (Reformulated.AutPerF.Acris.toBdRPlus l (Cmp6.OC l))
    (fun x => Cmp6.cBc_algebraMap l x) (fun y => Cmp6.cD_algebraMap l y) hι f

end Formalism.BasicNotions.CmpTie.Incl
