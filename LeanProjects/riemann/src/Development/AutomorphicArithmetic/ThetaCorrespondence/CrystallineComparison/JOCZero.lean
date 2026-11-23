import Development.AutomorphicArithmetic.ThetaCorrespondence.CrystallineComparison.ZeroEquiv
import Development.AutomorphicArithmetic.ThetaCorrespondence.CrystallineComparison.Zt2
import Development.AutomorphicArithmetic.ThetaCorrespondence.CrystallineComparison.Zt3

noncomputable section

namespace Formalism.BasicNotions.CmpTie.Incl

open GroundTheory.PAdicHodge

variable (l : ℕ) [Fact l.Prime]

set_option maxHeartbeats 200000 in
theorem jOC_zero (a : Reformulated.AutPerF.AcrisZero l (Cmp6.OC l)) :
    jOC l (algebraMap _ (Reformulated.AutPerF.Acris l (Cmp6.OC l)) a) =
      algebraMap (Reformulated.AutPerF.AinfInv l (Cmp6.OC l)) _ (a : Reformulated.AutPerF.AinfInv l (Cmp6.OC l)) := by
  show (Cmp6.cP l).symm (iotaP l (Cmp6.cA l (algebraMap _ _ a))) = _
  rw [RingEquiv.symm_apply_eq, Cmp6.cA_apply, Reformulated.AutPerF.Acris.map_algebraMap_zero, Cmp6.acrisNHom_algebraMap]
  erw [ACris.iota_of]
  simp only [Algebra.algebraMap_self, RingHom.id_apply]
  erw [zt1, zt2, zt3]

end Formalism.BasicNotions.CmpTie.Incl
