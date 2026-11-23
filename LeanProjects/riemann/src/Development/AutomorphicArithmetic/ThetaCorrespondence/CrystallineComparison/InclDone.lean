import Development.AutomorphicArithmetic.ThetaCorrespondence.CrystallineComparison.InclAsm
import Development.AutomorphicArithmetic.ThetaCorrespondence.CrystallineComparison.LeafMain

noncomputable section

namespace Formalism.BasicNotions.CmpTie.Incl

variable (l : ℕ) [Fact l.Prime]

theorem incl_F (f : Reformulated.AutPerF.Bcris l (Cmp6.OC l) →+* Reformulated.AutPerF.BdR l (Cmp6.OC l)) :
    IsCrisDRF f ↔ Formalism.Per6.IsCrisDR l (((Cmp6.cD l).toRingHom.comp f).comp (Cmp6.cBc l).symm.toRingHom) :=
  incl_native l (comparison_toBdRPlus l) f

end Formalism.BasicNotions.CmpTie.Incl
