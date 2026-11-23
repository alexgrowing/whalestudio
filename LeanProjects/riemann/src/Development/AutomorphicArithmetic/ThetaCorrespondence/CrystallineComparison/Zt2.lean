import Development.AutomorphicArithmetic.ThetaCorrespondence.CrystallineComparison.LeafDefs
noncomputable section
namespace Formalism.BasicNotions.CmpTie.Incl
open GroundTheory.PAdicHodge
variable (l : ℕ) [Fact l.Prime]
set_option maxHeartbeats 200000 in
theorem zt2 (z : Reformulated.AutPerF.AinfInv l (NC l)) :
    toBDeRhamPlus (↥(normInteger ℂ_[l])) l z = algebraMap (Reformulated.AutPerF.AinfInv l (NC l)) (Reformulated.AutPerF.BdRPlus l (NC l)) z := rfl
end Formalism.BasicNotions.CmpTie.Incl
