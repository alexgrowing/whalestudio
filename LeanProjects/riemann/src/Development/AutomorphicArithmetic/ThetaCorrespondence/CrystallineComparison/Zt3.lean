import Development.AutomorphicArithmetic.ThetaCorrespondence.CrystallineComparison.LeafDefs
noncomputable section
namespace Formalism.BasicNotions.CmpTie.Incl
open GroundTheory.PAdicHodge
variable (l : ℕ) [Fact l.Prime]
set_option maxHeartbeats 200000 in
theorem zt3 (a : Reformulated.AutPerF.AcrisZero l (Cmp6.OC l)) :
    ((Reformulated.AutPerF.AcrisZero.map l (Cmp6.e l).toRingHom a : Reformulated.AutPerF.AcrisZero l (NC l)) : Reformulated.AutPerF.AinfInv l (NC l)) =
      Reformulated.AutPerF.AinfInv.map l (Cmp6.e l).toRingHom (a : Reformulated.AutPerF.AinfInv l (Cmp6.OC l)) :=
  Reformulated.AutPerF.AcrisZero.coe_map _ _
end Formalism.BasicNotions.CmpTie.Incl
