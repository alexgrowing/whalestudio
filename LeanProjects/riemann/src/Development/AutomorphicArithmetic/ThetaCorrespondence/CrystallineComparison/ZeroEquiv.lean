import Development.AutomorphicArithmetic.ThetaCorrespondence.CrystallineComparison.LeafDefs
noncomputable section
namespace Formalism.BasicNotions.CmpTie.Incl
open GroundTheory.PAdicHodge
variable (l : ℕ) [Fact l.Prime]
set_option maxHeartbeats 200000 in
theorem zt1 (y : Reformulated.AutPerF.AcrisZero l (NC l)) :
    ((Cmp6.zeroEquiv l y : ACris.ACrisZero ℂ_[l] l) : Localization.Away ((l : ℕ) : AInf ℂ_[l] l)) =
      ((y : Reformulated.AutPerF.AcrisZero l (NC l)) : Reformulated.AutPerF.AinfInv l (NC l)) := by
  simp only [Cmp6.zeroEquiv, AlgEquiv.coe_ringEquiv, Subalgebra.equivOfEq_apply]
end Formalism.BasicNotions.CmpTie.Incl
