import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.FamilyGroupSumFactorsWeightAmplitude
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GenericTermsScalarClassesFormFamilyStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CorankOneScalarPairSymmetricStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ScalarCorankOnePairsTransStatement
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.SnFam
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SnFamGenAll

theorem famGen : GlobalTheory.SnFam.FamGen := by
  intro Cg cb Cw cT CT C0
  refine ⟨0, 0, ?_⟩
  intro C' Cl _ _ D large₂ X Y u u' _
  have hG : ∀ t : TauC Y u u', t ∈ (Y.tO u u').genSet → t.G ≠ 0 := by
    intro t ht h0
    have h1 : (Y.tO u u').G t ≠ 0 := ht.1
    apply h1
    show Gt t = 0
    simp [Gt, h0]
  exact GlobalTheory.T.genericTerms_scalarClasses_form_family D X Y u u'
    (fun t ht t' ht' _ hs hc => GlobalTheory.T.corank_one_scalar_pair_symmetric D X Y u u' t t' (hG t ht) (hG t' ht') hs hc)
    (fun t ht t' ht' t'' ht'' _ _ hs hc hs' hc' =>
      GlobalTheory.T.scalarCorankOnePairs_trans D X Y u u' t t' t'' (hG t ht) (hG t' ht') (hG t'' ht'') hs hc hs' hc')

end GlobalTheory.SnFamGenAll
