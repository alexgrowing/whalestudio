import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.ErrSum
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.IdxFull
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.IdxPsiGood
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.IdxRules
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.LemmaGG
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.Mirabolic
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.UnipotentNumeric
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.OnExport
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.OnLocal
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.OrthogonalityOfMackey
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.RamBasic
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.AbsorbLocalConditions
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.ThreeForms

namespace Formalism.EigenvalueLevelCeiling

theorem idxMono : IdxMono := index_monotone
theorem idxScaleIn : IdxScaleIn := index_scale_inclusion
theorem idxCutLe : IdxCutLe := index_truncation_le
theorem idxTransport : IdxTransport := index_transport
theorem latInter : LatInter := lattice_intersection
theorem threeForms : ThreeForms := three_forms
theorem threeFormsSum : ThreeFormsSum := three_forms_sum
theorem idxFull : IdxFull := by
  unfold IdxFull
  intro K _ _ _ Z _ _ _ _ _ w M Th ThK hM hTh hThK _ σ hσ hsc E r h
  obtain ⟨hL, heq⟩ := idxScaleIn K Z w ⊤ M ThK hM hThK σ hσ
  have hmono := idxMono K Z w ⊤ M Th (sc σ ThK) hM hTh hL hsc
  rw [heq, finrank_top] at hmono
  have h2 : (lix w M ThK : ℝ) + (Module.finrank K Z : ℝ) * (Formalism.DivisionValues.vw w σ : ℝ) ≤ (lix w M Th : ℝ) := by
    exact_mod_cast hmono
  nlinarith
theorem idxPsiGood : IdxPsiGood := idxPsiGood_of idxMono idxScaleIn idxCutLe latInter
theorem orthOfMackey : OrthOfMackey := orthogonality_of_mackey
theorem lemmaGG : LemmaGG := good_index_GG
theorem mackeyProd : MackeyProd := mackey_product
theorem mirabolicMackey : MirabolicMackey := mirabolic_mackey_pair
theorem mirabolicIsMackey : MirabolicIsMackey := mirabolic_is_mackey
theorem dataTrace : DataTrace := data_trace
theorem lengthRamified : LengthRamified := length_ramified
theorem onLocal : OnLocal := onLocal_of idxMono idxCutLe idxTransport latInter threeForms idxPsiGood lemmaGG
theorem ramBasic : RamBasic := ramified_basic_bound
theorem placeSum : PlaceSum := place_sum
theorem depthCases : DepthCases := depth_cases
theorem normaliserPair : NormaliserPair := normaliser_pair
theorem levelPair : LevelPair := level_pair
theorem shareNum : ShareNum := share_numeric
theorem unipNum : UnipNum := unipotent_numeric
theorem budgetNum : BudgetNum := budget_numeric
theorem errSumGood : ErrSumGood := by
  first
    | exact error_sum_good_places
    | exact errSumGood_of
    | exact errSumGood_thm
theorem onSum : OnSum := onSum_of placeSum ramBasic errSumGood
theorem absorbOn : AbsorbOn := absorb_local_conditions
theorem unitChange : UnitChange := unit_change'
theorem onExport : OnExport := by
  first
    | exact onExport_of_onExport2 (onExport2_of ramBasic)
    | exact onExport_proof'
    | exact onExport_of ramBasic

end Formalism.EigenvalueLevelCeiling
