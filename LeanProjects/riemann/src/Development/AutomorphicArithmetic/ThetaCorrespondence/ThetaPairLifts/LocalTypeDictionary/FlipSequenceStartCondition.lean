import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GivenPathRepresentationFinite
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.FlipSequenceStartColumn
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedThetaTowerFirstOccurrenceExists
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedThetaFirstOccurrenceFiniteSwappedPair
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GivenPathRepresentationFiniteStatement

section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
namespace GlobalTheory.FlipStart
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}
end GlobalTheory.FlipStart
open GlobalTheory.FlipStart in
theorem GlobalTheory.FlipStart.flipSequence_start_condition : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → GlobalTheory.RowClaim.Big fun {D} _ _ _ _ {T} _ _ _ _ _ {R} ch => ∃ Pg : GlobalTheory.FlipRun.PolE ch.G →₀ ℂ, ∀ t : T, ∃ z : ℂˣ, z ∈ GlobalTheory.RowClaim.xiVals R.toLevCh t ∧ ∀ Φ : ch.G.Datum, ∃ τg : TotT ch.G (GlobalTheory.FunObj.givenPath t D.R.m), GlobalTheory.FlipRun.RepFin ch.S.B ch.rm t (GlobalTheory.FunObj.givenPath t D.R.m) τg (fun w => (givenStage t w ch.S.B Φ).tensor) ∧ ∀ M : Vol ch.G, M.Is t → ∀ y, TotConv ch.W M _ (GlobalTheory.FlipRun.tensE ch.W _ Pg τg) (GlobalTheory.RowClaim.formTop ch t y) ∧ thetaChi ch.W ch.M ch.ρ Φ (ch.cv.lift t y) = (z : ℂ)⁻¹ • liftT ch.W M _ (GlobalTheory.FlipRun.tensE ch.W _ Pg τg) (GlobalTheory.RowClaim.formTop ch t y) := by
  intro hP hC
  obtain ⟨a, h⟩ := ((_root_.GlobalTheory.T.flipSequence_column_succ hP hC).and (_root_.GlobalTheory.T.twisted_theta_tower_first_occurrence_exists hP hC)).and (_root_.GlobalTheory.T.twisted_theta_first_occurrence_finite_swapped_pair hP)
  refine ⟨a, fun ε CF hCF => ?_⟩
  obtain ⟨x, h⟩ := h ε CF hCF
  refine ⟨x, fun D large₂ e hx Γ _ _ Pl0 T A Ks _ _ _ R F s ch i j => ?_⟩
  obtain ⟨⟨hcol, hrow⟩, hfin⟩ := h D large₂ e hx Γ Pl0 T A Ks R F s ch i j
  obtain ⟨q, hq⟩ := exists_chainPols ch
  refine ⟨Finsupp.single (gPol ch.ρ q) 1, fun t => ?_⟩
  obtain ⟨f, hf⟩ := exists_chainVecs ch t
  obtain ⟨z, hz, hrep⟩ := hfin t f hf
  refine ⟨z, hz, fun Φ => ⟨Finsupp.single (givenFin ch.W t f Φ) (z : ℂ), hrep Φ, fun M hM y => ?_⟩⟩
  obtain ⟨hc1, hc2⟩ := hcol t f q hf hq M hM y
  obtain ⟨hr1, hr2⟩ := hrow t Φ M hM y
  rw [tensE_single]
  refine ⟨fun d hd => ?_, ?_⟩
  · have hd' := Finsupp.support_single_subset hd
    rw [Finset.mem_singleton] at hd'
    subst hd'
    rw [zip_given]
    refine (pathConv_comp ch.W M _ _ _ _ _).2 ⟨hc1, ?_⟩
    rw [hc2]
    exact hr1
  · rw [liftT_single, zip_given]
    unfold givenPath
    rw [pathLift_comp, hc2, ← hr2, smul_smul, inv_mul_cancel₀ (Units.ne_zero z), one_smul]
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flipSequence_initial_term : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → GlobalTheory.RowClaim.Big fun {D} _ _ _ _ {T} _ _ _ _ _ {R} ch => ∃ Pg : GlobalTheory.FlipRun.PolE ch.G →₀ ℂ, ∀ t : T, ∃ z : ℂˣ, z ∈ GlobalTheory.RowClaim.xiVals R.toLevCh t ∧ ∀ Φ : ch.G.Datum, ∃ τg : TotT ch.G (GlobalTheory.FunObj.givenPath t D.R.m), GlobalTheory.FlipRun.RepFin ch.S.B ch.rm t (GlobalTheory.FunObj.givenPath t D.R.m) τg (fun w => (givenStage t w ch.S.B Φ).tensor) ∧ ∀ M : Vol ch.G, M.Is t → ∀ y, TotConv ch.W M _ (GlobalTheory.FlipRun.tensE ch.W _ Pg τg) (GlobalTheory.RowClaim.formTop ch t y) ∧ thetaChi ch.W ch.M ch.ρ Φ (ch.cv.lift t y) = (z : ℂ)⁻¹ • liftT ch.W M _ (GlobalTheory.FlipRun.tensE ch.W _ Pg τg) (GlobalTheory.RowClaim.formTop ch t y) := by
  first | exact @_root_.GlobalTheory.FlipStart.flipSequence_start_condition | exact _root_.GlobalTheory.FlipStart.flipSequence_start_condition | (intros; apply _root_.GlobalTheory.FlipStart.flipSequence_start_condition <;> assumption)
end
