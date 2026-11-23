import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PathConvergenceHorizontalTheta
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.CuspStepOfLargeFlipRun
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistCuspLiftMemCuspList
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PathConvergenceHorizontalThetaStatement

section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
namespace GlobalTheory.RowStart
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}
end GlobalTheory.RowStart
namespace GlobalTheory.RowStart
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}
end GlobalTheory.RowStart
namespace GlobalTheory.RowStart
theorem theta_tower_first_occurrence_exists : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → GlobalTheory.RowClaim.Big fun {D} _ _ _ _ {T} _ _ _ _ _ {R} ch => ∀ (t : T) (Φ : ch.G.Datum) (M : Vol ch.G), M.Is t → ∀ y : (R.HX t).H, PathConv ch.W M (rowPath T 0 D.R.m) (rowDatum ch.W ch.ρ Φ) (ch.cv.lift t y) ∧ thetaChi ch.W ch.M ch.ρ Φ (ch.cv.lift t y) = liftP ch.W M (rowPath T 0 D.R.m) (rowDatum ch.W ch.ρ Φ) (ch.cv.lift t y) := by
  intro hP hLC
  refine ((_root_.GlobalTheory.FlipRun.cuspStep_of_large_flipRun hLC hP).and ((_root_.GlobalTheory.T.twist_cusp_lift_mem_cuspList hP hLC).and (GlobalTheory.T.firstRow_cosetVectors_isLocalThetaVector.and GlobalTheory.T.firstRowSchwartzData_isThetaFunction_largeDepth))).imp fun CF0 h ε CF hC => ?_
  obtain ⟨x₀, h⟩ := h ε CF hC
  refine ⟨x₀, fun D large₂ e hx Γ _ _ Pl0 T A Ks _ _ _ R F s ch hch hsc t Φ M hM y => ?_⟩
  obtain ⟨hstep, hcusp, hloc, hth⟩ := h D large₂ e hx Γ Pl0 T A Ks R F s ch hch hsc
  have H := rowCore ch.W ch.M M ch.rm t ch.ρ Φ (hstep t M hM) (hloc t) (fun i => hth Φ i) hch.vol hM.isRow
    (ch.cv.lift t y) (hcusp t y) D.R.m le_rfl
  exact ⟨H.1, H.2.2⟩
end GlobalTheory.RowStart
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_theta_tower_first_occurrence_exists : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → GlobalTheory.RowClaim.Big fun {D} _ _ _ _ {T} _ _ _ _ _ {R} ch => ∀ (t : T) (Φ : ch.G.Datum) (M : Vol ch.G), M.Is t → ∀ y : (R.HX t).H, PathConv ch.W M (rowPath T 0 D.R.m) (rowDatum ch.W ch.ρ Φ) (ch.cv.lift t y) ∧ thetaChi ch.W ch.M ch.ρ Φ (ch.cv.lift t y) = liftP ch.W M (rowPath T 0 D.R.m) (rowDatum ch.W ch.ρ Φ) (ch.cv.lift t y) := by
  first | exact @_root_.GlobalTheory.RowStart.theta_tower_first_occurrence_exists | exact _root_.GlobalTheory.RowStart.theta_tower_first_occurrence_exists | (intros; apply _root_.GlobalTheory.RowStart.theta_tower_first_occurrence_exists <;> assumption)
end
