import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspidalFlipOnVolumes
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.CuspidalLiftSmoothAtOfCuspidalLift
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.CuspTransitionRightward
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.FlipRunDescendingCuspTransition
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspidalFlipOnVolumesStatement

section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
namespace GlobalTheory.FlipRun
theorem cuspStep_of_large_flipRun : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.RowClaim.Big fun {_} _ _ _ _ {T} _ _ _ _ _ _ ch => ∀ (t : T) (M : Vol ch.G), M.Is t → GlobalTheory.FlipRun.CuspStep ch.W M ch.rm t := by
  intro hLC hP
  have hS := _root_.GlobalTheory.T.cuspidal_lift_smooth_at_cusps hLC hP
  refine (GlobalTheory.RowClaim.Big.and (_root_.GlobalTheory.T.cusp_transition_rightward hS hP) (_root_.GlobalTheory.T.flipRun_descending_cusp_transition hS hP)).imp fun CF0 h ε CF hC => ?_
  obtain ⟨x₀, h⟩ := h ε CF hC
  refine ⟨x₀, fun D large₂ e hx Γ _ _ Pl0 T A Ks _ _ _ R F s ch hch hsc t M hM a ha e' he φ f hf Q F' hF => ?_⟩
  have H := h D large₂ e hx Γ Pl0 T A Ks R F s ch hch hsc
  rcases ha with ⟨i, j, hi, hj, rfl⟩ | ⟨i, j, hi, hj, rfl⟩
  · exact H.1 t M hM _ (Or.inl ⟨i, j, hi, hj, rfl⟩) ⟨i, j, rfl⟩ e' he φ f hf Q F' hF
  · exact H.2 t M hM _ (Or.inr ⟨i, j, hi, hj, rfl⟩) ⟨i, j, rfl⟩ e' he φ f hf Q F' hF
end GlobalTheory.FlipRun
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flipRun_cusp_transition : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.RowClaim.Big fun {_} _ _ _ _ {T} _ _ _ _ _ _ ch => ∀ (t : T) (M : Vol ch.G), M.Is t → GlobalTheory.FlipRun.CuspStep ch.W M ch.rm t := by
  first | exact @_root_.GlobalTheory.FlipRun.cuspStep_of_large_flipRun | exact _root_.GlobalTheory.FlipRun.cuspStep_of_large_flipRun | (intros; apply _root_.GlobalTheory.FlipRun.cuspStep_of_large_flipRun <;> assumption)
end
