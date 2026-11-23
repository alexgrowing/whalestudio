import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodProjectorSmallestSpaceForms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InnerThetaStepsPreserveFaceLevelStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LastThetaStepKeepsFaceLevelStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowProjHolds
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.Mem.R3.DTheta

set_option maxHeartbeats 4000000 in

theorem composite_eq_lift : (GlobalTheory.Published.DiscreteSeriesCover ∧ GlobalTheory.Published.HarishChandraModules ∧ GlobalTheory.Published.CasselmanWallach ∧ GlobalTheory.Published.HarishChandraFinite ∧ GlobalTheory.Published.CuspRapidDecay) → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0), Pins R F cG → Holds R F → (∀ t x, (Y.Ish.jE (D.what₂.iota (Y.tup t) (Y.jA t x))).1 = PiTensorProduct.lift (R.HE.e (R.Th t (R.jX t (rowForm A3.A F.P1 F.ψ1 t x))))) ∧ ∀ t x, (Y.Iz.jE (X0.s.iota (Y.tup t) (Y.jA0 t x))).1 = PiTensorProduct.lift (R.HE.e (R.Th t (R.jX t (rowForm A3.A F.P0 F.ψ0 t x)))) := by
  intro hC D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y hPins hHolds
  have hch : R.toRealDat.IsChain := RealDat.chain_of_weak hPins.char.base.chain hHolds.aux.ex
  have hS : StepLev R.toRealDat F.lv2 := GlobalTheory.T.innerThetaSteps_preserve_faceLevel hC D G Pl0 I0 T A3 Ks R F cG hPins hHolds
  have hT : TopLev R.toRealDat F.lv2 := GlobalTheory.T.lastThetaStep_keeps_faceLevel hC D G Pl0 I0 T A3 Ks R F cG hPins hHolds
  have hP : RowProj R.toRealDat F.lv2 := rowProj_holds hC.2.2.2.2 D G Pl0 I0 T A3 Ks R F cG hPins hHolds
  have hUsed : ∀ t, Used0 D (Y.tup t) := by
    intro t
    rcases hPins.char.tup.mu_used t with h | ⟨w, hw⟩
    · left
      rw [h]
      exact Y.tup0
    · right
      refine ⟨D.plEq.symm w, ?_⟩
      rw [Y.muAt, Equiv.apply_symm_apply, hw]
  refine ⟨fun t x => ?_, fun t x => ?_⟩
  · rw [iota_sharp]
    exact iota_eq_real' R.toRealDat F.lv2 Y.tupT Y.hm Y.hTop hch hS hT hP (RowSide.sharp D) true Y.Ish Y.tied.sharp
      (Y.tup t) (hUsed t) (Y.jA t x) t (Y.tupT_tup t) _ (Y.topRead t (hUsed t) x)
  · exact iota_eq_real' R.toRealDat F.lv2 Y.tupT Y.hm Y.hTop hch hS hT hP X0.s false Y.Iz Y.tied.base
      (Y.tup t) (hUsed t) (Y.jA0 t x) t (Y.tupT_tup t) _ (Y.topRead0 t (hUsed t) x)

end GlobalTheory.Mem.R3.DTheta
