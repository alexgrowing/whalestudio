import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoefAEqOfHeq
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsBIffCoreB
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RationalRowTestKernel
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HoldsUIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBare
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CopyLIntegral
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestAtRealisationOfHilbertModelsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EventuallyStagesParametersParameterSizeConditionsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestHypothesesAtMemberAdelicDataStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TestChoicesExistLargeCoeffFieldAdelicDataStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqualMultiplicitiesRowTestOfSameGroupTransferStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open GlobalTheory.RowClaim

noncomputable section

namespace GlobalTheory.Mem.R3.Rw.RowAt

theorem ev_scale {p : ℝ → ℝ → Prop} (h : ∀ eps : ℝ, 0 < eps → ∃ x₀ : ℝ, p eps x₀) :
    Ev fun K => ∃ x₀ : ℝ, x₀ ≤ K.s.x ∧ p K.s.eps x₀ :=
  ⟨1, one_pos, fun eps _ h0 _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun _ _ _ _ => ⟨0, fun _ _ => ⟨0, fun _ _ =>
    let ⟨x₀, hx⟩ := h eps h0
    ⟨x₀, fun _ _ _ _ hs hx' => ⟨x₀, hx', hs ▸ hx⟩⟩⟩⟩⟩⟩

set_option maxHeartbeats 2000000 in

theorem atDat_rowTest : GlobalTheory.Published.GreenCuspidal → GlobalTheory.Published.CuspRapidDecay → LinK → InjK → ConstK → SumOKK → Formula2K → SumRatK →
    RatioK → GlobalTheory.RowEx.ExField → StepW Pinned fun _ B f T w => ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
      (z : GlobalTheory.Mem.R3.Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GlobalTheory.Mem.R3.GrpAt (w.st Z) w.I → z.R.toRealDat.ExAt →
      GlobalTheory.RealGeo.InGeo z.geo → Formalism.IndefR.Rat.RowTest (z.R.toCx3 z.F) := by
  intro hG hC h1 h2 h3 h4 h5 h6 h7 hEF
  obtain ⟨CF1, H1⟩ := GlobalTheory.T.rowTest_at_realisation_of_hilbertModels hC h1 h2 h3 h4 h5 h6 h7
  obtain ⟨CF2, H2⟩ := GlobalTheory.T.testChoices_exist_largeCoeffField_adelicData hEF
  have hCh := H2 (max CF1 CF2) (le_max_right _ _)
  have e1 := ((evG_of_ev (ev_scale fun eps _ => H1 eps (max CF1 CF2) (le_max_left _ _))).inter GlobalTheory.T.eventually_stages_parameterSizeConditions).inter
    (evG_of_ev GlobalTheory.T.hidaSetting_of_sizeRows)
  have s1 : Step KPx (fun _ _ _ _ => True) _ := Step.of_evLgG (evLgG_of_evLg hCh)
  refine s1.trans (Step.of_evG (e1.imp ?_))
  rintro K - - - - ⟨⟨⟨x₀, hx, hH⟩, hLed⟩, hSet⟩ B f T hO - - hch w - Z hX Wt z g1 - hEx -
  obtain ⟨Z', g1', hη, hA⟩ := LedRec.exists_bare hG (B := B) (C := w.C) Z f (6 * K.s.x ^ (-K.C.P.CF))
  obtain ⟨L, hsc, hsz⟩ := hLed (w.st Z') hO hη hA
  have s : SameGrp Z Z' := LedRec.sameGrp g1 g1'
  refine (GlobalTheory.T.equalMultiplicities_rowTest_of_sameGroupTransfer B w.C Z Z' w.px w.I hX T Wt s z).2 ?_
  have hEx' := DatCopy.copy_exAt Z' s hEx
  generalize DatCopy.copy Z' s z = y at hEx' ⊢
  have hS := hSet B f T w Z' hX Wt y hO g1' hEx' L hsz
  exact hH (w.st Z').toD7 L (by rw [hsc]) (by rw [hsc]; exact hx) _ _ _ _ _ _ y.R y.F hS (hch w Z' hX Wt y L hsc hS)

end GlobalTheory.Mem.R3.Rw.RowAt

end
