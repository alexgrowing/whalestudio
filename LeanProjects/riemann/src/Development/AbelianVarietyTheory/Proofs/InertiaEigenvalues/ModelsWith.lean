import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksW
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LastStepIntertwinerOneTupleAllTuplesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IoPOfIsIoWAt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PItYOfOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpOfOrder
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChainStepsLevelCharacterConditionsHoldStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsThetaLiftMultiplicitySpacesOfPublishedStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtYAndItYOfPair
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteLastStepRealIntertwinerStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InnerStepsOfStepsOK
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMultiplicityLiftLastChainStepStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PostOnGaLMemGoodPart
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLowestKTypeFockMapThetaVectorsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsThetaLiftLinearMapCuspFormMultiplicityStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PostOnSumMemRange
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ConjExt

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

set_option maxHeartbeats 4000000 in
theorem models_with (h : R.IsModels) (ioY ioX Th thF thG) :
    ({ R with ioY := ioY, ioX := ioX, Th := Th, thF := thF, thG := thG } : RealDat D A Ks).IsModels :=
  ⟨h.inf, h.vpos, h.cX, h.cV, h.prX, h.HX, h.HV, h.HE, h.HW, h.gE, h.gW, h.jX, h.jV, h.νY, h.νY', h.ν0, h.νX, h.νV, h.νW, h.BV,
    h.order⟩

set_option maxHeartbeats 4000000 in
theorem fam_with (h : R.IsFam) (ioY ioX Th thF thG) :
    ({ R with ioY := ioY, ioX := ioX, Th := Th, thF := thF, thG := thG } : RealDat D A Ks).IsFam :=
  ⟨h.tie, h.Sb, h.roots, h.pl_onto, h.degR, h.degL, h.muVal, h.etaVal⟩

theorem chain_with (hωY : R.chain_ωY) (hωX : R.chain_ωX) (hvY : R.chain_vY) (hvX : R.chain_vX) (a : R.chain_ptY)
    (b : R.chain_ptX) (c : R.chain_ItY) (d : R.chain_ItX) (ioY ioX Th) (e : ({ R with ioY := ioY } : RealDat D A Ks).chain_ioY)
    (f : ({ R with ioX := ioX } : RealDat D A Ks).chain_ioX)
    (g : ({ R with ioY := ioY, ioX := ioX, Th := Th } : RealDat D A Ks).chain_Th) :
    ({ R with ioY := ioY, ioX := ioX, Th := Th } : RealDat D A Ks).IsChain :=
  ⟨hωY, hωX, hvY, hvX, a, b, c, d, e, f, g⟩

theorem exists_th (hL : R.toLevCh.Is A.μ0) (hr : R.grp_record) (hF : R.IsFam) (hM : R.IsModels) (ioY ioX) :
    ∃ Th, ({ R with ioY := ioY, ioX := ioX, Th := Th } : RealDat D A Ks).chain_Th :=
  GlobalTheory.ProjectedLift.exists_chain_Th D G Pl0 T A Ks { R with ioY := ioY, ioX := ioX } hL
    (fam_with hF ioY ioX R.Th R.thF R.thG) (models_with hM ioY ioX R.Th R.thF R.thG) hr

set_option maxHeartbeats 800000 in

theorem exists_chain (h₁ : GlobalTheory.Published.DiscreteSeriesCover) (h₂ : GlobalTheory.Published.HarishChandraModules) (h₃ : GlobalTheory.Published.CuspRapidDecay)
    (h₄ : GlobalTheory.Published.CasselmanWallach) (hP : ∀ k, GlobalTheory.Chain.ChainPar D k) (hL : R.toLevCh.Is A.μ0) (hr : R.grp_record)
    (hF : R.IsFam) (hM : R.IsModels) (hωY : R.chain_ωY) (hωX : R.chain_ωX) (hvY : R.chain_vY) (hvX : R.chain_vX) (t₀ : T)
    (hY : ∀ k, k + 1 < D.R.m → IsItW R.θ (R.MY k) (R.MY (k + 1)) (R.ωY t₀ k) (R.ptY t₀ k) (R.ItY k))
    (hX : IsItW R.θ (R.MY (D.R.m - 1)) R.MX (R.ωX t₀) (R.ptX t₀) R.ItX) :
    ∃ ioY ioX Th, ({ R with ioY := ioY, ioX := ioX, Th := Th } : RealDat D A Ks).IsChain := by
  have hS := GlobalTheory.Chain.StepVac.stepsOK D G Pl0 T A Ks R hL hM.inf hωY hωX hvY hvX
  have hW := GlobalTheory.T.chainSteps_levelCharacter_conditions_hold D G Pl0 T A Ks R hL hM.inf hωY hωX hvY hvX
  have hIY : R.chain_ItY := fun t k hk =>
    GlobalTheory.Chain.ItAllTuples.pItY_of_one h₁ h₂ D G Pl0 T A Ks R hP hL hM hωY hωX hvY hvX k hk t₀ _ (hY k hk) t
  have hIX : R.chain_ItX := GlobalTheory.T.lastStep_intertwiner_one_tuple_all_tuples D G Pl0 T A Ks R hL hM hωX hvX t₀ _ hX
  have hpY : R.chain_ptY := fun t k hk P =>
    GlobalTheory.Chain.InnerSteps.theta_pureTensorO (hωY t k hk).std hM.inf _ _ _ _ (hS.1 t ⟨k, by omega⟩ hk).2.theta P
  have hpX : R.chain_ptX := (GlobalTheory.T.definite_lastStep_real_intertwiner D G Pl0 T A Ks R hL hF hM hωX hvX).1
  exact (GlobalTheory.Chain.InnerLift.exists_ioY_of_pair R (GlobalTheory.T.exists_thetaLift_multiplicitySpaces_of_hypotheses h₁ h₂ h₃ h₄ D) hP hS.1 hW.1 hM hIY).elim fun ioY hioY =>
    (GlobalTheory.T.exists_multiplicityLift_lastChainStep D G Pl0 T A Ks R hL hF hM hωX hvX hpX hIX).elim fun ioX hioX =>
    (exists_th hL hr hF hM ioY ioX).elim fun Th hTh =>
    ⟨ioY, ioX, Th, chain_with hωY hωX hvY hvX hpY hpX hIY hIX ioY ioX Th hioY hioX hTh⟩

set_option maxHeartbeats 4000000 in

theorem exists_thP (h₃ : GlobalTheory.Published.CuspRapidDecay) (hL : R.toLevCh.Is A.μ0) (hF : R.IsFam) (hM : R.IsModels) (hω : R.thP_ωP)
    (hv : R.thP_vP) (t₀ : T)
    (hI : ∀ i, IsIoW R.θ (R.MW i (sg0 D A)) (R.cV i) (R.ωP i t₀) (R.ptP i t₀) (RealDat.Delta i) (R.ioP i)) :
    ∃ thF thG, ({ R with thF := thF, thG := thG } : RealDat D A Ks).IsThP := by
  have hp : R.thP_pt_theta := (GlobalTheory.T.exists_lowestKType_fockMap_thetaVectors D G Pl0 T A Ks R hL hF hM hω hv).1
  have hio : R.thP_ioP := fun i => GlobalTheory.IoAllTuples.ioP_of_isIoW_at D G Pl0 T A Ks R hL hF hM hω hv i t₀ _ (hI i)
  obtain ⟨thF, h1, h2⟩ := GlobalTheory.T.exists_thetaLift_linearMap_cuspFormMultiplicity h₃ D G Pl0 T A Ks R hL hF hM hω hv hp hio
  obtain ⟨thG, h3⟩ := GlobalTheory.GoodProjLift.exists_thG D G Pl0 T A Ks { R with thF := thF } hL
    (fam_with hF R.ioY R.ioX R.Th thF R.thG) (models_with hM R.ioY R.ioX R.Th thF R.thG) h1
  exact ⟨thF, thG, hω, hv, hp, hio, h1, h2, h3⟩

end GlobalTheory.ConjExt

end
