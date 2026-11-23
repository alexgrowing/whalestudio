import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoreEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroWild
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalAboveL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OverRowsAndMono
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIrreducibleTwist
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaCorrespondenceLargeRankStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceLocalComponentExistsUniqueClass
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RankOneLocalComponentDet
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharLocalComponentExistsUniqueUnitary
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PairReadingOfJoin
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.FixedNeBotOfEquiv
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasThetaAtOfThetaMod
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharacteristicFunctionIntegralApply
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaFunctionsSpannedHeckeTwistedStandardFrameStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JumpsCardOfBuilt
import Formalism.LocalToGlobal.IndefiniteReal.FockTheta.RealPlaceImaginaryGeneratorReEqZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReferenceTupleFormsSmoothAdmissibleUnitaryModuleStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReferenceTupleThetaValuedMapMemThetaDataStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TrilinearThetaFormReferenceTupleInvariantStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReferenceTupleDatumFormReadsThetaLiftInnerProducStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReferenceTupleWeilDatumCharactersStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.SplitRead GlobalTheory.NPin

open GlobalTheory.RefPair

open GlobalTheory.RefTheta GlobalTheory.ThetaTri Formalism.IndefR.Datum Formalism.IndefR.Links in

theorem GlobalTheory.RefTheta.datum_real : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : Formalism.L2.DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : Formalism.IndefR.Links.RealDat3 D A3 Ks) (F : Formalism.IndefR.Links.Face3 D A3) (cG : Formalism.L2.DIV.G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := A3) R.toRealDat F.lv2 X0), GlobalTheory.Mem.R3.Pins R F cG → GlobalTheory.Mem.R3.Holds R F → R.toRealDat.ExAt → ∀ (M : MtFam D), GlobalTheory.HeightCounting.MtAd Y M → ∀ (i : Fin D.R.m), ∃ X : GlobalTheory.NPin.RowMod D (GlobalTheory.RefTheta.repY Y) (i.1 + 1), HasThetaAt D (M D.what₂.mu0 (i.1 + 1) (by omega) (by omega)) X (R.C.mu0 i) R.C.eta := by
  intro hHC hCR D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y hP hH hEx M Ad i
  have hC := (GlobalTheory.CoreOfWeak.core_of_weak R F hP.char hEx).1
  obtain ⟨X, hc⟩ := GlobalTheory.T.referenceTuple_forms_smoothAdmissibleUnitaryModule hHC hCR D G Pl0 I0 T A3 Ks R F cG X0 Y hP hH hEx i
  have hth : ∀ v, IsThetaFunO R.ψ (Vc D i) (Wc D i) (phi0 Y i v) := fun v => hC.thP.pt_theta i _ _
  have h0 : phi0 Y i ∈ Om Ad i hc := GlobalTheory.T.referenceTuple_thetaValued_map_mem_thetaData hHC hCR D G Pl0 I0 T A3 Ks R F cG X0 Y hP hH hEx M Ad i X hc _ hth
  refine ⟨X, Om Ad i hc, inferInstance, inferInstance, om Ad i hc, lamL Ad i hc, ⟨_, h0⟩, ?_, ?_, ?_⟩
  · intro h g φ Fm Fm' y y' hF hy
    exact GlobalTheory.T.trilinearThetaForm_referenceTuple_invariant D G Pl0 I0 T A3 Ks R F cG X0 Y hP hH hEx M Ad i X hc h g φ.1 φ.2 Fm Fm' y y' hF hy
  · intro x y Fm hF
    exact GlobalTheory.T.referenceTuple_datumForm_reads_thetaLift_innerProducts D G Pl0 I0 T A3 Ks R F cG X0 Y hP hH hEx M Ad i X hc x y Fm hF
  intro s μw ηw hμw hηw
  obtain ⟨h1, h2⟩ := GlobalTheory.T.referenceTuple_weilDatum_characters D G Pl0 I0 T A3 Ks R F cG X0 Y hP hH hEx i
  have hv : ∀ v, phi0 Y i v ∈ ⨆ (ι : GlobalTheory.SplitWeil.SB (Matrix (Fin D.R.nV) (Fin D.R.r)
      (s.w.adicCompletion D.host.E)) →ₗ[ℂ] (WO (Vc D i) (Wc D i) → ℂ))
      (_ : GlobalTheory.NPin.IsLinAt (omStd Ad i (t0 Y)) s μw ηw ι ∧ ∀ Φ, IsThetaFunO R.ψ (Vc D i) (Wc D i) (ι Φ)),
      LinearMap.range ι := fun v =>
    GlobalTheory.T.thetaFunctions_spanned_heckeTwisted_standardFrame D R.ψ (Vc D i) (Wc D i) D.R.nV D.R.r (Ad.PV i) (Y.PW i) Y.hF
      (Ad.std i) (Y.stdPsi.2 i) _ _ (R.ωP i (t0 Y)) (hC.thP.ωP i _) _ _ h1 h2 s μw ηw hμw hηw _ (hth v)
  have hlin := mem_iSup_isLinAt_lin' (omStd Ad i (t0 Y)) (IsThetaFunO R.ψ (Vc D i) (Wc D i)) (· ∈ Om Ad i hc)
    (fun β f hf => GlobalTheory.T.referenceTuple_thetaValued_map_mem_thetaData hHC hCR D G Pl0 I0 T A3 Ks R F cG X0 Y hP hH hEx M Ad i X hc _ fun v => by
      simpa [single1] using Formalism.IndefR.Fock.CCR.theta_smul hf (β v))
    s μw ηw _ hv
  exact mem_iSup_isLinAt_omSub _ _ _ _ _ _ _ _ _ s μw ηw h0 hlin

theorem GlobalTheory.RefTheta.main : PrN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, GlobalTheory.LiftRef.AtRows hL fun D cf rep _ _ M => ∀ (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m), ∃ X : RowMod D rep j, HasThetaAt D (M D.what₂.mu0 j h1 h2) X (cf.mu0 ⟨j - 1, by omega⟩) cf.eta := by
  intro hN hL
  unfold GlobalTheory.LiftRef.AtRows OverRows
  refine GlobalTheory.HeightCounting.JumpsAt.evLgG_of_forall fun K B f T _ w _ Z Wt hX z p0 Y hH hEx _ _ _ Rw a M tup Q hMA _ j h1 h2 => ?_
  obtain ⟨i, rfl⟩ : ∃ i : Fin (w.st Z).toD7.R.m, j = (i : ℕ) + 1 := ⟨⟨j - 1, by omega⟩, by simp only; omega⟩
  have hC : z.R.C = TC.cf w.I w.l Z := z.lev.C
  obtain ⟨X, hX⟩ := GlobalTheory.RefTheta.datum_real hN.hc hN.decay _ _ _ _ _ _ _ z.R z.F z.cG p0 Y z.pins hH hEx M hMA i
  refine ⟨X, ?_⟩
  rw [← hC]
  exact hX
