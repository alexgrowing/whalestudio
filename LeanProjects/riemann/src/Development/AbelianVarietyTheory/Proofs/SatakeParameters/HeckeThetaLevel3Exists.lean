import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodGeneric
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HcFiniteAndSchurMult
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GoodProjectorUnitaryFormsModelLaws
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EigSumMulProjEq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConjugateSpaceJointEigenspacesPairCommISupStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalOperatorsFormsOnRankSpaceNormalStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RealizationFamilyNormalOperatorsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaIntertwinesMatchedOperatorsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharacterisationPlacesPartsOfWeakStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EveryLiftOperatorIsLabelOperatorWithPartnerStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSeparatingInertEigenvaluePassageStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CarriedPartEigensystemPassageOfTypeStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EigenPartLeTypePartOfPassageStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ZeroEigensystemNotPassageOfFiniteTypeStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Hk3

theorem tw_cut_eig (s : Bool) {E I C : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (h : I → Module.End ℂ E) (e : Module.End ℂ E) (Ec : C → Submodule ℂ E) (lab : C → I → ℂ)
    (he : e * e = e) (hs : (⨆ c, Ec c) = LinearMap.range e) (hl : ∀ c, ∀ w ∈ Ec c, ∀ i, h i w = lab c i • w) :
    Formalism.L2.Col.PairComm (fun i => (Tw.map s (h i * e) : Module.End ℂ (Tw s E))) ∧
      ∀ Q : (I → ℂ) → Prop, ¬ Q 0 →
        Formalism.L2.Col.eigSum (fun i => (Tw.map s (h i * e) : Module.End ℂ (Tw s E))) Q =
          Tw.sub s (⨆ (c : C) (_ : Q (fun i => cj s (lab c i))), Ec c) := by
  obtain ⟨hc, hq⟩ := GlobalTheory.Hk3.eigSum_mul_proj_eq h e Ec lab he hs hl
  obtain ⟨a, b, -⟩ := GlobalTheory.T.conjugateSpace_jointEigenspaces_pairComm_iSup s (fun i => h i * e)
  refine ⟨a hc, fun Q hQ => ?_⟩
  have h0 : (fun i => cj s ((0 : I → ℂ) i)) = 0 := by funext i; simp
  rw [b Q, hq _ (by rw [h0]; exact hQ)]

theorem cxSys_cj_iff {K I : Type} [Field K] {σ τ : K →+* ℂ} {s : Bool} (h : ∀ a, σ a = cj s (τ a)) (H : (I → K) → Prop) (y : I → ℂ) :
    cxSys σ H (fun i => cj s (y i)) ↔ cxSys τ H y := by
  constructor
  · rintro ⟨x, hx, e⟩
    refine ⟨x, hx, funext fun i => ?_⟩
    have := congrFun e i
    simp only [h] at this
    simpa [cj_cj] using congrArg (cj s) this
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, funext fun i => (h _).symm⟩

set_option maxHeartbeats 2000000 in
theorem heckeTheta_level3_exists_alt : HoweUnram → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), GlobalTheory.Chain.LiftInteg D → R.WeakCharacterisation F → R.toRealDat.ExAt → InertJunk A3 → ∀ s, A3.fam3.Ok3 s → GoodGeneric A3.A.X F.P0 F.ψ0⁻¹ → R.toRealDat.LUnif → R.PGUnit F → R.PGEquiv F → R.PLevW F → R.PThmA → (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) → R.PThmB → (R.toCx3 F).PartsW false → A3.fam3.TypesSep3 → ((∃ tr, R.TrISem F tr ∧ TrISepWith A3 tr) → R.TrISem F A3.trI ∧ A3.fam3.TrISep) → ∃ hW, HeckeIntertwiningLifts A3 (R.toCx3 F) hW := by
  intro hHowe hHC hCusp D G _ _ Pl0 I0 T A3 Ks _ _ _ R F hLI hC hEx hJ s hOk hGG hLU hGU hGE hLW hA hPos hB hParts hTS hPin
  have hirr : ∀ χ ∈ A3.A.X, IsAbsIrrChar χ := hOk.ok2.irr
  obtain ⟨hCoreE, hSF, -, -, -, hWc, -⟩ := GlobalTheory.T.heckeCharacterisation_places_of_weakCharacterisation R F hC
  have hCore := hCoreE hEx
  have hSch : SchurAll R.toRealDat :=
    ⟨fun _ _ _ => (GlobalTheory.MultFinite.hcFinite_and_schurMult hHC hCusp D _ _ _ _ _ _ _ _).2,
      (GlobalTheory.MultFinite.hcFinite_and_schurMult hHC hCusp D _ _ _ _ _ _ _ _).2,
      fun _ => (GlobalTheory.MultFinite.hcFinite_and_schurMult hHC hCusp D _ _ _ _ _ _ _ _).2⟩
  have hTr := (hPin (GlobalTheory.T.exists_separating_inert_eigenvalue_passage hHowe R F hLI hC hEx hSch hJ hirr hB hPos)).1
  have hOps := fun i => GlobalTheory.T.sphericalOperators_forms_on_rank_space_normal R.toRealDat F.lv2 hCore hSch hirr R.SF hSF i
  choose h hIsW hNorm hGc hSup hInv hEig hChar using hOps
  have hDict := GlobalTheory.T.every_liftOperator_is_labelOperator_with_partner hHowe R F hLI hC hEx hSch hJ
  choose pl cV cW hD using hDict
  have hLaws := GlobalTheory.Hk3.eH_laws R.toRealDat F.lv2 hCore hirr
  have hcut := fun j => tw_cut_eig (twAt D.what₂.embLL A3.A.v0) (fun i => h j (pl j A3.A.μ0 i) (cW j A3.A.μ0 i)) (eH R.toRealDat j)
    (Wcc R.toRealDat R.SF j) (fun c => labW j (pl j A3.A.μ0) (cW j A3.A.μ0) c) (hLaws j).1 (hSup j)
    (fun c w hw i => hEig j c _ ((hD j A3.A.μ0).good i) _ w hw)
  refine ⟨fun j t i => Tw.map (E := (R.HW j (sg0 D A3.A)).H) (F := (R.HW j (sg0 D A3.A)).H) (twAt D.what₂.embLL A3.A.v0) (h j (pl j t i) (cW j t i) * eH R.toRealDat j), ?_, ?_, ?_⟩
  · intro j t i u
    obtain ⟨hV, hVo, -⟩ := (GlobalTheory.T.realization_family_normal_operators R.toRealDat F.lv2 hCore.lev hCore.fam hCore.models).2 j t
    have hK := RealDat3.kFormL_of (R := R) (F := F) hCore.models
    have hop : (R.toCx3 F).opLC j t (Sum.inl i) = Tw.map (E := (R.HV j t).H) (F := (R.HV j t).H) (twAt D.what₂.embLL A3.A.v0) (hV (pl j t i) (cV j t i)) := by
      refine LinearMap.ext_on_range (hK j t).2 fun k => ?_
      rw [← CxData.jL_opL _ hK]
      show Tw.mk (twAt D.what₂.embLL A3.A.v0) (R.jV j t ((A3.liftI j t).opAll i _)) = Tw.mk (twAt D.what₂.embLL A3.A.v0) (hV _ _ (R.jV j t _))
      exact congrArg (Tw.mk (twAt D.what₂.embLL A3.A.v0)) ((hD j t).op hV hVo i _)
    have hs := (GlobalTheory.T.theta_intertwines_matched_operators R.toRealDat F.lv2 hCore hSch hirr R.SF hSF j t (pl j t i) ((hD j t).good i) _ _ ((hD j t).mat i) hV hVo).1 (h j) (hIsW j)
    rw [hop]
    show R.phs j • Tw.mk (twAt D.what₂.embLL A3.A.v0) (R.thG j t (hV _ _ (Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HV j t).H) u))) =
      Tw.map (E := (R.HW j (sg0 D A3.A)).H) (F := (R.HW j (sg0 D A3.A)).H) (twAt D.what₂.embLL A3.A.v0) (h j (pl j t i) (cW j t i) * eH R.toRealDat j)
        (R.phs j • Tw.mk (twAt D.what₂.embLL A3.A.v0) (R.thG j t (Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HV j t).H) u)))
    rw [map_smul]
    congr 1
    show Tw.mk (twAt D.what₂.embLL A3.A.v0) (R.thG j t (hV _ _ (Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HV j t).H) u))) = Tw.mk (twAt D.what₂.embLL A3.A.v0) (h j (pl j t i) (cW j t i) (eH R.toRealDat j (R.thG j t (Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HV j t).H) u))))
    rw [(hLaws j).2.2.2 t, hs]
  · intro j
    exact (hcut j).1
  · intro j p
    have hv := fun a => R.toRealDat.emb0 a
    have hQ0 : ¬ cxSys A3.fam3.base3.v0.embedding ((A3.liftI j A3.A.fam.μ0).HasRes3 (A3.fam3.tr3 j p.1)) 0 := by
      intro h0
      have h1 : (0 : (A3.liftI j A3.A.fam.μ0).OpIx → ℂ) = fun i => cj (twAt D.what₂.embLL A3.A.v0) ((0 : (A3.liftI j A3.A.fam.μ0).OpIx → ℂ) i) := by
        funext i; simp
      rw [h1] at h0
      exact GlobalTheory.T.zero_eigensystem_not_passage_of_finiteType R F hC j p ((cxSys_cj_iff hv _ _).1 h0)
    have key := (hcut j).2 _ hQ0
    show Tw.sub _ (R.Wp3 j p) = _
    refine Eq.trans ?_ key.symm
    congr 1
    apply le_antisymm
    · refine iSup₂_le fun c hc => ?_
      by_cases hne : R.Wc' j c = ⊥
      · rw [hne]; exact bot_le
      · exact le_iSup₂_of_le c ((cxSys_cj_iff hv _ _).2
          (GlobalTheory.T.carriedPart_eigensystem_passage_of_type hHowe R F hLI hC hEx hSch hJ s hOk hGG hLU hGU hGE hLW hA hPos hB hTr j _ _ _ (hD j A3.A.μ0) p c hc hne)) (hWc j c).le
    · refine iSup₂_le fun c hc => ?_
      rw [← hWc j c]
      exact GlobalTheory.T.eigenPart_le_typePart_of_passage hHowe R F hLI hC hEx hSch hJ s hOk hGG hLU hGU hGE hLW hA hPos hB hTr hParts hTS j _ _ _ (hD j A3.A.μ0) p c
        ((cxSys_cj_iff hv _ _).1 hc)

end GlobalTheory.Hk3

end
