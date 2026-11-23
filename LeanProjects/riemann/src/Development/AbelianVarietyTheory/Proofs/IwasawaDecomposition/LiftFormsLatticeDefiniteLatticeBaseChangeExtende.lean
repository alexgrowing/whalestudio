import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExtendedDataLiftFormsLatticeBaseLevelBaseChangeAStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteLiftLatticeBaseChangeExtendedDataStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseLevelLiftMatrixSolvesRelationExtendedDataStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseLevelComplexPointsInjectiveExtendedDataStatement
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBaseEnlargementFixedCoefFieldOfCoeffEnlargemen
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoefAEqOfHeq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Forms
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
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix

namespace GlobalTheory.Mem.R3.LiftLat0

section Key

open Formalism.IndefR.Cx

variable {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K']

theorem map_mulVec_fun (φ : K →+* K') {m n : ℕ} (θ : Matrix (Fin m) (Fin n) K) (x : Fin n → K) :
    (fun k => φ ((θ *ᵥ x) k)) = θ.map φ *ᵥ fun k => φ (x k) := by
  funext k; exact RingHom.map_mulVec φ θ x k

theorem cpt_single (σ : K' →+* ℂ) {n : ℕ} (k : Fin n) : cpt σ (Pi.single k (1 : K')) = Pi.single k 1 := by
  funext i; by_cases h : i = k
  · subst h; simp [cpt]
  · simp [cpt, Pi.single_apply, h]

theorem kOf_apply (σ : K' →+* ℂ) (a : K') : kOf σ (σ a) = a := by
  classical
  have h : ∃ b : K', σ b = σ a := ⟨a, rfl⟩
  unfold kOf
  rw [dif_pos h]
  exact σ.injective h.choose_spec

theorem matLat_relMat_of_heq (φ : K →+* K') (σ : K →+* ℂ) (σ' : K' →+* ℂ)
    {W W' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] {dW dW' dZ dZ' : ℕ}
    (w0 : (Fin dW → ℂ) →ₗ[ℂ] W) (t0 : (Fin dZ → ℂ) →ₗ[ℂ] W) (w0' : (Fin dW' → ℂ) →ₗ[ℂ] W')
    (t0' : (Fin dZ' → ℂ) →ₗ[ℂ] W') (θ : Matrix (Fin dW) (Fin dZ) K) (G : Matrix (Fin dW') (Fin dW) K')
    (N : Matrix (Fin dZ') (Fin dZ) K') (hN : Function.Bijective N.mulVec)
    (hG : ∀ y : Fin dW → K, HEq (w0' (cpt σ' (G *ᵥ fun k => φ (y k)))) (w0 (cpt σ y)))
    (hNc : ∀ x : Fin dZ → K, HEq (t0' (cpt σ' (N *ᵥ fun k => φ (x k)))) (t0 (cpt σ x)))
    (hR : ∀ x : Fin dZ → K, w0 (cpt σ (θ *ᵥ x)) = t0 (cpt σ x)) (hI : Function.Injective w0')
    (L : Submodule (𝓞 K) (Fin dZ → K)) :
    Formalism.DivisionValues.matLat (kMat σ' (relMat w0' t0'))
              (Submodule.span (𝓞 K') ((fun x : Fin dZ → K => N *ᵥ fun k => φ (x k)) '' (L : Set (Fin dZ → K)))) =
      Submodule.span (𝓞 K') ((fun x : Fin dW → K => G *ᵥ fun k => φ (x k)) ''
        (Formalism.DivisionValues.matLat θ L : Set (Fin dW → K))) := by
  classical
  set eN := LinearEquiv.ofBijective (Matrix.mulVecLin N) hN with heN
  have hNe : ∀ v, eN v = N *ᵥ v := fun v => rfl
  have hb : ∀ x : Fin dZ → K, t0' (cpt σ' (N *ᵥ fun k => φ (x k))) =
      w0' (cpt σ' (G *ᵥ (θ.map φ *ᵥ fun k => φ (x k)))) := by
    intro x
    rw [← map_mulVec_fun φ θ x]
    exact eq_of_heq ((hNc x).trans ((heq_of_eq (hR x)).symm.trans (hG (θ *ᵥ x)).symm))

  have hL : ((t0'.comp (cptL σ' dZ')).comp N.mulVecLin : (Fin dZ → K') →ₛₗ[σ'] W') =
      (w0'.comp (cptL σ' dW')).comp (G.mulVecLin.comp (θ.map φ).mulVecLin) := by
    refine (Pi.basisFun K' (Fin dZ)).ext fun i => ?_
    have hs : (Pi.basisFun K' (Fin dZ)) i = fun k => φ ((Pi.single i (1 : K) : Fin dZ → K) k) := by
      rw [Pi.basisFun_apply]; funext k; by_cases h : k = i
      · subst h; simp
      · simp [Pi.single_apply, h]
    rw [hs]
    simpa [cptL, Matrix.mulVecLin_apply] using hb (Pi.single i 1)

  have hθ : ∀ u : Fin dZ' → K', kMat σ' (relMat w0' t0') *ᵥ u = G *ᵥ (θ.map φ *ᵥ eN.symm u) := by
    have hk : ∀ k : Fin dZ', ∀ i, kMat σ' (relMat w0' t0') i k = (G *ᵥ (θ.map φ *ᵥ eN.symm (Pi.single k 1))) i := by
      intro k i
      set v := G *ᵥ (θ.map φ *ᵥ eN.symm (Pi.single k 1)) with hv
      have hw : w0' (cpt σ' v) = t0' (Pi.single k 1) := by
        have h1 := congrArg (fun f => f (eN.symm (Pi.single k 1))) hL
        simp only [LinearMap.comp_apply, cptL, LinearMap.coe_mk, AddHom.coe_mk, Matrix.mulVecLin_apply] at h1
        have h2 : N *ᵥ eN.symm (Pi.single k 1) = Pi.single k 1 := by
          rw [← hNe]; exact eN.apply_symm_apply (Pi.single k 1)
        rw [h2, cpt_single] at h1
        exact h1.symm
      have hex : ∃ y, w0' y = t0' (Pi.single k 1) := ⟨_, hw⟩
      have hsol : solve w0' (t0' (Pi.single k 1)) = cpt σ' v := by
        apply hI
        unfold solve
        rw [dif_pos hex]
        exact hex.choose_spec.trans hw.symm
      show kOf σ' (solve w0' (t0' (Pi.single k 1)) i) = v i
      rw [hsol]
      exact kOf_apply σ' (v i)
    have hlin : (kMat σ' (relMat w0' t0')).mulVecLin =
        G.mulVecLin.comp ((θ.map φ).mulVecLin.comp eN.symm.toLinearMap) := by
      refine (Pi.basisFun K' (Fin dZ')).ext fun k => ?_
      rw [Pi.basisFun_apply]
      funext i
      simp only [Matrix.mulVecLin_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [← hk k i, Matrix.mulVec_single_one]
      rfl
    intro u
    exact congrArg (fun f => f u) hlin

  unfold Formalism.DivisionValues.matLat
  rw [Submodule.map_span, Submodule.map_coe, Set.image_image, Set.image_image]
  congr 1
  refine Set.image_congr fun x _ => ?_
  simp only [LinearMap.restrictScalars_apply, Matrix.mulVecLin_apply]
  rw [hθ, map_mulVec_fun φ θ x]
  congr 2
  rw [← hNe]; exact eN.symm_apply_apply (fun k => φ (x k))

end Key

set_option maxHeartbeats 4000000 in

theorem liftFormsLattice_definiteLattice_baseChange_extended_alt : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x) →
        ∃ G : Matrix (Fin ((s0Of z'.R z'.F).dW j')) (Fin ((s0Of z.R z.F).dW j)) (w'.st Z').toD7.what₂.LL, Function.Bijective G.mulVec ∧
          (s0Of z'.R z'.F).M j' = Submodule.span (𝓞 (w'.st Z').toD7.what₂.LL) ((fun x : Fin ((s0Of z.R z.F).dW j) → (w.st Z).toD7.what₂.LL => Matrix.mulVec G fun k => φ (x k)) '' (((s0Of z.R z.F).M j : Submodule (𝓞 (w.st Z).toD7.what₂.LL) (Fin ((s0Of z.R z.F).dW j) → (w.st Z).toD7.what₂.LL)) : Set (Fin ((s0Of z.R z.F).dW j) → (w.st Z).toD7.what₂.LL))) ∧
          Formalism.DivisionValues.matLat ((s0Of z'.R z'.F).θ j' (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.μ0) (((famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).side3 z'.F.P0 z'.F.ψ0 (zsOf z'.R z'.F)).Tl j' (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.μ0) =
            Submodule.span (𝓞 (w'.st Z').toD7.what₂.LL) ((fun x : Fin ((s0Of z.R z.F).dW j) → (w.st Z).toD7.what₂.LL => Matrix.mulVec G fun k => φ (x k)) '' ((Formalism.DivisionValues.matLat ((s0Of z.R z.F).θ j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0) (((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0 (zsOf z.R z.F)).Tl j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0) : Submodule (𝓞 (w.st Z).toD7.what₂.LL) (Fin ((s0Of z.R z.F).dW j) → (w.st Z).toD7.what₂.LL)) : Set (Fin ((s0Of z.R z.F).dW j) → (w.st Z).toD7.what₂.LL)))) := by
  intro h1 h2 h3 h4 h5 h6 h7
  refine StepW.trans (StepW.and (StepW.and (GlobalTheory.T.extendedData_liftFormsLattice_baseLevel_baseChange_alt h1 h2 h3 h4 h5 h6 h7) (GlobalTheory.T.definiteLiftLattice_baseChange_extendedData h1 h2 h3 h4 h5 h6 h7))
    (StepW.and (GlobalTheory.T.baseLevelLiftMatrix_solves_relation_extendedData_alt h1 h2 h3 h4 h5 h6 h7) (GlobalTheory.T.baseLevelComplexPoints_injective_extendedData_alt h1 h2 h3 h4 h5 h6 h7))) (StepW.of_all ?_)
  intro K B' f' T' w' _ _ H B f T w hE hf hPin hpx Z hX Wt z hG hGA hFi hHL Z' hX' hG' hGA' hV z' hFi' hExt j j' hj φ hφ
  obtain ⟨G, hGb, hM, hGc⟩ := H.1.1 B f T w hE hf hPin hpx Z hX Wt z hG hGA hFi hHL Z' hX' hG' hGA' hV z' hFi' hExt j j' hj φ hφ
  obtain ⟨N, hNb, hTl, hNc⟩ := H.1.2 B f T w hE hf hPin hpx Z hX Wt z hG hGA hFi hHL Z' hX' hG' hGA' hV z' hFi' hExt j j' hj φ hφ
  have hR := H.2.1 B f T w hE hf hPin hpx Z hX Wt z hG hGA hFi hHL Z' hX' hG' hGA' hV z' hFi' hExt j j' hj φ hφ
  have hI := H.2.2 B f T w hE hf hPin hpx Z hX Wt z hG hGA hFi hHL Z' hX' hG' hGA' hV z' hFi' hExt j j' hj φ hφ
  refine ⟨G, hGb, hM, ?_⟩
  rw [hTl]
  exact matLat_relMat_of_heq φ _ _ _ _ _ _ _ G N hNb hGc hNc hR hI _

end GlobalTheory.Mem.R3.LiftLat0
