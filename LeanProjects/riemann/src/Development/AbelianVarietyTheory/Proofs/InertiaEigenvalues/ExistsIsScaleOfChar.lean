import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsScalar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarmonicPolynomialEqZeroOfFunctionStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockHarmonicValueSpaceMapEqDualWeylModuleFunctioStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RealisationDefiniteRealPointFockVectorActionStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodBaseDataWeightEqLiftCoeffModuleWeightStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffPolynomialEqZeroOfVanishingOnGLFamilyStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurEquivariantMapsProportionalStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPolynomialModelCoefficientSpaceRealPoints
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockPolynomialVectorsInjectiveNonzeroVacuum
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryEqRealMulFiniteSplit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtensionOfLowSmoothLines
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaVectorNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaVectorFockVacuum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpOfOrder

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum
  IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries MvPolynomial Matrix
open Formalism.IndefR.Links
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.SeriesTie

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace Scale

variable {D : D7} {n : ℕ}

theorem coefFn_translate (lam : D.what₂.Tau → DomWeight n) (u : GLR D n) (F : Formalism.L2.DIV.Pol ℂ D.what₂.Tau n) (x : GLR D n) :
    coefFn (RingHom.id ℂ) lam (actP lam (invTrK u) F) x = coefFn (RingHom.id ℂ) lam F (u⁻¹ * x) := by
  have e1 : actP lam (invTrK u) F = detTwK lam (invTrK u) • trAct (invTrK u) F := rfl
  have e2 : (eval₂Hom (RingHom.id ℂ) (fun v : D.what₂.Tau × Fin n × Fin n => (x v.1).val v.2.1 v.2.2)).comp
        (trAct (invTrK u) : Formalism.L2.DIV.Pol ℂ D.what₂.Tau n →+* Formalism.L2.DIV.Pol ℂ D.what₂.Tau n) =
      eval₂Hom (RingHom.id ℂ) (fun v => ((u⁻¹ * x) v.1).val v.2.1 v.2.2) := by
    refine MvPolynomial.ringHom_ext (fun a => by simp [trAct, Formalism.GradedWeylDivisibility.blockAct]) fun v => ?_
    simp only [RingHom.comp_apply, RingHom.coe_coe, trAct, Formalism.GradedWeylDivisibility.blockAct, aeval_X, map_sum, map_mul, eval₂Hom_C,
      eval₂Hom_X', Pi.mul_apply, Pi.inv_apply, Units.val_mul, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun b _ => rfl
  have e3 : (RingHom.id ℂ) (detTwK lam (invTrK u)) =
      ((detFam (fun τ => (lam τ).detShift) u⁻¹ : ℂˣ) : ℂ) := by
    simp only [detTwK, detPow, detFam, map_prod, MonoidHom.coe_mk, OneHom.coe_mk, Units.coe_prod, Units.val_zpow_eq_zpow_val,
      map_zpow₀, GeneralLinearGroup.val_det_apply]
    refine Finset.prod_congr rfl fun τ _ => ?_
    congr 1
    change (((u τ)⁻¹).valᵀ).det = _
    rw [det_transpose]
    rfl
  rw [coefFn, coefFn, e1, smul_eq_C_mul, map_mul, eval₂Hom_C, e3, ← e2, map_mul, Units.val_mul]
  simp only [RingHom.comp_apply, RingHom.coe_coe]
  ring

theorem coefFn_map {K : Type} [Field K] (σ : K →+* ℂ) (lam : D.what₂.Tau → DomWeight n) (F : Formalism.L2.DIV.Pol K D.what₂.Tau n) :
    coefFn (RingHom.id ℂ) lam (MvPolynomial.map σ F) = coefFn σ lam F := by
  funext x
  rw [coefFn, coefFn, eval₂Hom_map_hom, RingHom.id_comp]

def coefLin (lam : D.what₂.Tau → DomWeight n) : VV ℂ lam →ₗ[ℂ] (GLR D n → ℂ) where
  toFun F := coefFn (RingHom.id ℂ) lam (F : Formalism.L2.DIV.Pol ℂ D.what₂.Tau n)
  map_add' F F' := by
    funext x
    simp only [coefFn, Submodule.coe_add, map_add, Pi.add_apply, mul_add]
  map_smul' a F := by
    funext x
    simp only [coefFn, Submodule.coe_smul, smul_eq_C_mul, map_mul, eval₂Hom_C, Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    ring

theorem coefLin_injective (lam : D.what₂.Tau → DomWeight n) : Function.Injective (coefLin lam) :=
  (injective_iff_map_eq_zero _).2 fun F hF => Subtype.ext (GlobalTheory.T.coeffPolynomial_eq_zero_of_vanishing_on_GLFamily D n lam F (congrFun hF))

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {j : Fin D.R.m}
  {B : Base (Vc D j) (Wc D j)}

theorem io_act (hlev : R.toLevCh.Is A.μ0) (hth : R.IsThP) (hB : B.Good) (hψ : B.F.ψ = R.ψ) (hθ : B.F.θ = R.θ)
    (hsT : B.F.sT = cart (R.MW j (sg0 D A))) (hBS : ∀ τ, (B.F.BS τ).val = R.BV j τ) (hBT : B.F.BT = onb (R.MW j (sg0 D A)))
    (hmu : B.mu0 = R.mu0 ((j : ℕ) + 1)) (heta : B.eta = R.eta) (x : LowT (R.MW j (sg0 D A))) :
    ∀ u ∈ GinfC (Vc D j), ∀ w, R.ioP j x ((R.cV j).ρ u w) = B.act u (R.ioP j x w) := by
  have hinf : IsInfFam R.θ := hθ ▸ hB.frame.vac.2.inf
  have hf : IsThetaFunO R.ψ (Vc D j) (Wc D j) (R.vP j A.μ0) := by
    have := hth.pt_theta j A.μ0 1
    unfold RealDat.ptP pureTensorO at this
    rwa [GlobalTheory.AdTh.VecFock.pureTensorL_one] at this
  have hon : ∀ τ, IsONBasis (gramAt D (Vc D j) τ) 1 (R.BV j τ) (Vc D j).rank := fun τ => hBS τ ▸ hB.frame.onbS τ
  have hinj : Function.Injective (R.ptP j A.μ0) :=
    GlobalTheory.FockIndep.pureTensorO_injective D R.ψ R.θ _ _ _ (R.MW j (sg0 D A)) (R.BV j) (R.vP j A.μ0) (hth.ωP j A.μ0).std hinf
      (fun τ => GlobalTheory.GalLift.Vec.isCartanInv_one (hon τ)) hon hf
      (GlobalTheory.AdTh.VecNe.thPVec_ne_zero (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hlev.βV j))
        (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hlev.βW j)) hB.frame.rank_le (hth.vP j A.μ0))
      (GlobalTheory.DatumFock.isFockVacAt_thPVec _ _ _ _ (fun _ => 1) _ _ _ _ _ _ _ _ _ _ (hth.vP j A.μ0) hf)
  have hexp : ∀ τ, HasInfExp D (R.toLevCh.mu A.μ0 ((j : ℕ) + 1)) τ
      ((B.w.c τ : ℚ) - ((B.w.p τ : ℚ) - B.w.q τ) / 2 + 1 / 2) := fun τ => by
    obtain ⟨k, hk, ho⟩ := hlev.xi_fin A.μ0
    have h1 := hB.inf τ
    rw [hmu] at h1
    have h2 := GlobalTheory.Chain.StepVac.hasInfExp_mul h1 (GlobalTheory.Chain.StepVac.hasInfExp_of_order hinf (hlev.xi A.μ0) hk ho τ)
    rwa [add_zero] at h2
  intro u hu w
  exact hinj (((hth.ioP j A.μ0).1 u hu x w).symm.trans
    (GlobalTheory.T.realisation_definite_realPoint_fockVector_action D G Pl0 T0 A Ks R j A.μ0 B hth hB hψ hθ hsT hBS hBT heta hexp u hu _))

theorem exists_scale (hlev : R.toLevCh.Is A.μ0) (hth : R.IsThP) (hc : (R.cV j).Is) (hB : B.Good) (hψ : B.F.ψ = R.ψ)
    (hθ : B.F.θ = R.θ) (hsT : B.F.sT = cart (R.MW j (sg0 D A))) (hBS : ∀ τ, (B.F.BS τ).val = R.BV j τ)
    (hBT : B.F.BT = onb (R.MW j (sg0 D A))) (hmu : B.mu0 = R.mu0 ((j : ℕ) + 1)) (heta : B.eta = R.eta)
    (hap : ∀ τ, B.w.ap τ = aPl D j ((Wc D j).sig (tauE D τ)).1 τ)
    (ham : ∀ τ, B.w.am τ = aMi D j ((Wc D j).sig (tauE D τ)).1 ((Wc D j).sig (tauE D τ)).2 τ)
    (c0 : VV D.what₂.LL (FWT.lamV D j) →ₛₗ[D.what₂.embLL] (R.cV j).W)
    (ht : Bridge.CoefMapTie (Vc D j) (R.cV j).coef c0 (rhoVr (labLL D) (FWT.lamV D j)))
    (x : LowT (R.MW j (sg0 D A))) (w₀ : (R.cV j).W) (hw : R.ioP j x w₀ = RealDat.Delta j) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ F : VV D.what₂.LL (FWT.lamV D j), harmFn (Wc D j).rank B.w B.F.BS (R.ioP j x (c0 F)) =
      c • coefFn D.what₂.embLL (FWT.lamV D j) (F : Formalism.L2.DIV.Pol D.what₂.LL D.what₂.Tau (Vc D j).rank) := by
  have hinf : IsInfFam R.θ := hθ ▸ hB.frame.vac.2.inf
  have hT := io_act hlev hth hB hψ hθ hsT hBS hBT hmu heta x
  have hlam : B.w.lam = FWT.lamV D j := GlobalTheory.T.good_baseData_weight_eq_lift_coeff_module_weight D T0 R.toLevCh A.μ0 j B hlev hB hmu hap ham
  have hpq : ∀ τ, B.w.p τ + B.w.q τ ≤ (Wc D j).rank := fun τ => by
    obtain ⟨e, -⟩ := hB.sigOK (tauE D τ)
    rw [← hB.sig τ] at e
    have := Fintype.card_congr e
    simp only [Fintype.card_fin, Fintype.card_sum] at this
    omega
  have hΔ : B.w.delta (Wc D j).rank = RealDat.Delta j := by
    unfold Weight.delta RealDat.Delta
    rw [show B.w.p = _ from funext fun τ => congrArg Prod.fst (hB.sig τ),
      show B.w.q = _ from funext fun τ => congrArg Prod.snd (hB.sig τ), show B.w.ap = _ from funext hap,
      show B.w.am = _ from funext ham]
  have hirr : ∀ U : Submodule ℂ (R.cV j).W, (∀ h : GinfC (Vc D j), U.map ((R.cV j).ρ h) ≤ U) → U = ⊥ ∨ U = ⊤ :=
    fun U hU => hc.2.2.2.2 U fun h => by
      obtain ⟨a, ha, k, hk, rfl⟩ := (GlobalTheory.UnitarySplit.real_finite_split D _).1 h
      rw [map_mul, hc.1 k hk, mul_one]
      exact hU ⟨a, ha⟩
  have hΔ0 := GlobalTheory.AdTh.IoExtPf.Delta_ne (D := D) j
  have hharm : ∀ w, R.ioP j x w ∈ harm (Wc D j).rank B.w B.F.BS := by
    rcases hirr ((harm (Wc D j).rank B.w B.F.BS).comap (R.ioP j x)) (fun h => by
      rintro _ ⟨w, hw', rfl⟩
      rw [Submodule.mem_comap, hT h h.2]
      exact fockGL_mem_harm _ _ _ hw') with h | h
    · have h0 : w₀ ∈ (harm (Wc D j).rank B.w B.F.BS).comap (R.ioP j x) := by
        rw [Submodule.mem_comap, hw, ← hΔ]
        exact delta_mem_harm _ _
      rw [h, Submodule.mem_bot] at h0
      rw [h0, map_zero] at hw
      exact absurd hw.symm hΔ0
    · exact fun w => (h ▸ Submodule.mem_top : w ∈ (harm (Wc D j).rank B.w B.F.BS).comap (R.ioP j x))
  obtain ⟨e, he0, he⟩ := GlobalTheory.CoefReal.exists_real_model (Vc D j) R.θ (R.cV j) (FWT.lamV D j) c0 hinf hc ht
  haveI := hc.2.2.2.1
  obtain ⟨c, hcc⟩ := GlobalTheory.T.schur_equivariant_maps_proportional (GinfC (Vc D j)) (R.cV j).W (GLR D (Vc D j).rank → ℂ) (fun h => (R.cV j).ρ h)
    (fun h => LinearMap.funLeft ℂ ℂ fun y => (realGL R.θ (Vc D j) h)⁻¹ * y)
    (harmFn (Wc D j).rank B.w B.F.BS ∘ₗ R.ioP j x) (coefLin (FWT.lamV D j) ∘ₗ e.symm.toLinearMap) hirr
    ((coefLin_injective _).comp e.symm.injective)
    (by
      rintro _ ⟨w, rfl⟩
      have h1 : harmFn (Wc D j).rank B.w B.F.BS (R.ioP j x w) ∈
          (harm (Wc D j).rank B.w B.F.BS).map (harmFn (Wc D j).rank B.w B.F.BS) := Submodule.mem_map_of_mem (hharm w)
      rw [GlobalTheory.T.fockHarmonicValueSpace_map_eq_dualWeylModuleFunctions D _ _ B.w B.F.BS hB.wt hpq, hlam] at h1
      refine Submodule.span_le.2 ?_ h1
      rintro _ ⟨F, rfl⟩
      exact ⟨e F, congrArg (coefLin _) (e.symm_apply_apply F)⟩)
    (fun h w => funext fun y => by
      change harmFn _ B.w B.F.BS (R.ioP j x ((R.cV j).ρ h w)) y = harmFn _ B.w B.F.BS (R.ioP j x w) _
      rw [hT h h.2, ← hθ]
      exact harmFn_fockGL _ _ _ _ _)
    (fun h w => funext fun y => by
      obtain ⟨v, rfl⟩ := e.surjective w
      change coefLin _ (e.symm ((R.cV j).ρ h (e v))) y = coefLin _ (e.symm (e v)) _
      rw [he h h.2, e.symm_apply_apply, e.symm_apply_apply]
      exact coefFn_translate _ _ _ _)
  refine ⟨c, fun h0 => hΔ0 ?_, fun F => ?_⟩
  · have h1 := LinearMap.congr_fun hcc w₀
    rw [h0, zero_smul, LinearMap.comp_apply, hw] at h1
    exact GlobalTheory.T.harmonic_polynomial_eq_zero_of_function D _ _ B.w B.F.BS hB.wt hpq _ (hw ▸ hharm w₀) h1
  · refine (LinearMap.congr_fun hcc (c0 F)).trans ?_
    change c • coefLin _ (e.symm (c0 F)) = _
    rw [show e.symm (c0 F) = _ from e.symm_apply_eq.2 (he0 F).symm, ← coefFn_map]
    rfl

end Scale

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem exists_isScale (Rl : RealDat3 D A3 Ks) (cG : G0 Rl.Pg D.R.r ≃* G0g D.nd)
    (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) {ρ : Setup D.ntw} (hρ : ρ.Good) (hpin : RealPin Rl cG ρ)
    (hlev : Rl.toLevCh.Is A3.A.μ0) (hfam : Rl.toRealDat.fam_tie) (hcV : Rl.toRealDat.models_cV) (hth : Rl.toRealDat.IsThP)
    (hio : FWT.IoExt Rl.toRealDat) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)
    (hv : FWT.IsChosenExtremalVector Rl.toRealDat j (sg0 D A3.A) (v₀ j _)) : ∃ c : ℂ, c ≠ 0 ∧ IsScale Rl v₀ (ρ.B i j b) c := by
  obtain ⟨gramR, c0R, c0L, hft⟩ := hfam
  obtain ⟨u, w₀, hu, -, hw⟩ := FWT.IsChosenExtremalVector.io _ hv hio
  obtain ⟨c, hc0, hc⟩ := Scale.exists_scale hlev hth (hcV j) (hρ.base i j b) (hpin.psi i j b) (hpin.inf i j b)
    (hpin.cartT i j b) (hpin.onbS i j b) (hpin.onbT i j b) (hpin.mu0 i j b) (hpin.eta i j b) (hpin.ap i j b) (hpin.am i j b)
    (c0L j) (hft.mapL j) _ w₀ hw
  exact ⟨c, hc0, gramR, c0R, c0L, hft, u, hu, hc⟩

theorem exists_isScale_of_char (Rl : RealDat3 D A3 Ks) (cG : G0 Rl.Pg D.R.r ≃* G0g D.nd)
    (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) {ρ : Setup D.ntw} (hρ : ρ.Good) (hpin : RealPin Rl cG ρ)
    {F : Face3 D A3} (hC : Rl.Char3 F) (hio : FWT.IoExt Rl.toRealDat) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)
    (hv : FWT.IsChosenExtremalVector Rl.toRealDat j (sg0 D A3.A) (v₀ j _)) : ∃ c : ℂ, c ≠ 0 ∧ IsScale Rl v₀ (ρ.B i j b) c :=
  exists_isScale Rl cG v₀ hρ hpin hC.lev hC.fam.tie hC.models.cV hC.thP hio i j b hv

end GlobalTheory.SeriesTie

end
