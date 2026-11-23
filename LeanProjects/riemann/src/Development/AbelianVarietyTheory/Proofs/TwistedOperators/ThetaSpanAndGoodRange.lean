import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaTranslateRangeGap
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PureTensorOSmul
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilFiniteVectorFixedPrincipalLevelCoeffSpaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLeviFlagOfMemParabolic
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualCoordLatticeOfSelfDualFrame
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsCtxBase
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.WeakWeilRepCarriesDerivativesVacuaFockVectors
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaKernelOrthonormalFrameInDomainPeriodLinear
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RationalUnitaryGroupStructure
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FockPolynomialVectorLaws
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaFormIntegrality
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemSpanThetaSeriesOfBoundedHolomorphicStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsContinuousRealScalarCharacterWeakWeilStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPointsUnitaryCharacterEqDetPowerStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactTorusActsFockVectorRowHighestStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HolomorphicUpToFactorOfLoweringKilledTorusWeightStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.StableFockSpanContainsRowHighestPolynomialsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftFiniteVectorEqTranslateLevelDatumStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFrameChangeWeakWeilRepresentationStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockPolynomialVectorsReframeSourceStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ReframeVacuumAndLiftVectorStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaSeriesEqThetaLiftDefiniteGroupFormStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExtremalVectorValuesLoweringAndTorusStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelCharacterPlacesOddAndPrincipalLevelStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RevPosRevPos

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdSpan
variable {D : D7}

theorem compAt_fin {V : HSp D} (θ : InfFam D) {k : GA D V} (hk : k ∈ GfC V) (τ : D.what₂.Tau) :
    compAt θ τ (Formalism.L2.Theta.mt V k) = 1 := by
  have h : (Formalism.L2.Theta.mt V k).map (infPart D) = 1 := congrArg Units.val (MonoidHom.mem_ker.1 hk)
  have h2 : compAt θ τ (Formalism.L2.Theta.mt V k) = ((Formalism.L2.Theta.mt V k).map (infPart D)).map (θ τ) := rfl
  rw [h2, h, Matrix.map_one _ (map_zero _) (map_one _)]

theorem fvec_om_fin {S T : HSp D} (C : Ctx S T) {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hom : IsWeak C.ψ S T om)
    {B : C.Bas} (hB : C.IsB B) {k : GA D S} (hk : k ∈ GfC S) {u : WO S T → ℂ} (hu : C.IsTh u) :
    (C.IsFock B u → C.IsFock B (om (k, 1) u)) ∧ ∀ Q, om (k, 1) (C.fvec B u Q) = C.fvec B (om (k, 1) u) Q := by
  have h1 : C.mvB 1 B = B := (((GlobalTheory.Ker.onBasis_frame_period D S T C).2 B hB).2.2.2.2.2 1).2.2.1 (GfC T).one_mem
  have h2 := (GlobalTheory.Ker.WeakMove.om_move D S T C om hom k 1 u hu).2 B hB
  rw [h1] at h2
  refine ⟨h2.1, fun Q => ?_⟩
  rw [h2.2 Q, show (fun τ => compAt C.θ τ (Formalism.L2.Theta.mt S k)) = fun _ => 1 from funext fun τ => compAt_fin C.θ hk τ]
  rfl

set_option maxHeartbeats 1000000 in
theorem span_std {S T : HSp D} (C : Ctx S T) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (hom : IsWeak C.ψ S T om)
    (hc : ContT C.ψ om) (hsig : T.SigOK) (hsz : 4 * (Module.finrank ℚ D.host.E * T.rank) + 4 ≤ S.rank) (hn : T.rank ≤ S.rank)
    (B₀ : C.Bas) (hB₀ : C.IsB B₀) (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (hBS : ∀ τ, (BS τ)ᴴ * BS τ = 1)
    (ΛT : Lt D.host.E T.rank) (hsd : IsSelfDualC T ΛT) (hAA : IsAA C.X.Λ ΛT)
    (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D))
    (hβS : Formalism.L2.DIV.IsFrame βS (stdL D.host.E S.rank)) (hβT : Formalism.L2.DIV.IsFrame βT ΛT)
    (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (hPg : Pg.Nonempty)
    (hodd : ∀ PP, PP ∈ Pg ∨ PP ∈ Q → (2 : 𝓞 D.host.E) ∉ PP.asIdeal) (f₀ f : WO S T → ℂ)
    (hf : IsThPVecOf C.ψ C.θ S T (fun _ => 1) (C.sB B₀) (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E))
      (ΛT : Set (Fin T.rank → D.host.E)) βS βT Pg Q ξ f₀ f)
    (p q : D.what₂.Tau → ℕ) (ap am : D.what₂.Tau → ℕ → ℕ) (hp : ∀ τ, p τ = C.X.p0) (hq : ∀ τ, q τ = C.q0)
    (pt : MvPolynomial (FVar D T.rank S.rank) ℂ → WO S T → ℂ) (U : Submodule ℂ (MvPolynomial (FVar D T.rank S.rank) ℂ))
    (hpt : ∀ P, pt P = pureTensorO C.ψ C.θ S T (fun _ => 1) (C.sB B₀) BS B₀ f P)
    (hΔ : Formalism.IndefR.Datum.delta p q ap am ∈ U) (hU : ∀ h ∈ GinfC S, ∀ P ∈ U, ∃ P' ∈ U, om (h, 1) (pt P) = pt P')
    (φ : GA D T → ℂ) (hk : LowKilled C.θ T (revB C.X.p0 B₀) φ)
    (hw : ∀ (ρ : D.what₂.Tau) (s : Fin T.rank → ℝ), ∃ l : ℂ,
      om (1, torAt C.θ T (revB C.X.p0 B₀) ρ s) (pt (Formalism.IndefR.Datum.delta p q ap am)) = l • pt (Formalism.IndefR.Datum.delta p q ap am) ∧
      ∀ g, φ (g * torAt C.θ T (revB C.X.p0 B₀) ρ s) = l * φ g)
    (hl : ∀ γ ∈ GQ T, ∀ g, φ (γ * g) = φ g)
    (hlev : ∀ k ∈ GfC T, Lev.finE T k ∈ Formalism.L2.DIV.St βT → (∀ PP ∈ Pg, Formalism.L2.DIV.redFn βT PP (Lev.finE T k) = 1) →
      om (1, k) f = f ∧ ∀ g, φ (g * k) = φ g)
    (hb : ∃ K : ℝ, ∀ g, ‖φ g‖ ≤ K) :
    φ ∈ Submodule.span ℂ {ψ : GA D T → ℂ | ∃ (h : GA D S) (P : MvPolynomial (FVar D T.rank S.rank) ℂ), P ∈ U ∧
      ψ = fun g => om (h, g) (pt P) 0} := by
  obtain ⟨Lv, M, f', k₀, hw2, hM, hMm, hbase, hk₀, hfu, hu1, hu2, hu3, hK⟩ :=
    GlobalTheory.T.thetaLiftFiniteVector_eq_translate_levelDatum D S T C om hom hn B₀ hB₀ ΛT hsd hAA βS βT hβS hβT Pg Q ξ hPg hodd f₀ f hf
  set u := C.uVec Lv hn f' with hu
  have hinv : ∀ x, om (k₀⁻¹, 1) (om (k₀, 1) x) = x := fun x => by
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, inv_mul_cancel, mul_one]
    exact congrArg (fun e : Module.End ℂ (WO S T → ℂ) => e x) om.map_one
  have hf1 : C.IsTh f := hfu ▸ hom.om_pres _ _ hu1
  have hf2 : C.IsFock B₀ f := hfu ▸ (fvec_om_fin C hom hB₀ hk₀ hu1).1 hu2
  have hf3 : f ≠ 0 := fun h0 => hu3 (by rw [← hinv u, ← hfu, h0, map_zero])
  obtain ⟨hB, hs, c, c', Q₀, hQ₀, hQ₀', hne, hall⟩ :=
    GlobalTheory.T.stableFockSpan_contains_rowHighestPolynomials D S T C om hom hn B₀ hB₀ BS hBS f hf1 hf2 hf3 p q ap am hp hq pt U hpt hΔ hU
  set B : C.Bas := revB C.X.p0 B₀ with hBdef
  have hfock : ∀ x, C.IsFock B₀ x → C.IsFock B x := fun x hx τ => by rw [hs]; exact hx τ
  obtain ⟨z, z1, z2, z3, z4⟩ := GlobalTheory.T.exists_continuous_realScalar_character_weakWeil D S T C om hom hc
  obtain ⟨m, hm⟩ := GlobalTheory.T.realPoints_unitaryCharacter_eq_detPower D C.θ T C.inf hsig z z1 z2 z3
  have hsc : ∀ a ∈ GinfC T, RealScal C om B a (detPow C.θ T m a) := fun a ha => hm a ha ▸ z4 B hB a ha
  have htor : ∀ ρ s, torAt C.θ T B ρ s ∈ GinfC T := fun ρ s => by
    unfold torAt atTau
    split_ifs with h
    exacts [h.choose_spec.1, (GinfC T).one_mem]
  have hhol : HolUpTo C B (ThFr.wtOf C.X C.hr c c' S.rank) (detPow C.θ T m) φ := by
    refine GlobalTheory.T.holomorphicUpToFactor_of_loweringKilled_torusWeight D S T C B hB _ m φ hk fun ρ s g => ?_
    obtain ⟨l, h1, h2⟩ := hw ρ s
    have h3 := (GlobalTheory.T.compactTorus_acts_fockVector_rowHighest D S T C om hom B hB f hf1 (hfock f hf2) c c' Q₀ hQ₀ ρ s m (hsc _ (htor ρ s))).2
    rw [hQ₀', h1] at h3
    rw [h2, smul_left_injective ℂ hne h3]
  have hcore := GlobalTheory.T.mem_span_thetaSeries_of_boundedHolomorphic D S T C om hom hsz Lv hn M hw2 hM hMm B hB f' ⟨hbase.th, hbase.ne, hfock _ hbase.fock, hbase.lat⟩ c c' _ φ
    hsc hhol hl (fun k κ hkκ => by
      obtain ⟨h1, h2⟩ := hlev k hkκ.1 (hK k κ hkκ).1 (hK k κ hkκ).2
      refine ⟨?_, h2⟩
      have h3 : om (1, k) (om (k₀⁻¹, 1) f) = om (k₀⁻¹, 1) (om (1, k) f) := by
        rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
        simp only [Prod.mk_mul_mk, one_mul, mul_one]
      rw [h1, hfu, hinv] at h3
      exact h3) hb
  refine Submodule.span_mono ?_ hcore
  rintro _ ⟨h, Q', hQ', rfl⟩
  obtain ⟨P, hP, hPe⟩ := hall Q' hQ'
  refine ⟨h * k₀⁻¹, P, hP, funext fun g => ?_⟩
  rw [← hPe, hfu, ← (fvec_om_fin C hom hB hk₀ hu1).2 Q', ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk,
    inv_mul_cancel_right, mul_one]

theorem eq_zero_of_value {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (e : H →ₗ[ℂ] MMap M) (d : ℂ) (μ : Measure (GA D V)) (𝓕 : Set (GA D V))
    (he : ∀ x y, inner ℂ x y = d * ipM M μ 𝓕 (e x) (e y)) (v : M.Vec) (hv : ∀ τ, ‖(v τ : M.H τ)‖ = 1) (x : H)
    (hx : e x v = 0) : x = 0 := by
  rw [← inner_self_eq_zero (𝕜 := ℂ), he]
  refine mul_eq_zero_of_right _ ?_
  by_cases h : ∃ c, IsMultIP M μ 𝓕 (e x) (e x) c
  · have h1 := (ipM_spec M μ 𝓕 _ _ h v v).2
    simp only [hx, Pi.zero_apply, mul_zero, integral_zero, inner_self_eq_norm_sq_to_K, hv] at h1
    simpa using h1.symm
  · exact dif_neg h

theorem isB_onb {S T : HSp D} (C : Ctx S T) {Sp : D.what₂.Tau → SPar} (M : DSModel T Sp)
    (hε : ∀ τ a, M.ε τ a = decide ((a : ℕ) < C.X.p0)) : C.IsB (onb M) ∧ C.sB (onb M) = cart M := by
  have hJ : ∀ τ, Formalism.REAL.Jm (M.ε τ) = sgnM C.X := fun τ => by
    unfold Formalism.REAL.Jm sgnM
    congr 1
    funext a
    rw [hε, sgn]
    by_cases h : (a : ℕ) < C.X.p0 <;> simp [h]
  have hu : ∀ τ, IsUnit (M.fr τ).det := fun τ => (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  refine ⟨fun τ => ?_, funext fun τ => ?_⟩
  · have h1 : M.fr τ * (M.fr τ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ (hu τ)
    rw [← M.fr_gram τ, ← hJ τ]; unfold onb
    calc _ = (M.fr τ * (M.fr τ)⁻¹)ᴴ * Formalism.REAL.Jm (M.ε τ) * (M.fr τ * (M.fr τ)⁻¹) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [h1]; simp
  · unfold Ctx.sB cart onb
    rw [Matrix.nonsing_inv_nonsing_inv _ (hu τ), hJ]

set_option maxHeartbeats 1000000 in

theorem span_any {S T : HSp D} (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (θ : InfFam D) (hθ : IsInfFam θ)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (hom : IsWeak ψ S T om) (hc : ContT ψ om)
    (b : Module.Basis (Fin S.rank) D.host.E S.V) (hb : StdFrame.OrthFrame (reS S b)) (hev : Even S.rank) (p₀ q₀ : ℕ)
    (hpq : p₀ + q₀ = T.rank) (hsig : T.SigOK) (hsigv : ∀ τ, T.sig (tauE D τ) = (p₀, q₀))
    (hsz : 4 * (Module.finrank ℚ D.host.E * T.rank) + 4 ≤ S.rank) (hn : T.rank ≤ S.rank)
    {Sp : D.what₂.Tau → SPar} (M : DSModel T Sp) (hε : ∀ τ a, M.ε τ a = decide ((a : ℕ) < p₀))
    (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (hBS : ∀ τ, (BS τ)ᴴ * gramAt D S τ * BS τ = 1)
    (ΛS : Lt D.host.E S.rank) (hΛS : (ΛS : Set (Fin S.rank → D.host.E)) = L0c D S)
    (ΛT : Lt D.host.E T.rank) (hsd : IsSelfDualC T ΛT)
    (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D))
    (hβS : Formalism.L2.DIV.IsFrame βS ΛS) (hβT : Formalism.L2.DIV.IsFrame βT ΛT)
    (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (hPg : Pg.Nonempty)
    (hodd : ∀ PP, PP ∈ Pg ∨ PP ∈ Q → (2 : 𝓞 D.host.E) ∉ PP.asIdeal) (f₀ f : WO S T → ℂ)
    (hf : IsThPVecOf ψ θ S T (fun _ => 1) (cart M) (ΛS : Set (Fin S.rank → D.host.E))
      (ΛT : Set (Fin T.rank → D.host.E)) βS βT Pg Q ξ f₀ f)
    (ap am : D.what₂.Tau → ℕ → ℕ)
    (pt : MvPolynomial (FVar D T.rank S.rank) ℂ → WO S T → ℂ) (U : Submodule ℂ (MvPolynomial (FVar D T.rank S.rank) ℂ))
    (hpt : ∀ P, pt P = pureTensorO ψ θ S T (fun _ => 1) (cart M) BS (onb M) f P)
    (Δ : MvPolynomial (FVar D T.rank S.rank) ℂ)
    (hΔe : Δ = Formalism.IndefR.Datum.delta (fun τ => (T.sig (tauE D τ)).1) (fun τ => (T.sig (tauE D τ)).2) ap am)
    (hΔ : Δ ∈ U) (hU : ∀ h ∈ GinfC S, ∀ P ∈ U, ∃ P' ∈ U, om (h, 1) (pt P) = pt P')
    (φ : GA D T → ℂ) (hk : LowKilled θ T (revB p₀ (onb M)) φ)
    (hw : ∀ (ρ : D.what₂.Tau) (s : Fin T.rank → ℝ), ∃ l : ℂ,
      om (1, torAt θ T (revB p₀ (onb M)) ρ s) (pt Δ) = l • pt Δ ∧ ∀ g, φ (g * torAt θ T (revB p₀ (onb M)) ρ s) = l * φ g)
    (hl : ∀ γ ∈ GQ T, ∀ g, φ (γ * g) = φ g)
    (hlev : ∀ k ∈ GfC T, Lev.finE T k ∈ Formalism.L2.DIV.St βT → (∀ PP ∈ Pg, Formalism.L2.DIV.redFn βT PP (Lev.finE T k) = 1) →
      om (1, k) f = f ∧ ∀ g, φ (g * k) = φ g)
    (hbd : ∃ K : ℝ, ∀ g, ‖φ g‖ ≤ K) :
    φ ∈ Submodule.span ℂ {ψ : GA D T → ℂ | ∃ (h : GA D S) (P : MvPolynomial (FVar D T.rank S.rank) ℂ), P ∈ U ∧
      ψ = fun g => om (h, g) (pt P) 0} := by
  subst hΔe
  obtain ⟨C₀, hp0, hq0, hAA, -⟩ := GlobalTheory.Ker.Inhab.inhabitants.1 D (reS S b) T _ _ ΛT hb.gram_eq hev hpq hsig hsigv hsd
  subst hp0
  let C : Ctx (reS S b) T := { C₀ with ψ := ψ, std := hψ, θ := θ, inf := hθ }
  obtain ⟨hB, hs⟩ := isB_onb C M hε
  obtain ⟨e, he, hom'⟩ := GlobalTheory.T.exists_frameChange_weakWeilRepresentation D S T b
  obtain ⟨om', hw', hc', hre⟩ := hom' ψ om hom hc
  obtain ⟨BS', hBS', hpt'⟩ := GlobalTheory.T.fockPolynomialVectors_reframeSource D S T b ψ θ hθ BS
  obtain ⟨βS', hβS', hvec⟩ := GlobalTheory.T.reframe_vacuum_and_liftVector D S T b hb ψ θ _ ΛS _ βS βT Pg Q ξ _ _ hΛS hβS hf
  have hg : ∀ τ, gramAt D (reS S b) τ = 1 := fun τ => by
    unfold gramAt
    rw [hb.gram_eq, Matrix.map_one _ (map_zero _) (map_one _)]
  have key := span_std C om' hw' hc' hsig hsz hn _ hB BS' (fun τ => by
      have := hBS' τ
      rwa [hBS, hg, Matrix.mul_one] at this) ΛT hsd hAA βS' βT hβS' hβT Pg Q ξ hPg hodd _ _
    (by rw [hs]; exact hvec) (fun τ => (T.sig (tauE D τ)).1) (fun τ => (T.sig (tauE D τ)).2) ap am
    (fun τ => by rw [hsigv]) (fun τ => by rw [hsigv]; exact hq0.symm)
    (fun P => reF S T b (pt P)) U (fun P => by rw [hs]; exact (congrArg (reF S T b) (hpt P)).trans (hpt' _ _ _ P).symm) hΔ
    (fun h hh P hP => by
      obtain ⟨P', h1, h2⟩ := hU _ ((he h).2 hh) P hP
      exact ⟨P', h1, by rw [hre, h2]⟩)
    φ hk
    (fun ρ s => by
      obtain ⟨l, h1, h2⟩ := hw ρ s
      refine ⟨l, ?_, h2⟩
      rw [hre, map_one e]
      exact (congrArg (reF S T b) h1).trans (map_smul _ _ _))
    hl
    (fun k hk h1 h2 => by
      obtain ⟨h3, h4⟩ := hlev k hk h1 h2
      exact ⟨by rw [hre, map_one e, h3], h4⟩)
    hbd
  refine Submodule.span_mono ?_ key
  rintro _ ⟨h, P, hP, rfl⟩
  exact ⟨e h, P, hP, funext fun g => by rw [hre, reF_zero]⟩

theorem pureTensorO_one {S T : HSp D} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (f : WO S T → ℂ) : pureTensorO ψ θ S T sS sT BS BT f 1 = f := by
  have h : (1 : MvPolynomial (FVar D T.rank S.rank) ℂ) = MvPolynomial.basisMonomials _ ℂ 0 := by
    rw [MvPolynomial.coe_basisMonomials]; rfl
  unfold pureTensorO pureTensorL
  rw [h, Module.Basis.constr_basis]
  simp [opPow]

theorem onBasis_pos {k : ℕ} {G B : Matrix (Fin k) (Fin k) ℂ} (h : IsONBasis G 1 B k) : Bᴴ * G * B = 1 := by
  obtain ⟨ε, h1, h2, -⟩ := h
  rw [h2, ← Matrix.diagonal_one]
  congr 1
  funext a
  rcases h1 a with h | h
  · simp [h.1]
  · exact absurd a.2 (not_lt.2 h.2)

theorem ranks (i : Fin D.R.m) : (D.R.sigW ((i : ℕ) + 1)).1 + (D.R.sigW ((i : ℕ) + 1)).2 = D.R.r ∧ Even D.R.nV := by
  have := D.R.m_add_three_le_k
  have := i.2
  have h1 := D.R.k_even
  have h2 := D.R.m_even
  have h3 := D.R.t_odd
  simp only [Ranks.sigW, Ranks.nV, Ranks.r]
  rw [Nat.even_iff] at *
  rw [Nat.odd_iff] at h3
  omega

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

set_option maxHeartbeats 1000000 in

theorem value_mem_span (hP : GlobalTheory.Published.CuspRapidDecay) (hsz : GlobalTheory.IndefiniteRowSideFullHecke.ThetaTranslateSize.SizeOK D) (hL : R.toLevCh.Is A.μ0)
    (hM : R.IsModels) (hT : R.IsThP) (i : Fin D.R.m) (t : T0) (u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (w₀ : (R.cV i).W)
    (hu : IsExtVec (R.MW i (sg0 D A)) (fun ρ => u ρ)) (hΔ : R.ioP i (PiTensorProduct.tprod ℂ u) w₀ = RealDat.Delta i)
    (T : MMap (R.MW i (sg0 D A))) (hTm : T ∈ R.Wall i (sg0 D A)) :
    T (fun ρ => u ρ) ∈ Submodule.span ℂ {ψ : GA D (Wc D i) → ℂ | ∃ (h : GA D (Vc D i)) (P : PolF D (Wc D i).rank (Vc D i).rank),
      P ∈ LinearMap.range (R.ioP i (PiTensorProduct.tprod ℂ u)) ∧ ψ = fun g => R.ωP i t (h, g) (R.ptP i t P) 0} := by
  have hin : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩
  have hrV : (Vc D i).rank = D.R.nV := D.sp.V_rank _ hin.1 hin.2
  have hrW : (Wc D i).rank = D.R.r := rank_Wc i
  have ho := D.sp.V_std ((i : ℕ) + 1) hin.1 hin.2
  rw [StdFrame.neg_eq_false_of_posDef D i (hM.vpos i)] at ho
  obtain ⟨b, hb⟩ := StdFrame.exists_orthFrame (Vc D i) hrV ho
  have hsigW : ∀ τ, (Wc D i).sig (tauE D τ) = D.R.sigW ((i : ℕ) + 1) := fun τ => D.sp.W_sigval _ hin.1 hin.2 _
  have hpq := (ranks i).1.trans hrW.symm
  have hev : Even (Vc D i).rank := by rw [hrV]; exact (ranks i).2
  have hsz' : 4 * (Module.finrank ℚ D.host.E * (Wc D i).rank) + 4 ≤ (Vc D i).rank := by
    rw [hrV, hrW, finrank_host D]
    calc 4 * (2 * D.R.f * D.R.r) + 4 = 8 * D.R.f * D.R.r + 4 := by ring
      _ ≤ _ := hsz
  have hn : (Wc D i).rank ≤ (Vc D i).rank := hrW.le.trans (r_le_V i)
  have hsd := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hL.βW i)
  obtain ⟨hPg, hodd, hlev⟩ := GlobalTheory.T.levelCharacter_places_odd_and_principal_level D T0 R.toLevCh A.μ0 hL
  have hmult := (GlobalTheory.MultMem.mem_mult_iff D _ _ _ _ _ _ _).1 hTm
  obtain ⟨hk, hwt⟩ := GlobalTheory.T.extremalVector_values_lowering_and_torus D G Pl0 T0 A Ks R hM hT i t u w₀ (D.R.sigW ((i : ℕ) + 1)).1 (fun τ => congrArg Prod.fst (hsigW τ))
    (le_of_le_of_eq (Nat.le_add_right _ _) hpq) hu T hTm
  have hth : ∀ i t, IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vP i t) := fun i t =>
    (pureTensorO_one R.ψ R.θ _ _ _ _ (R.vP i t)) ▸ hT.pt_theta i t 1
  have hε : ∀ τ a, (R.MW i (sg0 D A)).ε τ a = decide ((a : ℕ) < (D.R.sigW ((i : ℕ) + 1)).1) := fun τ a => by
    rw [hM.order i τ a, hsigW]
  have hU : ∀ h ∈ GinfC (Vc D i), ∀ P ∈ LinearMap.range (R.ioP i (PiTensorProduct.tprod ℂ u)),
      ∃ P' ∈ LinearMap.range (R.ioP i (PiTensorProduct.tprod ℂ u)), R.ωP i t (h, 1) (R.ptP i t P) = R.ptP i t P' := by
    rintro h hh _ ⟨w, rfl⟩
    exact ⟨_, ⟨(R.cV i).ρ h w, rfl⟩, (hT.ioP i t).1 h hh _ w⟩
  have hlv : ∀ k ∈ GfC (Wc D i), Lev.finE (Wc D i) k ∈ Formalism.L2.DIV.St (R.βW i) →
      (∀ PP ∈ R.Pg, Formalism.L2.DIV.redFn (R.βW i) PP (Lev.finE (Wc D i) k) = 1) →
      R.ωP i t (1, k) (R.vP i t) = R.vP i t ∧ ∀ g, T (fun ρ => u ρ) (g * k) = T (fun ρ => u ρ) g := fun k hk h1 h2 =>
    ⟨GlobalTheory.T.weilFiniteVector_fixed_principalLevel_coeffSpace D G Pl0 T0 A Ks R hL hT.ωP hT.vP hth i t k (hlev i k hk h1 h2).1, fun g =>
      (hmult.lev _ k (hlev i k hk h1 h2).1 g).trans (by rw [(hlev i k hk h1 h2).2, one_mul])⟩
  exact span_any R.ψ (hT.ωP i t).std R.θ hM.inf (R.ωP i t) (isWeak_of_datum (hT.ωP i t))
    (fun f hf w => ((hT.ωP i t).om_cont f hf w).comp (Continuous.prodMk_right 1)) b hb hev _ _ hpq (D.sp.W_sig _) hsigW hsz' hn
    (R.MW i (sg0 D A)) hε (R.BV i) (fun τ => onBasis_pos (hM.BV i τ)) (R.ΛV i) (GlobalTheory.OneMapRef.FactsLat.selfDual_frame_level_one_lattice_eq_standard (hL.βV i))
    (R.ΛW i) hsd (R.βV i) (R.βW i) (hL.βV i).choose_spec.1 (hL.βW i).choose_spec.1 R.Pg (R.Q t) (R.xiR t) hPg (hodd t)
    (R.vacP i) (R.vP i t) (hT.vP i t) _ _ (R.ptP i t) _ (fun _ => rfl) _ hΔ (LinearMap.mem_range_self _ w₀) hU _ hk hwt (hmult.aut _).left hlv
    (GlobalTheory.CuspDecay.bounded_of_cuspForm hP hM.inf (hmult.aut _) (hmult.cusp _))

theorem mem_range_of_value {X H Y Z : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup H] [Module ℂ H] [AddCommGroup Y] [Module ℂ Y]
    [AddCommGroup Z] [Module ℂ Z] (th : X →ₗ[ℂ] Y) (e : H →ₗ[ℂ] Y) (ev : Y →ₗ[ℂ] Z) (W : Submodule ℂ Y) (hr : LinearMap.range e = W)
    (hth : ∀ x, th x ∈ W) (hev : ∀ y, ev (e y) = 0 → y = 0) (s : Set Z) (hs : ∀ z ∈ s, ∃ x, ev (th x) = z) (T : Y) (hT : T ∈ W)
    (hm : ev T ∈ Submodule.span ℂ s) : T ∈ LinearMap.range th := by
  obtain ⟨x, hx⟩ : ev T ∈ LinearMap.range (ev ∘ₗ th) := Submodule.span_le.2 (fun z hz => hs z hz) hm
  obtain ⟨y, hy⟩ := hr.ge (W.sub_mem (hth x) hT)
  have h0 := hev y (by rw [hy, map_sub]; exact sub_eq_zero.2 hx)
  rw [h0, map_zero] at hy
  exact ⟨x, sub_eq_zero.1 hy.symm⟩

def evAtVec {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (v : M.Vec) : MMap M →ₗ[ℂ] (GA D V → ℂ) where
  toFun T := T v
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

set_option maxHeartbeats 1000000 in

theorem range_thF (hP : GlobalTheory.Published.CuspRapidDecay) (hsz : GlobalTheory.IndefiniteRowSideFullHecke.ThetaTranslateSize.SizeOK D) (hL : R.toLevCh.Is A.μ0) (hF : R.IsFam)
    (hM : R.IsModels) (hT : R.IsThP) (i : Fin D.R.m) (t : T0) : LinearMap.range (R.thF i t) = R.Wall i (sg0 D A) := by
  refine le_antisymm (by rintro _ ⟨x, rfl⟩; exact hT.thF_mem i t x) fun T hTm => ?_
  obtain ⟨v, hv, u, w₀, huv, -, hΔ⟩ := GlobalTheory.IoExtremal.ioExt D G Pl0 T0 A Ks R hL hF hM hT i
  obtain rfl : v = fun ρ => (u ρ : (R.MW i (sg0 D A)).sm ρ) := (funext huv).symm
  refine mem_range_of_value (R.thF i t) (R.HW i (sg0 D A)).e (evAtVec _ fun ρ => u ρ) _ (hM.HW i (sg0 D A)).2.1 (hT.thF_mem i t)
    (fun y hy => eq_zero_of_value _ _ _ _ _ (hM.HW i (sg0 D A)).2.2 _ (fun τ => (hv τ).1) y hy) _ ?_ T hTm
    (value_mem_span R hP hsz hL hM hT i t u w₀ hv hΔ T hTm)
  rintro _ ⟨h, _, ⟨w, rfl⟩, rfl⟩
  obtain ⟨x, hx⟩ := GlobalTheory.T.thetaSeries_eq_thetaLift_definiteGroup_form D G Pl0 T0 A Ks R hL hM hT i t h w
  exact ⟨x, funext (hx u)⟩

theorem span_translates {X H Y Γ : Type} [Group Γ] [AddCommGroup X] [Module ℂ X] [AddCommGroup H] [Module ℂ H] [AddCommGroup Y]
    [Module ℂ Y] (th : X →ₗ[ℂ] Y) (e : H →ₗ[ℂ] Y) (W : Submodule ℂ Y) (hr : LinearMap.range e = W) (hth : LinearMap.range th = W)
    (ρ : Representation ℂ Γ H) (tr : Γ → Y →ₗ[ℂ] Y) (htr : ∀ g y, e (ρ g y) = tr g (e y)) :
    Submodule.span ℂ {y | ∃ (g : Γ) (x : X), y = tr g (th x)} = W := by
  refine le_antisymm (Submodule.span_le.2 ?_) fun T hT => ?_
  · rintro _ ⟨g, x, rfl⟩
    obtain ⟨y, hy⟩ := hr.ge (hth.le ⟨x, rfl⟩)
    exact hr.le ⟨ρ g y, by rw [htr, hy]⟩
  · obtain ⟨x, hx⟩ := hth.ge hT
    obtain ⟨y, hy⟩ := hr.ge hT
    refine Submodule.subset_span ⟨1, x, ?_⟩
    rw [hx, ← hy, ← htr, map_one, Module.End.one_apply]

set_option maxHeartbeats 1000000 in
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaTranslateSize in

theorem spanAt (hP : GlobalTheory.Published.CuspRapidDecay) (hsz : SizeOK D) (hL : R.toLevCh.Is A.μ0) (hF : R.IsFam)
    (hM : R.IsModels) (hT : R.IsThP) (i : Fin D.R.m) (t : T0) : SpanAt R i t :=
  span_translates (R.thF i t) (R.HW i (sg0 D A)).e _ (hM.HW i (sg0 D A)).2.1 (range_thF R hP hsz hL hF hM hT i t)
    (R.gW i (sg0 D A)) (transl R i) (hM.gW i (sg0 D A))

set_option maxHeartbeats 1000000 in
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaTranslateSize in

theorem goodRangeAt (hP : GlobalTheory.Published.CuspRapidDecay) (hsz : SizeOK D) (hL : R.toLevCh.Is A.μ0) (hG : R.grp_record) (hF : R.IsFam)
    (hM : R.IsModels) (hT : R.IsThP) (i : Fin D.R.m) (t : T0) : GoodRangeAt R i t := by
  rw [goodRangeAt_iff hM.HW hT.thG, LinearMap.range_comp, range_thF R hP hsz hL hF hM hT i t]
  refine le_antisymm ?_ fun U hU => ⟨U, hU.1, sub_eq_zero.1 hU.2⟩
  rintro _ ⟨U, hU, rfl⟩
  exact GlobalTheory.GoodProjLevel.proj_mem_good R hL hG R.hv0 i R.triv U hU

end GlobalTheory.AdSpan

end
