import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftLeftInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundDomLtTop
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LintegralSiegelConeInvModulusLtTopWeil
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LintegralFundamentalDomainLeOfMeetsOrbits
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittRankLeHermitianSignatureStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelSetWittFrameCompactBoundStatement
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
open scoped TensorProduct NNReal Matrix ENNReal
open GlobalTheory.WeilM GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.ThKGrowthBd

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] in

theorem isHermND_skew {σ : E →ₐ[F] E} (hσ : ∀ x, σ (σ x) = x) {B : Base F E} {d : ℕ} {W : Spc F E d} {r s : ℕ}
    (h : W.IsSkew σ B r s) {c : E} (hc : c ≠ 0) (hcs : σ c = -c) : IsHermND σ (c • W.J.map σ) := by
  refine ⟨fun i j => ?_, ?_⟩
  · simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_mul, hσ, hcs]
    rw [h.skew j i]
    ring
  · have hJ : W.J.det ≠ 0 := by
      obtain ⟨w⟩ : Nonempty (NumberField.InfinitePlace F) := inferInstance
      intro hz
      apply GlobalTheory.UnitaryVol.det_ne_zero_of_isCartan (h.cartan w)
      rw [Matrix.det_smul, show W.J.map (B.emb w).1 = ((B.emb w).1).mapMatrix W.J from rfl, ← RingHom.map_det, hz,
        map_zero, mul_zero]
    rw [Matrix.det_smul, show W.J.map σ = (σ : E →+* E).mapMatrix W.J from rfl, ← RingHom.map_det]
    exact mul_ne_zero (pow_ne_zero _ hc) ((map_ne_zero _).2 hJ)

open scoped Classical in

theorem growth_bd : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : ∀ x, σ (σ x) = x) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), GlobalTheory.ThK.KP → IsTriple B G X om om' →
    ∀ (c : E) (hc : c ≠ 0), σ c = -c →
    ∃ N : ℕ, ∀ Φ ∈ GlobalTheory.ThK.PolData B G.M, ∃ C : ℝ, ∀ g : GAd σ (c • G.W.J.map σ),
      ‖G.M.I om Φ ((toGAd hσ G.W.J hc).symm g)‖ ≤ C * (height σ (c • G.W.J.map σ) g : ℝ) ^ N := by
  intro F E _ _ _ _ _ σ hσ B a a' G X om om' hKP hT c hc hcs
  have hP := GlobalTheory.ThK.Inhab.pairV hT
  have hcm := hT.base.cm
  have hTB : ThetaBasic := GlobalTheory.T.theta_basic_properties hKP.base
  have hb := hTB F E σ B a (a + a') G.V G.W G.M X.β (X.β / X.α) om (a - G.p) G.p (a + a' - (G.p + G.q)) (G.p + G.q) hP

  have hJ' : IsHermND σ (c • G.W.J.map σ) := isHermND_skew hσ hT.geo.hW hc hcs
  obtain ⟨rW, XW, YW, hWW⟩ := exists_isWittFrame hcm hJ'
  obtain ⟨KW, ΩW, cW, hKW, hΩW, -, -, -, -, hcovW, -, -, ⟨Ch, A, hCh⟩, -⟩ :=
    hKP.siegelSetUnitary F E σ hcm (a + a') (c • G.W.J.map σ) hJ' rW XW YW hWW
  obtain ⟨Cf, hCf, hCfS⟩ := exists_isCompact_projFin (X := XW) (Y := YW) hΩW cW hKW

  have hJV : IsHermND σ ((1 : E) • G.V.J.map σ) := by
    rw [one_smul]; exact GlobalTheory.UnitaryVol.isHermND_map hσ hT.geo.hV
  let e : UA σ G.V.J ≃* GAd σ ((1 : E) • G.V.J.map σ) :=
    MulEquiv.subgroupCongr (GlobalTheory.SiegelSet.ug_eq_hr (F := F) (J := G.V.J) hσ (one_ne_zero : (1 : E) ≠ 0))
  have he : Continuous e := continuous_subtype_val.subtype_mk _
  have he' : Continuous e.symm := continuous_subtype_val.subtype_mk _
  have : BorelSpace (UA σ G.V.J) := ⟨rfl⟩
  have : ContinuousMul (UA σ G.V.J) := ⟨by
    have h3 : (fun p : UA σ G.V.J × UA σ G.V.J => p.1 * p.2) = fun p => e.symm (e p.1 * e p.2) :=
      funext fun p => by rw [← map_mul, MulEquiv.symm_apply_apply]
    rw [h3]
    exact he'.comp ((he.comp continuous_fst).mul (he.comp continuous_snd))⟩
  have := hP.good.haar
  have := GlobalTheory.UnitaryVol.countable_ratU σ G.V.J
  have : MeasurableMul (UA σ G.V.J) :=
    ⟨fun g => (continuous_const.mul continuous_id).measurable, fun g => (continuous_id.mul continuous_const).measurable⟩
  have hH : (G.M.μ.map e).IsHaarMeasure := MulEquiv.isHaarMeasure_map G.M.μ e he he'
  obtain ⟨r₀, Xf, Yf, hW⟩ := exists_isWittFrame hcm hJV
  obtain ⟨-, hs₀⟩ := GlobalTheory.T.witt_rank_le_hermitian_signature F E σ B a G.V (a - G.p) G.p hT.base hT.geo.hV r₀ Xf Yf hW
  obtain ⟨K, Ω, c', hK, hΩ, -, hc', -, hcl, hcov, ⟨C₀, hC₀, hconj⟩, hmeas, -, -⟩ :=
    hKP.siegelSetUnitary F E σ hcm a ((1 : E) • G.V.J.map σ) hJV r₀ Xf Yf hW
  obtain ⟨-, C₁, hC₁⟩ := hmeas _ hH
  have hSm : MeasurableSet (GlobalTheory.SiegelSet.siegelSet σ ((1 : E) • G.V.J.map σ) Xf Yf Ω c' K) := hcl.measurableSet
  have hS' : MeasurableSet (e ⁻¹' GlobalTheory.SiegelSet.siegelSet σ ((1 : E) • G.V.J.map σ) Xf Yf Ω c' K) :=
    hSm.preimage he.measurable
  have hScov : ∀ g : UA σ G.V.J, ∃ γ ∈ ratU σ G.V.J,
      γ * g ∈ e ⁻¹' GlobalTheory.SiegelSet.siegelSet σ ((1 : E) • G.V.J.map σ) Xf Yf Ω c' K := fun g => by
    obtain ⟨γ, hγ, s', hs', hgs⟩ := hcov (e g)
    obtain ⟨u, -, hu⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hγ)
    have hr : e.symm γ ∈ ratU σ G.V.J := Subgroup.mem_subgroupOf.2 ⟨u, hu⟩
    refine ⟨(e.symm γ)⁻¹, inv_mem hr, ?_⟩
    show e ((e.symm γ)⁻¹ * g) ∈ GlobalTheory.SiegelSet.siegelSet σ ((1 : E) • G.V.J.map σ) Xf Yf Ω c' K
    rw [map_mul, map_inv, MulEquiv.apply_symm_apply, hgs, inv_mul_cancel_left]
    exact hs'

  have hI : ∫⁻ t in GlobalTheory.SiegelSet.cone r₀ c', ENNReal.ofReal (∏ i, t i ^ (Module.finrank ℚ F * (a + a'))) *
      ENNReal.ofReal ((GlobalTheory.SiegelSet.modulus F a t * ∏ i, t i)⁻¹) < ⊤ := by
    have h1 := hT.geo.eBig
    exact GlobalTheory.SiegelSet.lintegral_cone_modulus_lt_top F a r₀ (a + a') hc' (by omega)
  set I := ∫⁻ t in GlobalTheory.SiegelSet.cone r₀ c', ENNReal.ofReal (∏ i, t i ^ (Module.finrank ℚ F * (a + a'))) *
      ENNReal.ofReal ((GlobalTheory.SiegelSet.modulus F a t * ∏ i, t i)⁻¹) with hIdef
  have key : ∀ (θ0 : UA σ G.V.J → ℂ) (A' : ℝ), Continuous θ0 → (∀ γ ∈ ratU σ G.V.J, ∀ g, θ0 (γ * g) = θ0 g) →
      (∀ p ∈ Ω, ∀ t ∈ GlobalTheory.SiegelSet.cone r₀ c', ∀ a₀, GlobalTheory.SiegelSet.IsTorusElt σ ((1 : E) • G.V.J.map σ) Xf Yf t a₀ →
        ∀ k ∈ K, ‖θ0 (e.symm (p * a₀ * k))‖ ≤ A' * ∏ i, t i ^ (Module.finrank ℚ F * (a + a'))) →
      ∫ g in G.M.dom, ‖θ0 g‖ ∂G.M.μ ≤ (C₁ : ℝ) * max A' 0 * I.toReal := by
    intro θ0 A' hθc hθi hθb
    have hA : 0 ≤ max A' 0 := le_max_right _ _
    have hle : ∫⁻ g in G.M.dom, ‖θ0 g‖ₑ ∂G.M.μ ≤ C₁ * (ENNReal.ofReal (max A' 0) * I) := by
      calc ∫⁻ g in G.M.dom, ‖θ0 g‖ₑ ∂G.M.μ
          ≤ ∫⁻ g in e ⁻¹' GlobalTheory.SiegelSet.siegelSet σ ((1 : E) • G.V.J.map σ) Xf Yf Ω c' K, ‖θ0 g‖ₑ ∂G.M.μ :=
            GlobalTheory.lintegral_fundamentalDomain_le_of_meets_orbits (ratU σ G.V.J) G.M.μ hP.good.dom hS' hScov
              hθc.enorm.measurable (fun γ hγ g => by rw [hθi γ hγ g])
        _ = ∫⁻ x in GlobalTheory.SiegelSet.siegelSet σ ((1 : E) • G.V.J.map σ) Xf Yf Ω c' K, ‖θ0 (e.symm x)‖ₑ ∂(G.M.μ.map e) := by
            rw [setLIntegral_map (f := fun x => ‖θ0 (e.symm x)‖ₑ) hSm (hθc.comp he').enorm.measurable he.measurable]
            simp only [MulEquiv.symm_apply_apply]
        _ ≤ C₁ * ∫⁻ t in GlobalTheory.SiegelSet.cone r₀ c', ENNReal.ofReal (max A' 0 * ∏ i, t i ^ (Module.finrank ℚ F * (a + a'))) *
              ENNReal.ofReal ((GlobalTheory.SiegelSet.modulus F a t * ∏ i, t i)⁻¹) := by
            refine hC₁ (fun x => ‖θ0 (e.symm x)‖ₑ) _ (by fun_prop) fun q hq t ht a₀ ha k hk => ?_
            have ht0 : ∀ i, 0 < t i := ht.1
            have hP0 : 0 ≤ ∏ i, t i ^ (Module.finrank ℚ F * (a + a')) :=
              Finset.prod_nonneg fun i _ => pow_nonneg (ht0 i).le _
            rw [← ofReal_norm]
            exact ENNReal.ofReal_le_ofReal
              ((hθb q hq t ht a₀ ha k hk).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hP0))
        _ = C₁ * (ENNReal.ofReal (max A' 0) * I) := by
            rw [hIdef, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
            congr 1
            exact lintegral_congr fun t => by rw [ENNReal.ofReal_mul hA, mul_assoc]
    rw [integral_norm_eq_lintegral_enorm hθc.aestronglyMeasurable]
    refine (ENNReal.toReal_mono (by finiteness) hle).trans (le_of_eq ?_)
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hA, ENNReal.coe_toReal]
    ring

  obtain ⟨N, hN⟩ := GlobalTheory.T.siegel_set_witt_frame_compact_bound F E σ B a (a + a') G.V G.W G.M X.β (X.β / X.α) om _ _ _ _ hP r₀ Xf Yf hW Ω C₀ K c' hΩ hC₀ hK
    hc' hconj hσ c hc Cf hCf
  refine ⟨A * N, fun Φ hΦ => ?_⟩
  have hSΦ := GlobalTheory.ThKRatInv.polData_le_schA B G.M hT.geo.hM hΦ
  obtain ⟨C, hC⟩ := hN Φ hSΦ
  refine ⟨(C₁ : ℝ) * max C 0 * I.toReal * (Ch : ℝ) ^ N, fun g => ?_⟩
  obtain ⟨γ, hγ, s, hs, rfl⟩ := hcovW g
  obtain ⟨u, -, hu⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hγ)
  have hγ' : (toGAd hσ G.W.J hc).symm γ ∈ ratU σ G.W.J := Subgroup.mem_subgroupOf.2 ⟨u, hu⟩
  rw [map_mul, GlobalTheory.ThKRatInv.I_rat_inv hTB B G.M hP Φ hΦ _ hγ']
  set h := (toGAd hσ G.W.J hc).symm s with hhdef
  have hf : projFin σ (c • G.W.J.map σ) (toGAd hσ G.W.J hc h) ∈ Cf := by
    rw [hhdef, MulEquiv.apply_symm_apply]; exact hCfS s hs
  have hcont : Continuous fun g => theta om Φ g h := (hb.1 Φ hSΦ).1.comp (continuous_id.prodMk continuous_const)
  have hinv : ∀ γ ∈ ratU σ G.V.J, ∀ g, theta om Φ (γ * g) h = theta om Φ g h := fun γ hγ g => by
    have := (hb.1 Φ hSΦ).2.1 γ hγ 1 (one_mem _) g h
    rwa [one_mul] at this
  have hk := key (fun g => theta om Φ g h) (C * (ht h : ℝ) ^ N) hcont hinv
    (fun p hp t ht a₀ ha k hk => hC h _ hf p hp t ht a₀ ha k hk rfl)
  have h1 : ‖G.M.I om Φ h‖ ≤ (C₁ : ℝ) * max (C * (ht h : ℝ) ^ N) 0 * I.toReal :=
    (norm_integral_le_integral_norm _).trans hk
  have hH0 : (0 : ℝ) ≤ (ht h : ℝ) ^ N := by positivity
  have h2 : max (C * (ht h : ℝ) ^ N) 0 = max C 0 * (ht h : ℝ) ^ N := by
    rw [← zero_mul ((ht h : ℝ) ^ N), ← max_mul_of_nonneg _ _ hH0, zero_mul]
  have h3 : (ht h : ℝ) = (height σ (c • G.W.J.map σ) s : ℝ) := by
    rw [hhdef]; rfl
  have h4 : (height σ (c • G.W.J.map σ) s : ℝ) ≤ (Ch : ℝ) * (height σ (c • G.W.J.map σ) (γ * s) : ℝ) ^ A := by
    exact_mod_cast hCh s hs γ hγ
  have h5 : (ht h : ℝ) ^ N ≤ (Ch : ℝ) ^ N * (height σ (c • G.W.J.map σ) (γ * s) : ℝ) ^ (A * N) := by
    rw [h3, pow_mul, ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) h4 N
  have hI0 : 0 ≤ I.toReal := ENNReal.toReal_nonneg
  calc ‖G.M.I om Φ h‖ ≤ (C₁ : ℝ) * (max C 0 * (ht h : ℝ) ^ N) * I.toReal := by rw [← h2]; exact h1
    _ ≤ (C₁ : ℝ) * (max C 0 * ((Ch : ℝ) ^ N * (height σ (c • G.W.J.map σ) (γ * s) : ℝ) ^ (A * N))) * I.toReal := by
        gcongr
    _ = _ := by ring

end GlobalTheory.ThKGrowthBd
