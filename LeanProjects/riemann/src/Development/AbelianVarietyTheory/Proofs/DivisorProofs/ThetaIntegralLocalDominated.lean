import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaBasicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundDomLtTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LintegralSiegelConeInvModulusLtTopWeil
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LintegralFundamentalDomainLeOfMeetsOrbits
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelSetWittFrameDomainStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittRankLeHermitianSignatureStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilConvergenceOfKernel

noncomputable section

open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.ThetaDom

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem pairV {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {Y : Chars F E} {om : Rep σ G.V G.W}
    {om' : Rep σ G.V' G.W} (hT : IsTriple B G Y om om') :
    IsPair B G.M Y.β (Y.β / Y.α) om (a - G.p) G.p (a + a' - (G.p + G.q)) (G.p + G.q) where
  base := hT.base
  herm := hT.geo.hV
  skew := hT.geo.hW
  good := hT.geo.hM
  hX := hT.chars.heckeβ
  hW := by
    refine ⟨?_, fun x => ?_⟩
    · exact hT.chars.heckeβ.1.div' hT.chars.heckeα.1
    · rw [MonoidHom.div_apply, hT.chars.heckeβ.2 x, hT.chars.heckeα.2 x, div_one]
  resX := hT.chars.resβ
  weil := hT.weil
  resW := fun u => by
    rw [MonoidHom.div_apply, Circle.coe_div, hT.chars.resβ u, hT.chars.resα u]
    split_ifs
    · simp
    · rw [div_eq_mul_inv, ← inv_pow, inv_neg_one, pow_add]

end GlobalTheory.ThetaDom

open GlobalTheory.ThetaDom in
open scoped Classical in

theorem GlobalTheory.ThetaDom.theta_dominated : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    IsTriple B G X om om' → ∀ Φ ∈ schA F (Fin a × Fin (a + a')), ∀ h₀ : UA σ G.W.J, ∃ U ∈ 𝓝 h₀, ∃ bound : UA σ G.V.J → ℝ,
      IntegrableOn bound G.M.dom G.M.μ ∧ ∀ h ∈ U, ∀ᵐ g ∂(G.M.μ.restrict G.M.dom), ‖theta om Φ g h‖ ≤ bound g := by
  intro hKP F E _ _ _ _ _ σ B a a' G Y om om' hT Φ hΦ h₀
  have hP := pairV hT
  have hb := GlobalTheory.T.theta_basic_properties hKP.base F E σ B a (a + a') G.V G.W G.M Y.β (Y.β / Y.α) om _ _ _ _ hP
  have hcm := hP.base.cm
  have hσ := GlobalTheory.SiegelSet.sigma_sigma hcm
  have hJ' : IsHermND σ ((1 : E) • G.V.J.map σ) := by
    rw [one_smul]; exact GlobalTheory.UnitaryVol.isHermND_map hσ hP.herm
  let e : UA σ G.V.J ≃* GAd σ ((1 : E) • G.V.J.map σ) :=
    MulEquiv.subgroupCongr (GlobalTheory.SiegelSet.ug_eq_hr (F := F) (J := G.V.J) hσ (one_ne_zero : (1 : E) ≠ 0))
  have he : Continuous e := continuous_subtype_val.subtype_mk _
  have he' : Continuous e.symm := continuous_subtype_val.subtype_mk _
  haveI : BorelSpace (UA σ G.V.J) := ⟨rfl⟩
  haveI : ContinuousMul (UA σ G.V.J) := ⟨by
    have h3 : (fun p : UA σ G.V.J × UA σ G.V.J => p.1 * p.2) = fun p => e.symm (e p.1 * e p.2) :=
      funext fun p => by rw [← map_mul, MulEquiv.symm_apply_apply]
    rw [h3]
    exact he'.comp ((he.comp continuous_fst).mul (he.comp continuous_snd))⟩
  haveI := hP.good.haar
  haveI := GlobalTheory.UnitaryVol.countable_ratU σ G.V.J
  haveI : MeasurableMul (UA σ G.V.J) :=
    ⟨fun g => (continuous_const.mul continuous_id).measurable, fun g => (continuous_id.mul continuous_const).measurable⟩
  have hH : (G.M.μ.map e).IsHaarMeasure := MulEquiv.isHaarMeasure_map G.M.μ e he he'
  obtain ⟨r₀, Xf, Yf, hW⟩ := GlobalTheory.SiegelSet.exists_isWittFrame hcm hJ'
  obtain ⟨-, hs₀⟩ := GlobalTheory.T.witt_rank_le_hermitian_signature F E σ B a G.V (a - G.p) G.p hP.base hP.herm r₀ Xf Yf hW
  obtain ⟨K, Ω, c, hK, hΩ, -, hc, -, hcl, hcov, ⟨C₀, hC₀, hconj⟩, hmeas, -, -⟩ :=
    hKP.siegelSetUnitary F E σ hcm a ((1 : E) • G.V.J.map σ) hJ' r₀ Xf Yf hW
  obtain ⟨-, C₁, hC₁⟩ := hmeas _ hH
  have hSm : MeasurableSet (GlobalTheory.SiegelSet.siegelSet σ ((1 : E) • G.V.J.map σ) Xf Yf Ω c K) := hcl.measurableSet
  have hS' : MeasurableSet (e ⁻¹' GlobalTheory.SiegelSet.siegelSet σ ((1 : E) • G.V.J.map σ) Xf Yf Ω c K) :=
    hSm.preimage he.measurable
  have hScov : ∀ g : UA σ G.V.J, ∃ γ ∈ ratU σ G.V.J,
      γ * g ∈ e ⁻¹' GlobalTheory.SiegelSet.siegelSet σ ((1 : E) • G.V.J.map σ) Xf Yf Ω c K := fun g => by
    obtain ⟨γ, hγ, s', hs', hgs⟩ := hcov (e g)
    obtain ⟨u, -, hu⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hγ)
    have hr : e.symm γ ∈ ratU σ G.V.J := Subgroup.mem_subgroupOf.2 ⟨u, hu⟩
    refine ⟨(e.symm γ)⁻¹, inv_mem hr, ?_⟩
    show e ((e.symm γ)⁻¹ * g) ∈ GlobalTheory.SiegelSet.siegelSet σ ((1 : E) • G.V.J.map σ) Xf Yf Ω c K
    rw [map_mul, map_inv, MulEquiv.apply_symm_apply, hgs, inv_mul_cancel_left]
    exact hs'
  have hI : ∫⁻ t in GlobalTheory.SiegelSet.cone r₀ c, ENNReal.ofReal (∏ i, t i ^ (Module.finrank ℚ F * (a + a'))) *
      ENNReal.ofReal ((GlobalTheory.SiegelSet.modulus F a t * ∏ i, t i)⁻¹) < ⊤ := by
    have h1 := hT.geo.eBig
    exact GlobalTheory.SiegelSet.lintegral_cone_modulus_lt_top F a r₀ (a + a') hc (by omega)
  set I := ∫⁻ t in GlobalTheory.SiegelSet.cone r₀ c, ENNReal.ofReal (∏ i, t i ^ (Module.finrank ℚ F * (a + a'))) *
      ENNReal.ofReal ((GlobalTheory.SiegelSet.modulus F a t * ∏ i, t i)⁻¹) with hIdef

  have pres : ∀ x, ∀ Φ ∈ schA F (Fin a × Fin (a + a')), om x Φ ∈ schA F (Fin a × Fin (a + a')) := fun x Φ hΦ =>
    (IsUWeilPair.isUSplitting hP.weil).pres x Φ hΦ
  have thAdd : ∀ Φ ∈ schA F (Fin a × Fin (a + a')), ∀ Ψ ∈ schA F (Fin a × Fin (a + a')), ∀ g h,
      theta om (Φ + Ψ) g h = theta om Φ g h + theta om Ψ g h := fun Φ hΦ Ψ hΨ g h => by
    simp only [theta, map_add]
    exact thetaSum_add F (pres _ Φ hΦ) (pres _ Ψ hΨ)
  have thSmul : ∀ (z : ℂ) Φ g h, theta om (z • Φ) g h = z * theta om Φ g h := fun z Φ g h => by
    simp only [theta, map_smul]
    exact thetaSum_smul F z _
  have hPr : ∀ t ∈ GlobalTheory.SiegelSet.cone r₀ c, 0 ≤ ∏ i, t i ^ (Module.finrank ℚ F * (a + a')) := fun t ht =>
    Finset.prod_nonneg fun i _ => pow_nonneg (ht.1 i).le _
  have boundA : ∀ Φ ∈ schA F (Fin a × Fin (a + a')), ∃ (N : ℕ) (C : ℝ), ∀ h, ∀ p ∈ Ω, ∀ t ∈ GlobalTheory.SiegelSet.cone r₀ c, ∀ a₀,
      GlobalTheory.SiegelSet.IsTorusElt σ ((1 : E) • G.V.J.map σ) Xf Yf t a₀ → ∀ k ∈ K,
      ‖theta om Φ (e.symm (p * a₀ * k)) h‖ ≤ C * (ht h : ℝ) ^ N * ∏ i, t i ^ (Module.finrank ℚ F * (a + a')) := by
    intro Φ hΦ
    induction hΦ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨f, g, hg, rfl⟩ := hx
      obtain ⟨N, C, T, hT⟩ := GlobalTheory.T.siegel_set_witt_frame_domain F E σ B a (a + a') G.V G.W G.M Y.β (Y.β / Y.α) om _ _ _ _ hP r₀ Xf Yf hW
        Ω C₀ K c hΩ hC₀ hK hc hconj g hg
      exact ⟨N, C * (T.sup (schwartzSeminormFamily ℂ _ ℂ)) f, fun h p hp t htc a₀ ha k hk =>
        hT f h _ p hp t htc a₀ ha k hk rfl⟩
    | zero => exact ⟨0, 0, fun h p _ t _ a₀ _ k _ => by simp [theta, thetaSum]⟩
    | add x y hx hy ihx ihy =>
      obtain ⟨N₁, C₁', h₁⟩ := ihx
      obtain ⟨N₂, C₂', h₂⟩ := ihy
      refine ⟨max N₁ N₂, max C₁' 0 + max C₂' 0, fun h p hp t htc a₀ ha k hk => ?_⟩
      have e1 : (1 : ℝ) ≤ ht h := GlobalTheory.ThKWeil.one_le_ht h
      have a1 : (ht h : ℝ) ^ N₁ ≤ (ht h : ℝ) ^ max N₁ N₂ := pow_le_pow_right₀ e1 (le_max_left _ _)
      have a2 : (ht h : ℝ) ^ N₂ ≤ (ht h : ℝ) ^ max N₁ N₂ := pow_le_pow_right₀ e1 (le_max_right _ _)
      have b1 := GlobalTheory.ThKWeil.mul_le_max_mul (C := C₁') (by positivity) a1 (hPr t htc)
      have b2 := GlobalTheory.ThKWeil.mul_le_max_mul (C := C₂') (by positivity) a2 (hPr t htc)
      rw [thAdd x hx y hy]
      calc _ ≤ ‖theta om x (e.symm (p * a₀ * k)) h‖ + ‖theta om y (e.symm (p * a₀ * k)) h‖ := norm_add_le _ _
        _ ≤ _ := add_le_add ((h₁ h p hp t htc a₀ ha k hk).trans b1) ((h₂ h p hp t htc a₀ ha k hk).trans b2)
        _ = _ := by ring
    | smul z x hx ih =>
      obtain ⟨N, C, h₁⟩ := ih
      refine ⟨N, ‖z‖ * C, fun h p hp t htc a₀ ha k hk => ?_⟩
      rw [thSmul, norm_mul]
      calc ‖z‖ * ‖theta om x (e.symm (p * a₀ * k)) h‖
          ≤ ‖z‖ * (C * (ht h : ℝ) ^ N * ∏ i, t i ^ (Module.finrank ℚ F * (a + a'))) :=
            mul_le_mul_of_nonneg_left (h₁ h p hp t htc a₀ ha k hk) (norm_nonneg _)
        _ = _ := by ring
  obtain ⟨N, C, hC⟩ := boundA Φ hΦ

  set H : ℝ := (ht h₀ : ℝ) + 1 with hHdef
  have hcht : Continuous fun h : UA σ G.W.J => (ht h : ℝ) :=
    NNReal.continuous_coe.comp ((GlobalTheory.Grow.continuous_heightGL F).comp continuous_subtype_val)
  set U : Set (UA σ G.W.J) := {h | (ht h : ℝ) < H} with hUdef
  have hU : U ∈ 𝓝 h₀ := (isOpen_lt hcht continuous_const).mem_nhds (by simp [hUdef, hHdef])

  set bE : UA σ G.V.J → ℝ≥0∞ := fun g => ⨆ h ∈ U, ‖theta om Φ g h‖ₑ with hbEdef
  have contθ : ∀ h, Continuous fun g => theta om Φ g h := fun h =>
    (hb.1 Φ hΦ).1.comp (continuous_id.prodMk continuous_const)
  have hbm : Measurable bE := by
    refine LowerSemicontinuous.measurable ?_
    exact lowerSemicontinuous_iSup fun h => lowerSemicontinuous_iSup fun _ => (contθ h).enorm.lowerSemicontinuous
  have hbi : ∀ γ ∈ ratU σ G.V.J, ∀ g, bE (γ * g) = bE g := fun γ hγ g => by
    simp only [hbEdef]
    refine iSup_congr fun h => iSup_congr fun _ => ?_
    have := (hb.1 Φ hΦ).2.1 γ hγ 1 (one_mem _) g h
    rw [one_mul] at this
    rw [this]
  have hA : 0 ≤ max C 0 * H ^ N := by
    have : (0 : ℝ) ≤ H := by positivity
    positivity
  have hbS : ∀ p ∈ Ω, ∀ t ∈ GlobalTheory.SiegelSet.cone r₀ c, ∀ a₀, GlobalTheory.SiegelSet.IsTorusElt σ ((1 : E) • G.V.J.map σ) Xf Yf t a₀ →
      ∀ k ∈ K, bE (e.symm (p * a₀ * k)) ≤ ENNReal.ofReal (max C 0 * H ^ N * ∏ i, t i ^ (Module.finrank ℚ F * (a + a'))) := by
    intro p hp t htc a₀ ha k hk
    refine iSup₂_le fun h hh => ?_
    rw [← ofReal_norm]
    refine ENNReal.ofReal_le_ofReal ((hC h p hp t htc a₀ ha k hk).trans ?_)
    have h0 : (0 : ℝ) ≤ (ht h : ℝ) ^ N := by positivity
    have h1 : (ht h : ℝ) ^ N ≤ H ^ N := pow_le_pow_left₀ (by positivity) (le_of_lt hh) N
    exact GlobalTheory.ThKWeil.mul_le_max_mul h0 h1 (hPr t htc)
  have hle : ∫⁻ g in G.M.dom, bE g ∂G.M.μ ≤ C₁ * (ENNReal.ofReal (max C 0 * H ^ N) * I) := by
    calc ∫⁻ g in G.M.dom, bE g ∂G.M.μ
        ≤ ∫⁻ g in e ⁻¹' GlobalTheory.SiegelSet.siegelSet σ ((1 : E) • G.V.J.map σ) Xf Yf Ω c K, bE g ∂G.M.μ :=
          GlobalTheory.lintegral_fundamentalDomain_le_of_meets_orbits (ratU σ G.V.J) G.M.μ hP.good.dom hS' hScov hbm hbi
      _ = ∫⁻ x in GlobalTheory.SiegelSet.siegelSet σ ((1 : E) • G.V.J.map σ) Xf Yf Ω c K, bE (e.symm x) ∂(G.M.μ.map e) := by
          rw [setLIntegral_map (f := fun x => bE (e.symm x)) hSm (hbm.comp he'.measurable) he.measurable]
          simp only [MulEquiv.symm_apply_apply]
      _ ≤ C₁ * ∫⁻ t in GlobalTheory.SiegelSet.cone r₀ c,
            ENNReal.ofReal (max C 0 * H ^ N * ∏ i, t i ^ (Module.finrank ℚ F * (a + a'))) *
            ENNReal.ofReal ((GlobalTheory.SiegelSet.modulus F a t * ∏ i, t i)⁻¹) :=
          hC₁ (fun x => bE (e.symm x)) _ (by fun_prop) fun q hq t ht a₀ ha k hk => hbS q hq t ht a₀ ha k hk
      _ = C₁ * (ENNReal.ofReal (max C 0 * H ^ N) * I) := by
          rw [hIdef, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          congr 1
          exact lintegral_congr fun t => by rw [ENNReal.ofReal_mul hA, mul_assoc]
  have hfin : ∫⁻ g in G.M.dom, bE g ∂G.M.μ < ⊤ :=
    hle.trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hI))
  refine ⟨U, hU, fun g => (bE g).toReal, ⟨hbm.ennreal_toReal.aestronglyMeasurable, ?_⟩, fun h hh => ?_⟩
  · refine lt_of_le_of_lt (lintegral_mono fun g => ?_) hfin
    rw [Real.enorm_eq_ofReal ENNReal.toReal_nonneg]
    exact ENNReal.ofReal_toReal_le
  · filter_upwards [ae_lt_top hbm hfin.ne] with g hg
    have h1 : ‖theta om Φ g h‖ₑ ≤ bE g := le_iSup₂ (f := fun h _ => ‖theta om Φ g h‖ₑ) h hh
    calc ‖theta om Φ g h‖ = (‖theta om Φ g h‖ₑ).toReal := (toReal_enorm _).symm
      _ ≤ (bE g).toReal := ENNReal.toReal_mono hg.ne h1
