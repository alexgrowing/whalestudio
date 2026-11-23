import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingConfigurationLeviIntegralImports
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundDomLtTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LintegralSiegelConeInvModulusLtTopWeil
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LintegralFundamentalDomainLeOfMeetsOrbits
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaBasicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelSetWittFrameDomainStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittRankLeHermitianSignature

noncomputable section

open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped Classical

namespace GlobalTheory.WeilSeminorm

theorem cone_zero (F : Type) [Field F] [NumberField F] (n d : ℕ) (c : ℝ) :
    ∫⁻ t in GlobalTheory.SiegelSet.cone 0 c, ENNReal.ofReal (∏ i, t i ^ (Module.finrank ℚ F * d)) *
      ENNReal.ofReal ((GlobalTheory.SiegelSet.modulus F n t * ∏ i, t i)⁻¹) < ⊤ := by
  have e : ∀ t : Fin 0 → ℝ, ENNReal.ofReal (∏ i, t i ^ (Module.finrank ℚ F * d)) *
      ENNReal.ofReal ((GlobalTheory.SiegelSet.modulus F n t * ∏ i, t i)⁻¹) = 1 := fun t => by
    simp [GlobalTheory.SiegelSet.modulus]
  simp only [e, setLIntegral_const, one_mul]
  refine (measure_mono (Set.subset_univ _)).trans_lt ?_
  rw [MeasureTheory.volume_pi, Measure.pi_univ]
  simp

theorem thetaSum_finset_sum {F : Type} [Field F] [NumberField F] {κ ι : Type} [Fintype κ] (s : Finset ι)
    (f : ι → (κ → AF F) → ℂ) (hf : ∀ k ∈ s, f k ∈ schA F κ) :
    thetaSum F (∑ k ∈ s, f k) = ∑ k ∈ s, thetaSum F (f k) := by
  induction s using Finset.induction_on with
  | empty => simp [thetaSum]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      thetaSum_add F (hf a (Finset.mem_insert_self a s)) (Submodule.sum_mem _ fun k hk => hf k (Finset.mem_insert_of_mem hk)),
      ih fun k hk => hf k (Finset.mem_insert_of_mem hk)]

theorem lintegral_theta_pure_le (hKP : KP) (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E)
    (om : Rep σ X W) (r s r' s' : ℕ) (hP : IsPair B M χX χW om r s r' s')
    (hdim : d + 2 * min r s < 2 * n ∨ min r s = 0) (φ : (Fin n × Fin d → Af F) → ℂ) (hφ : φ ∈ SB _) (h : UA σ W.J) :
    ∃ (T : Finset (ℕ × ℕ)) (C : ℝ≥0∞), C ≠ ⊤ ∧ ∀ f : SInf F (Fin n × Fin d),
      ∫⁻ g in M.dom, ‖theta om (pureA F f φ) g h‖ₑ ∂M.μ ≤
        C * ENNReal.ofReal ((T.sup (schwartzSeminormFamily ℂ _ ℂ)) f) := by
  have hb := GlobalTheory.T.theta_basic_properties hKP.base F E σ B n d X W M χX χW om r s r' s' hP
  have hcm := hP.base.cm
  have hσ := GlobalTheory.SiegelSet.sigma_sigma hcm
  have hJ' : IsHermND σ ((1 : E) • X.J.map σ) := by
    rw [one_smul]; exact GlobalTheory.UnitaryVol.isHermND_map hσ hP.herm
  let e : UA σ X.J ≃* GAd σ ((1 : E) • X.J.map σ) :=
    MulEquiv.subgroupCongr (GlobalTheory.SiegelSet.ug_eq_hr (F := F) (J := X.J) hσ (one_ne_zero : (1 : E) ≠ 0))
  have he : Continuous e := continuous_subtype_val.subtype_mk _
  have he' : Continuous e.symm := continuous_subtype_val.subtype_mk _
  haveI : BorelSpace (UA σ X.J) := ⟨rfl⟩
  haveI : ContinuousMul (UA σ X.J) := ⟨by
    have h3 : (fun p : UA σ X.J × UA σ X.J => p.1 * p.2) = fun p => e.symm (e p.1 * e p.2) :=
      funext fun p => by rw [← map_mul, MulEquiv.symm_apply_apply]
    rw [h3]
    exact he'.comp ((he.comp continuous_fst).mul (he.comp continuous_snd))⟩
  haveI := hP.good.haar
  haveI := GlobalTheory.UnitaryVol.countable_ratU σ X.J
  haveI : MeasurableMul (UA σ X.J) :=
    ⟨fun g => (continuous_const.mul continuous_id).measurable, fun g => (continuous_id.mul continuous_const).measurable⟩
  have hH : (M.μ.map e).IsHaarMeasure := MulEquiv.isHaarMeasure_map M.μ e he he'
  obtain ⟨r₀, Xf, Yf, hW⟩ := GlobalTheory.SiegelSet.exists_isWittFrame hcm hJ'
  obtain ⟨hr₀, hs₀⟩ := GlobalTheory.WittFrameSig.wittFrame_le_signature F E σ B n X r s hP.base hP.herm r₀ Xf Yf hW
  obtain ⟨K, Ω, c, hK, hΩ, -, hc, -, hcl, hcov, ⟨C₀, hC₀, hconj⟩, hmeas, -, -⟩ :=
    hKP.siegelSetUnitary F E σ hcm n ((1 : E) • X.J.map σ) hJ' r₀ Xf Yf hW
  obtain ⟨-, C₁, hC₁⟩ := hmeas _ hH
  have hSm : MeasurableSet (GlobalTheory.SiegelSet.siegelSet σ ((1 : E) • X.J.map σ) Xf Yf Ω c K) := hcl.measurableSet
  have hS' : MeasurableSet (e ⁻¹' GlobalTheory.SiegelSet.siegelSet σ ((1 : E) • X.J.map σ) Xf Yf Ω c K) :=
    hSm.preimage he.measurable
  have hScov : ∀ g : UA σ X.J, ∃ γ ∈ ratU σ X.J,
      γ * g ∈ e ⁻¹' GlobalTheory.SiegelSet.siegelSet σ ((1 : E) • X.J.map σ) Xf Yf Ω c K := fun g => by
    obtain ⟨γ, hγ, s', hs', hgs⟩ := hcov (e g)
    obtain ⟨u, -, hu⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hγ)
    have hr : e.symm γ ∈ ratU σ X.J := Subgroup.mem_subgroupOf.2 ⟨u, hu⟩
    refine ⟨(e.symm γ)⁻¹, inv_mem hr, ?_⟩
    show e ((e.symm γ)⁻¹ * g) ∈ GlobalTheory.SiegelSet.siegelSet σ ((1 : E) • X.J.map σ) Xf Yf Ω c K
    rw [map_mul, map_inv, MulEquiv.apply_symm_apply, hgs, inv_mul_cancel_left]
    exact hs'
  have hI : ∫⁻ t in GlobalTheory.SiegelSet.cone r₀ c, ENNReal.ofReal (∏ i, t i ^ (Module.finrank ℚ F * d)) *
      ENNReal.ofReal ((GlobalTheory.SiegelSet.modulus F n t * ∏ i, t i)⁻¹) < ⊤ := by
    rcases Nat.eq_zero_or_pos r₀ with h0 | h0
    · subst h0
      exact cone_zero F n d c
    · exact GlobalTheory.SiegelSet.lintegral_cone_modulus_lt_top F n r₀ d hc (by omega)
  set I := ∫⁻ t in GlobalTheory.SiegelSet.cone r₀ c, ENNReal.ofReal (∏ i, t i ^ (Module.finrank ℚ F * d)) *
      ENNReal.ofReal ((GlobalTheory.SiegelSet.modulus F n t * ∏ i, t i)⁻¹) with hIdef
  have key : ∀ (θ0 : UA σ X.J → ℂ) (A : ℝ), Continuous θ0 → (∀ γ ∈ ratU σ X.J, ∀ g, θ0 (γ * g) = θ0 g) →
      (∀ p ∈ Ω, ∀ t ∈ GlobalTheory.SiegelSet.cone r₀ c, ∀ a, GlobalTheory.SiegelSet.IsTorusElt σ ((1 : E) • X.J.map σ) Xf Yf t a →
        ∀ k ∈ K, ‖θ0 (e.symm (p * a * k))‖ ≤ A * ∏ i, t i ^ (Module.finrank ℚ F * d)) →
      ∫⁻ g in M.dom, ‖θ0 g‖ₑ ∂M.μ ≤ C₁ * (ENNReal.ofReal (max A 0) * I) := by
    intro θ0 A hθc hθi hθb
    have hA : 0 ≤ max A 0 := le_max_right _ _
    have hle : ∫⁻ g in M.dom, ‖θ0 g‖ₑ ∂M.μ ≤ C₁ * (ENNReal.ofReal (max A 0) * I) := by
      calc ∫⁻ g in M.dom, ‖θ0 g‖ₑ ∂M.μ
          ≤ ∫⁻ g in e ⁻¹' GlobalTheory.SiegelSet.siegelSet σ ((1 : E) • X.J.map σ) Xf Yf Ω c K, ‖θ0 g‖ₑ ∂M.μ :=
            GlobalTheory.lintegral_fundamentalDomain_le_of_meets_orbits (ratU σ X.J) M.μ hP.good.dom hS' hScov
              hθc.enorm.measurable (fun γ hγ g => by rw [hθi γ hγ g])
        _ = ∫⁻ x in GlobalTheory.SiegelSet.siegelSet σ ((1 : E) • X.J.map σ) Xf Yf Ω c K, ‖θ0 (e.symm x)‖ₑ ∂(M.μ.map e) := by
            rw [setLIntegral_map (f := fun x => ‖θ0 (e.symm x)‖ₑ) hSm (hθc.comp he').enorm.measurable he.measurable]
            simp only [MulEquiv.symm_apply_apply]
        _ ≤ C₁ * ∫⁻ t in GlobalTheory.SiegelSet.cone r₀ c, ENNReal.ofReal (max A 0 * ∏ i, t i ^ (Module.finrank ℚ F * d)) *
              ENNReal.ofReal ((GlobalTheory.SiegelSet.modulus F n t * ∏ i, t i)⁻¹) := by
            refine hC₁ (fun x => ‖θ0 (e.symm x)‖ₑ) _ (by fun_prop) fun q hq t ht a ha k hk => ?_
            have ht0 : ∀ i, 0 < t i := ht.1
            have hP0 : 0 ≤ ∏ i, t i ^ (Module.finrank ℚ F * d) :=
              Finset.prod_nonneg fun i _ => pow_nonneg (ht0 i).le _
            rw [← ofReal_norm_eq_enorm]
            exact ENNReal.ofReal_le_ofReal
              ((hθb q hq t ht a ha k hk).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hP0))
        _ = C₁ * (ENNReal.ofReal (max A 0) * I) := by
            rw [hIdef, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
            congr 1
            exact lintegral_congr fun t => by rw [ENNReal.ofReal_mul hA, mul_assoc]
    exact hle
  have contθ : ∀ Φ ∈ schA F (Fin n × Fin d), Continuous fun g => theta om Φ g h := fun Φ hΦ =>
    (hb.1 Φ hΦ).1.comp (continuous_id.prodMk continuous_const)
  have invθ : ∀ Φ ∈ schA F (Fin n × Fin d), ∀ γ ∈ ratU σ X.J, ∀ g, theta om Φ (γ * g) h = theta om Φ g h :=
    fun Φ hΦ γ hγ g => by
      have := (hb.1 Φ hΦ).2.1 γ hγ 1 (one_mem _) g h
      rwa [one_mul] at this
  obtain ⟨N, C, T, hT⟩ :=
    GlobalTheory.T.siegel_set_witt_frame_domain F E σ B n d X W M χX χW om r s r' s' hP r₀ Xf Yf hW Ω C₀ K c hΩ hC₀ hK hc hconj φ hφ
  have memA : ∀ f : SInf F (Fin n × Fin d), pureA F f φ ∈ schA F (Fin n × Fin d) := fun f =>
    Submodule.subset_span ⟨f, φ, hφ, rfl⟩
  have hH : (0 : ℝ) ≤ (ht h : ℝ) ^ N := by positivity
  refine ⟨T, C₁ * (ENNReal.ofReal (max C 0 * (ht h : ℝ) ^ N) * I), ?_, fun f => ?_⟩
  · have := hI.ne
    finiteness
  have hq : 0 ≤ (T.sup (schwartzSeminormFamily ℂ _ ℂ)) f := apply_nonneg _ _
  refine (key (fun g => theta om (pureA F f φ) g h)
      (C * (T.sup (schwartzSeminormFamily ℂ _ ℂ)) f * (ht h : ℝ) ^ N) (contθ _ (memA f)) (invθ _ (memA f))
      (fun p hp t htc a ha k hk => hT f h _ p hp t htc a ha k hk rfl)).trans (le_of_eq ?_)
  have e1 : max (C * (T.sup (schwartzSeminormFamily ℂ _ ℂ)) f * (ht h : ℝ) ^ N) 0 =
      (max C 0 * (ht h : ℝ) ^ N) * (T.sup (schwartzSeminormFamily ℂ _ ℂ)) f := by
    rw [show C * (T.sup (schwartzSeminormFamily ℂ _ ℂ)) f * (ht h : ℝ) ^ N =
      C * ((T.sup (schwartzSeminormFamily ℂ _ ℂ)) f * (ht h : ℝ) ^ N) by ring,
      ← zero_mul ((T.sup (schwartzSeminormFamily ℂ _ ℂ)) f * (ht h : ℝ) ^ N),
      ← max_mul_of_nonneg _ _ (mul_nonneg hq hH)]
    ring_nf
  rw [e1, ENNReal.ofReal_mul (mul_nonneg (le_max_right _ _) hH)]
  ring

theorem lintegral_thetaSum_le (hKP : KP) (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G₁ : Geo σ b a') (X : Chars F E) (om₁ : Rep σ G₁.V G₁.W)
    (om₁' : Rep σ G₁.V' G₁.W) (hT : IsTriple B G₁ X om₁ om₁') (m : ℕ) (φ : Fin m → (Fin b × Fin (b + a') → Af F) → ℂ)
    (hφ : ∀ j, φ j ∈ SB _) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ENNReal), C ≠ ⊤ ∧ ∀ f : Fin m → SInf F (Fin b × Fin (b + a')),
      ∫⁻ g₀ in G₁.M.dom, ‖thetaSum F (om₁ (g₀, 1) (∑ j, pureA F (f j) (φ j)))‖ₑ ∂G₁.M.μ ≤
        C * ∑ j, ENNReal.ofReal ((s.sup (schwartzSeminormFamily ℂ _ ℂ)) (f j)) := by
  have hP := GlobalTheory.ThK.Inhab.pairV hT
  have hdim : (b + a') + 2 * min (b - G₁.p) G₁.p < 2 * b ∨ min (b - G₁.p) G₁.p = 0 := by
    have h1 := hT.geo.eBig
    have h2 := hT.geo.lt
    omega
  choose T C hC hb using fun j => lintegral_theta_pure_le hKP F E σ B _ _ _ _ G₁.M _ _ om₁ _ _ _ _ hP hdim (φ j) (hφ j) 1
  have hbas := GlobalTheory.T.theta_basic_properties hKP.base F E σ B _ _ _ _ G₁.M _ _ om₁ _ _ _ _ hP
  haveI : BorelSpace (UA σ G₁.V.J) := ⟨rfl⟩
  refine ⟨Finset.univ.biUnion T, ∑ j, C j, ENNReal.sum_ne_top.2 fun j _ => hC j, fun f => ?_⟩
  have memA : ∀ j, pureA F (f j) (φ j) ∈ schA F (Fin b × Fin (b + a')) := fun j =>
    Submodule.subset_span ⟨f j, φ j, hφ j, rfl⟩
  have pres : ∀ x, ∀ Φ ∈ schA F (Fin b × Fin (b + a')), om₁ x Φ ∈ schA F (Fin b × Fin (b + a')) := fun x Φ hΦ =>
    (IsUWeilPair.isUSplitting hP.weil).pres x Φ hΦ
  have cont : ∀ j, Continuous fun g => theta om₁ (pureA F (f j) (φ j)) g 1 := fun j =>
    (hbas.1 _ (memA j)).1.comp (continuous_id.prodMk continuous_const)
  calc ∫⁻ g₀ in G₁.M.dom, ‖thetaSum F (om₁ (g₀, 1) (∑ j, pureA F (f j) (φ j)))‖ₑ ∂G₁.M.μ
      ≤ ∫⁻ g₀ in G₁.M.dom, ∑ j, ‖theta om₁ (pureA F (f j) (φ j)) g₀ 1‖ₑ ∂G₁.M.μ := by
        refine lintegral_mono fun g₀ => ?_
        rw [map_sum, thetaSum_finset_sum _ _ fun j _ => pres _ _ (memA j)]
        exact enorm_sum_le _ _
    _ = ∑ j, ∫⁻ g₀ in G₁.M.dom, ‖theta om₁ (pureA F (f j) (φ j)) g₀ 1‖ₑ ∂G₁.M.μ :=
        lintegral_finset_sum _ fun j _ => (cont j).enorm.measurable
    _ ≤ ∑ j, (∑ i, C i) * ENNReal.ofReal (((Finset.univ.biUnion T).sup (schwartzSeminormFamily ℂ _ ℂ)) (f j)) := by
        refine Finset.sum_le_sum fun j _ => (hb j (f j)).trans (mul_le_mul' ?_ (ENNReal.ofReal_le_ofReal ?_))
        · exact Finset.single_le_sum (f := C) (fun _ _ => zero_le) (Finset.mem_univ j)
        · exact Seminorm.le_def.1 (Finset.sup_mono (Finset.subset_biUnion_of_mem T (Finset.mem_univ j))) (f j)
    _ = _ := by rw [Finset.mul_sum]

end GlobalTheory.WeilSeminorm

end
