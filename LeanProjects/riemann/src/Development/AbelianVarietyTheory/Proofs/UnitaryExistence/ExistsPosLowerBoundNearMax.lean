import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspidalExponentialDecay
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.PeriodicSchwarzLemma
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MaximumBoundField

open NumberField Complex Filter ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate Topology Real

namespace GlobalTheory

namespace HalfMax

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem c_pos' (X : Data E r) (τ : X.Ψ) : 0 < X.c τ := by
  have h : τ.1 X.ξ0 ≠ 0 := (map_ne_zero τ.1).2 X.ξ0_ne
  have := norm_pos_iff.2 h
  simp only [Data.c]
  positivity

theorem exists_herm_eq_zero (X : Data E r) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ X.dom, ∀ v ∈ X.Λ,
      (∀ τ : X.Ψ, X.c τ * X.maj z τ (Data.emb τ.1 v) < δ) → herm X.Gm v v = 0 := by
  set S : ℝ := ∑ τ : X.Ψ, ‖τ.1 (X.den : E)‖ / X.c τ with hS
  have hterm : ∀ τ : X.Ψ, 0 ≤ ‖τ.1 (X.den : E)‖ / X.c τ := fun τ =>
    div_nonneg (norm_nonneg _) (c_pos' X τ).le
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun τ _ => hterm τ
  refine ⟨1 / (1 + S), by positivity, fun z hz v hv hsmall => ?_⟩
  have hden : (X.den : E) ≠ 0 := by exact_mod_cast X.den_ne
  refine (mul_eq_zero.1 (UnipotentCoefficientShift.eq_zero_of_conj_lt_one (X.Λ_int v hv v hv) ?_)).resolve_left hden
  intro σ
  have key : ∀ τ : X.Ψ, ‖τ.1 ((X.den : E) * herm X.Gm v v)‖ < 1 := fun τ => by
    have hc := c_pos' X τ
    have h1 : ‖τ.1 (herm X.Gm v v)‖ ≤ X.maj z τ (Data.emb τ.1 v) := by
      rw [← EmbeddingHermitianPairs.hermC_emb]
      exact UnipotentCoefficientShift.norm_hermC_le_maj hz τ (Data.emb τ.1 v)
    have h2 : ‖τ.1 (X.den : E)‖ / X.c τ ≤ S :=
      Finset.single_le_sum (f := fun τ : X.Ψ => ‖τ.1 (X.den : E)‖ / X.c τ)
        (fun σ _ => hterm σ) (Finset.mem_univ τ)
    have h3 := hsmall τ
    have h4 : X.c τ * ‖τ.1 (herm X.Gm v v)‖ ≤ 1 / (1 + S) :=
      (mul_le_mul_of_nonneg_left h1 hc.le).trans h3.le
    rw [map_mul, norm_mul]
    calc ‖τ.1 (X.den : E)‖ * ‖τ.1 (herm X.Gm v v)‖
        = (‖τ.1 (X.den : E)‖ / X.c τ) * (X.c τ * ‖τ.1 (herm X.Gm v v)‖) := by field_simp
      _ ≤ S * (1 / (1 + S)) := mul_le_mul h2 h4 (by positivity) hS0
      _ < 1 := by
        rw [mul_one_div, div_lt_one (by positivity)]
        linarith
  by_cases hσ : σ ∈ X.Ψ
  · exact key ⟨σ, hσ⟩
  · have hc : NumberField.ComplexEmbedding.conjugate σ ∈ X.Ψ := by
      rw [X.cmType, NumberField.ComplexEmbedding.involutive_conjugate E σ]
      exact hσ
    have := key ⟨_, hc⟩
    simpa [NumberField.ComplexEmbedding.conjugate_coe_eq] using this

theorem term_norm_one {ι : Type*} [Fintype ι] (c : ℂ) (ν : ι → ℝ) (ζ : ℂ) :
    ‖c * cexp (4 * π * I * ∑ τ, (ν τ : ℂ) * ζ)‖ = ‖c‖ * Real.exp (-(4 * π * (∑ τ, ν τ) * ζ.im)) := by
  have h := flowTermNormDecay.term_norm c ν ζ 1
  simpa only [Nat.cast_one, one_pow, div_one] using h

theorem tendsto_zero (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (hP : P ∈ X.SS la)
    {z0 : Frame X.Ψ r} (hz0 : z0 ∈ X.dom) {v : Fin r → E} (hξ : X.IsIso v)
    (hdom : ∀ ζ : ℂ, 0 ≤ ζ.im → X.flow v (fun _ => ζ) z0 ∈ X.dom) (G : ℂ → ℂ)
    (hG : ∀ ζ : ℂ, 0 < ζ.im → G ζ = P (X.flow v (fun _ => ζ) z0)) :
    Tendsto G (comap im atTop) (𝓝 0) := by
  classical
  set a : (X.Ψ → ℝ) → ℂ := fun ν => X.fj la v ν P z0 with ha
  have hexp : ∀ ζ : ℂ, 0 ≤ ζ.im → HasSum (fun ν : X.Ψ → ℝ =>
      a ν * cexp (4 * π * I * ∑ τ, (ν τ : ℂ) * ζ)) (P (X.flow v (fun _ => ζ) z0)) :=
    fun ζ hζ => m3bExp_holds r X la P hP.1.1 v hξ z0 hz0 (fun _ => ζ) (hdom ζ hζ)
  obtain ⟨C, hC⟩ := hP.1.2
  have hpos := (moderateCoefficientPositivity_holds r X la P C 0 hP.1.1 (fun x hx => by simpa using hC x hx)).1
  have ha0 : a 0 = 0 := hP.2 v hξ z0 hz0
  have hS : ∀ ν, a ν ≠ 0 → 0 < ∑ τ, ν τ := by
    intro ν hν
    have hnn : ∀ τ, 0 ≤ ν τ := hpos v hξ ν z0 hz0 hν
    have hne : ν ≠ 0 := by
      rintro rfl
      exact hν ha0
    obtain ⟨τ, hτ⟩ : ∃ τ, ν τ ≠ 0 := by
      by_contra h
      push Not at h
      exact hne (funext h)
    exact Finset.sum_pos' (fun τ _ => hnn τ)
      ⟨τ, Finset.mem_univ _, lt_of_le_of_ne (hnn τ) (Ne.symm hτ)⟩
  have hsum : Summable fun ν => ‖a ν‖ := by
    have h0 := (hexp 0 (le_refl _)).summable
    simp only [mul_zero, Finset.sum_const_zero, Complex.exp_zero, mul_one] at h0
    exact summable_norm_iff.2 h0
  have hab : ∀ ν : X.Ψ → ℝ, Tendsto (fun ζ : ℂ =>
      a ν * cexp (4 * π * I * ∑ τ, (ν τ : ℂ) * ζ)) (comap im atTop) (𝓝 0) := by
    intro ν
    by_cases hν : a ν = 0
    · simp only [hν, zero_mul]
      exact tendsto_const_nhds
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simp only [term_norm_one]
    have hk : 0 < 4 * π * (∑ τ, ν τ) := by
      have := hS ν hν
      positivity
    have h1 : Tendsto (fun ζ : ℂ => ζ.im) (comap im atTop) atTop := tendsto_comap
    have h2 := Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp (h1.const_mul_atTop hk))
    have h3 := h2.const_mul ‖a ν‖
    simpa using h3
  have hbound : ∀ᶠ ζ in comap im atTop, ∀ ν : X.Ψ → ℝ,
      ‖a ν * cexp (4 * π * I * ∑ τ, (ν τ : ℂ) * ζ)‖ ≤ ‖a ν‖ := by
    have hev : ∀ᶠ ζ in comap im atTop, (0 : ℝ) ≤ ζ.im :=
      tendsto_comap.eventually (eventually_ge_atTop 0)
    filter_upwards [hev] with ζ hζ ν
    rw [term_norm_one]
    by_cases hν : a ν = 0
    · simp [hν]
    have hk : 0 ≤ 4 * π * (∑ τ, ν τ) := by
      have := hS ν hν
      positivity
    refine mul_le_of_le_one_right (norm_nonneg _) (Real.exp_le_one_iff.2 ?_)
    have := mul_nonneg hk hζ
    linarith
  have hT := tendsto_tsum_of_dominated_convergence hsum hab hbound
  simp only [tsum_zero] at hT
  refine hT.congr' ?_
  have hev : ∀ᶠ ζ in comap im atTop, (0 : ℝ) < ζ.im :=
    tendsto_comap.eventually (eventually_gt_atTop 0)
  filter_upwards [hev] with ζ hζ
  rw [hG ζ hζ]
  exact (hexp ζ hζ.le).tsum_eq

theorem exists_period (X : Data E r) (la : Wt X.Ψ r) :
    ∃ M : ℝ, 0 < M ∧ ∀ v ∈ X.Λ, herm X.Gm v v = 0 →
      ∃ γ ∈ X.Γ, X.χ la γ = 1 ∧
        ∀ τ : X.Ψ, (γ : Matrix (Fin r) (Fin r) E).map τ.1 = X.flowMat v τ (M : ℂ) := by
  obtain ⟨n, hn, hχ⟩ := X.χ_fin la
  have h1 := X.m_pos
  refine ⟨((X.m * n : ℕ) : ℝ), by positivity, fun v hv hvv => ?_⟩
  obtain ⟨γ, hγ, hγm⟩ := X.transv v hv hvv 1 (map_one _) isIntegral_one
  refine ⟨γ ^ n, pow_mem hγ n, ?_, fun τ => ?_⟩
  · rw [TransvectionPeriodicity.chi_pow X la hγ, hχ γ hγ]
  · rw [Units.val_pow_eq_pow_val, hγm, TransvectionPeriodicity.transvMat_pow X.Gm hvv]
    refine TransvectionPeriodicity.transvMat_map X v τ _ _ ?_
    simp only [map_mul, map_one, map_natCast, TransvectionPeriodicity.emb_kappa]
    push_cast
    ring

theorem exists_le_maj_of_iso (X : Data E r) (la : Wt X.Ψ r) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ P ∈ X.SS la, ∀ z0 ∈ X.dom,
      (∀ x ∈ X.dom, X.pnorm la P x ≤ 2 * X.pnorm la P z0) → 0 < X.pnorm la P z0 →
      ∀ v, X.IsIso v → ∃ τ : X.Ψ, ε ≤ X.c τ * X.maj z0 τ (Data.emb τ.1 v) := by
  obtain ⟨M, hM, htrans⟩ := exists_period X la
  set w : ℝ := ∑ τ, X.spread la τ with hw
  have hw0 : 0 ≤ w := Finset.sum_nonneg fun τ _ => flowTermNormDecay.spread_nonneg' X la τ
  have hL : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hpi := Real.pi_pos
  set ε : ℝ := π / (M * (w + 2) * Real.log 2) with hε
  have hε0 : 0 < ε := by positivity
  refine ⟨ε, hε0, fun P hP z0 hz0 hhalf hpos v hξ => ?_⟩
  obtain ⟨hv, hvv, hv0⟩ := id hξ
  by_contra hcon
  push Not at hcon
  set e : X.Ψ → Fin r → ℂ := fun τ => Data.emb τ.1 v with he
  have he0 : ∀ τ : X.Ψ, e τ ≠ 0 := by
    intro τ h
    apply hv0
    funext a
    have := congr_fun h a
    simpa [e, Data.emb] using this
  have heIso : X.IsIsoV e := fun τ => ⟨by
    show hermC τ.1 X.Gm (fun a => τ.1 (v a)) (fun a => τ.1 (v a)) = 0
    rw [EmbeddingHermitianPairs.hermC_emb, hvv, map_zero], he0 τ⟩
  have hmaj : ∀ τ, 0 < X.maj z0 τ (e τ) := fun τ => X.maj_pos hz0 τ (he0 τ)
  set t : ℝ := 1 / (2 * ε) with ht
  have ht0 : 0 < t := by positivity
  have htt : ∀ τ, 2 * t < X.ttV e z0 τ := by
    intro τ
    simp only [Data.ttV]
    rw [show 2 * t = 1 / ε by rw [ht]; field_simp]
    exact one_div_lt_one_div_of_lt (mul_pos (c_pos' X τ) (hmaj τ)) (hcon τ)
  have hfl : ∀ s, X.flowV e s z0 = X.flow v s z0 := fun s => rfl
  have hdom : ∀ ζ : ℂ, -(2 * t) < ζ.im → X.flow v (fun _ => ζ) z0 ∈ X.dom := by
    intro ζ hζ
    rw [← hfl]
    refine ((flowDomainCriterion_holds r X e heIso z0 hz0 (fun _ => ζ)).1).2 (fun τ => ?_)
    show 0 < 1 + ζ.im / X.ttV e z0 τ
    have h := htt τ
    have hpos' : 0 < X.ttV e z0 τ := by linarith
    have : -1 < ζ.im / X.ttV e z0 τ := by rw [lt_div_iff₀ hpos']; linarith
    linarith
  set g : ℂ → ℂ := fun ζ => if -(2 * t) < ζ.im then P (X.flow v (fun _ => ζ) z0) else 0 with hg
  obtain ⟨γ, hγ, hχ, hγm⟩ := htrans v hv hvv
  have hper : Function.Periodic g M := by
    intro ζ
    simp only [hg, Complex.add_im, Complex.ofReal_im, add_zero]
    split_ifs with h
    · have hy := hdom ζ h
      have hlact : X.flow v (fun _ => ζ + (M : ℂ)) z0 = lact γ (X.flow v (fun _ => ζ) z0) := by
        funext τ
        show X.flowMat v τ (ζ + M) * mat z0 τ =
          (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat (X.flow v (fun _ => ζ) z0) τ
        rw [AdmissibleHermitianColumns.mat_flow, hγm τ, ← Matrix.mul_assoc,
          EmbeddingHermitianPairs.flowMat_mul X hvv, add_comm]
      rw [hlact, hP.1.1.2.2 γ hγ _ hy, hχ, one_mul]
    · rfl
  have hopen := FourierCoefficientDomain.isOpen_dom X
  have hdiff : ∀ ζ : ℂ, -(2 * t) < ζ.im → DifferentiableAt ℂ g ζ := by
    intro ζ hζ
    have hev : g =ᶠ[𝓝 ζ] fun ζ => P (X.flow v (fun _ => ζ) z0) := by
      have : {ζ : ℂ | -(2 * t) < ζ.im} ∈ 𝓝 ζ :=
        (isOpen_lt continuous_const Complex.continuous_im).mem_nhds hζ
      filter_upwards [this] with ζ' h'
      simp only [hg, if_pos (show -(2 * t) < ζ'.im from h')]
    refine DifferentiableAt.congr_of_eventuallyEq ?_ hev
    have hF : DifferentiableAt ℂ (fun ζ : ℂ => X.flow v (fun _ => ζ) z0) ζ :=
      ((FlowMeanContinuity.flow_differentiable X v z0).comp
        (differentiable_pi.2 fun _ => differentiable_id)) ζ
    exact (hP.1.1.1.differentiableAt (hopen.mem_nhds (hdom ζ hζ))).comp ζ hF
  have hzero : Tendsto g (comap im atTop) (𝓝 0) :=
    tendsto_zero X la P hP hz0 hξ
      (fun ζ hζ => hdom ζ (by linarith)) g
      (fun ζ hζ => by simp only [hg, if_pos (show -(2 * t) < ζ.im by linarith)])
  set B : ℝ := 2 * ‖P z0‖ * 2 ^ (w / 2) with hB
  have hBd : ∀ ζ : ℂ, ζ.im = -t → ‖g ζ‖ ≤ B := by
    intro ζ hζ
    have hlt : -(2 * t) < ζ.im := by linarith
    simp only [hg, if_pos hlt]
    set y := X.flow v (fun _ => ζ) z0 with hy
    have hyd := hdom ζ hlt
    have hnf : 0 < X.nfac la y := flowTermNormDecay.nfac_pos X la hyd
    have hratio : X.nfac la z0 / X.nfac la y ≤
        ∏ τ : X.Ψ, (max (1 + ζ.im / X.ttV e z0 τ) (1 + ζ.im / X.ttV e z0 τ)⁻¹) ^
          (X.spread la τ / 2) :=
      (m3bNorm_holds r X e heIso la z0 hz0 (fun _ => ζ) (by rw [hfl]; exact hyd)).2
    have hprod : ∏ τ : X.Ψ, (max (1 + ζ.im / X.ttV e z0 τ) (1 + ζ.im / X.ttV e z0 τ)⁻¹) ^
        (X.spread la τ / 2) ≤ (2 : ℝ) ^ (w / 2) := by
      have hterm : ∀ τ : X.Ψ, (max (1 + ζ.im / X.ttV e z0 τ) (1 + ζ.im / X.ttV e z0 τ)⁻¹) ^
          (X.spread la τ / 2) ≤ (2 : ℝ) ^ (X.spread la τ / 2) := by
        intro τ
        have h := htt τ
        have hT : 0 < X.ttV e z0 τ := by linarith
        have hq1 : 1 / 2 ≤ 1 + ζ.im / X.ttV e z0 τ := by
          rw [hζ, neg_div]
          have : t / X.ttV e z0 τ ≤ 1 / 2 := by rw [div_le_iff₀ hT]; linarith
          linarith
        have hq2 : 1 + ζ.im / X.ttV e z0 τ ≤ 1 := by
          rw [hζ, neg_div]
          have : 0 ≤ t / X.ttV e z0 τ := by positivity
          linarith
        have hqpos : 0 < 1 + ζ.im / X.ttV e z0 τ := by linarith
        have hinv : (1 + ζ.im / X.ttV e z0 τ)⁻¹ ≤ 2 := by
          rw [inv_le_comm₀ hqpos two_pos]
          linarith
        have hsp := flowTermNormDecay.spread_nonneg' X la τ
        exact Real.rpow_le_rpow (le_trans hqpos.le (le_max_left _ _))
          (max_le (by linarith) hinv) (by linarith)
      calc _ ≤ ∏ τ : X.Ψ, (2 : ℝ) ^ (X.spread la τ / 2) :=
            Finset.prod_le_prod (fun τ _ => Real.rpow_nonneg (le_trans (by
              have h := htt τ
              have hT : 0 < X.ttV e z0 τ := by linarith
              have : t / X.ttV e z0 τ ≤ 1 / 2 := by rw [div_le_iff₀ hT]; linarith
              rw [hζ, neg_div]
              linarith) (le_max_left _ _)) _) (fun τ _ => hterm τ)
        _ = (2 : ℝ) ^ (∑ τ : X.Ψ, X.spread la τ / 2) := (Real.rpow_sum_of_pos two_pos _ _).symm
        _ = (2 : ℝ) ^ (w / 2) := by rw [← Finset.sum_div]
    have h1 : ‖P y‖ * X.nfac la y ≤ 2 * (‖P z0‖ * X.nfac la z0) := hhalf y hyd
    have h2 : X.nfac la z0 ≤ 2 ^ (w / 2) * X.nfac la y := by
      rw [div_le_iff₀ hnf] at hratio
      exact hratio.trans (mul_le_mul_of_nonneg_right hprod hnf.le)
    have h3 : ‖P y‖ * X.nfac la y ≤ B * X.nfac la y := by
      calc ‖P y‖ * X.nfac la y ≤ 2 * (‖P z0‖ * X.nfac la z0) := h1
        _ ≤ 2 * (‖P z0‖ * (2 ^ (w / 2) * X.nfac la y)) := by gcongr
        _ = B * X.nfac la y := by rw [hB]; ring
    exact le_of_mul_le_mul_right h3 hnf
  have hsch := PeriodicSchwarzLemma.periodic_schwarz hM ht0 (show t < 2 * t by linarith) hper hdiff hzero hBd
  have hg0 : g 0 = P z0 := by
    simp only [hg, Complex.zero_im, if_pos (show -(2 * t) < (0 : ℝ) by linarith)]
    congr 1
    exact EmbeddingHermitianPairs.flow_zero X v z0
  rw [hg0] at hsch
  have hP0 : 0 < ‖P z0‖ := by
    have hpn : X.pnorm la P z0 = ‖P z0‖ * X.nfac la z0 := rfl
    rcases (norm_nonneg (P z0)).eq_or_lt with h | h
    · rw [hpn, ← h, zero_mul] at hpos
      exact absurd hpos (lt_irrefl 0)
    · exact h
  have h1 : 1 ≤ Real.exp (-2 * π * t / M) * (2 * 2 ^ (w / 2)) := by
    have e1 : Real.exp (-2 * π * t / M) * B =
        ‖P z0‖ * (Real.exp (-2 * π * t / M) * (2 * 2 ^ (w / 2))) := by rw [hB]; ring
    rw [e1] at hsch
    exact le_of_mul_le_mul_left (by rw [mul_one]; exact hsch) hP0
  have e3 : Real.exp ((1 + w / 2) * Real.log 2) = 2 * 2 ^ (w / 2) := by
    rw [show (1 + w / 2) * Real.log 2 = Real.log 2 + Real.log 2 * (w / 2) by ring, Real.exp_add,
      Real.exp_log two_pos, ← Real.rpow_def_of_pos two_pos]
  rw [← e3, ← Real.exp_add] at h1
  have h2 := Real.one_le_exp_iff.1 h1
  have h5 : -2 * π * t / M = -((w + 2) * Real.log 2) := by
    rw [ht, hε]
    field_simp
  rw [h5] at h2
  have h6 : 0 < (w + 2) * Real.log 2 := by positivity
  linarith

end HalfMax

theorem exists_lower_bound_half_max_norm (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ)
    (X : Data E r) (la : Wt X.Ψ r) (hr : 0 < r) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ P ∈ X.SS la, ∀ z ∈ X.dom,
      (∀ x ∈ X.dom, X.pnorm la P x ≤ 2 * X.pnorm la P z) → 0 < X.pnorm la P z → ε ≤ X.la1 z := by
  obtain ⟨δ, hδ, hiso⟩ := HalfMax.exists_herm_eq_zero X
  obtain ⟨ε, hε, hmax⟩ := HalfMax.exists_le_maj_of_iso X la
  have hm : 0 < min δ ε := lt_min hδ hε
  refine ⟨Real.sqrt (min δ ε), Real.sqrt_pos.2 hm, fun P hP z hz hhalf hpos => ?_⟩
  refine Real.sqrt_le_sqrt (le_csInf ?_ ?_)
  · by_contra hne
    have hbot : ∀ v ∈ X.Λ, v = 0 := fun v hv => by
      by_contra hv0
      exact hne ⟨_, v, hv, hv0, rfl⟩
    have h1 : Submodule.span E (X.Λ : Set (Fin r → E)) = ⊥ := Submodule.span_eq_bot.2 hbot
    have h2 : (1 : Fin r → E) ∈ Submodule.span E (X.Λ : Set (Fin r → E)) := by
      rw [X.Λ_span]; exact Submodule.mem_top
    rw [h1, Submodule.mem_bot] at h2
    exact one_ne_zero (congrFun h2 ⟨0, hr⟩)
  · rintro _ ⟨v, hv, hv0, rfl⟩
    have hp : ∀ τ : X.Ψ, 0 < X.maj z τ (Data.emb τ.1 v) := fun τ => by
      refine X.maj_pos hz τ fun h => hv0 ?_
      funext a
      have := congr_fun h a
      simpa [Data.emb] using this
    obtain ⟨τ, hτ⟩ : ∃ τ : X.Ψ, min δ ε ≤ X.c τ * X.maj z τ (Data.emb τ.1 v) := by
      by_contra hcon
      push Not at hcon
      have hvv := hiso z hz v hv fun τ => (hcon τ).trans_le (min_le_left _ _)
      obtain ⟨τ, hτ⟩ := hmax P hP z hz hhalf hpos v ⟨hv, hvv, hv0⟩
      exact absurd ((min_le_right δ ε).trans hτ) (not_le.2 (hcon τ))
    exact hτ.trans (Finset.single_le_sum
      (f := fun τ : X.Ψ => X.c τ * X.maj z τ (Data.emb τ.1 v))
      (fun σ _ => (mul_pos (HalfMax.c_pos' X σ) (hp σ)).le) (Finset.mem_univ τ))

end GlobalTheory
