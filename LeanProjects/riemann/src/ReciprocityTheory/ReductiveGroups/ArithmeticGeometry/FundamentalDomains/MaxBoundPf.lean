import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspidalExponentialDecay
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.PeriodicSchwarzLemma
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MaximumBoundField

namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex Filter
open scoped ComplexConjugate Topology Real

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

theorem maxBound_holds : MaxBoundStatement (E := E) := by
  classical
  intro r X la P M w hP hM hw hw0 htr z0 hz0 hhalf hpos v hv hv0
  by_contra hcon
  push_neg at hcon
  have hf : (1 : ℝ) ≤ (fdeg E : ℝ) := one_le_field_half_degree (E := E)
  have hk0 : 0 < X.k0 := X.minWeight_pos
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hD : 0 < M * ((fdeg E : ℝ) * w + 2) * X.k0 * Real.log 2 := by positivity
  have hεdef : epStar M (fdeg E) w X.k0 =
      min 1 (Real.pi / (M * ((fdeg E : ℝ) * w + 2) * X.k0 * Real.log 2)) := rfl
  obtain ⟨ε, hεe⟩ : ∃ ε, ε = epStar M (fdeg E) w X.k0 := ⟨_, rfl⟩
  rw [← hεe] at hcon
  have hε1 : ε ≤ 1 := by rw [hεe, hεdef]; exact min_le_left _ _
  have hε2 : ε * (M * ((fdeg E : ℝ) * w + 2) * X.k0 * Real.log 2) ≤ Real.pi := by
    have h : ε ≤ Real.pi / (M * ((fdeg E : ℝ) * w + 2) * X.k0 * Real.log 2) := by
      rw [hεe, hεdef]; exact min_le_right _ _
    exact (le_div_iff₀ hD).mp h
  have hεpos : 0 < ε := by
    rw [hεe, hεdef]; exact lt_min one_pos (div_pos Real.pi_pos hD)

  have hvv : herm X.Gm v v = 0 :=
    flowTermNormDecay.herm_eq_zero X hz0 hv (fun τ => lt_of_lt_of_le (hcon τ) hε1)
  have hemb0 : ∀ τ : X.Ψ, Data.emb τ.1 v ≠ 0 := by
    intro τ h
    apply hv0
    funext a
    have h2 := congrFun h a
    simp only [Data.emb, Pi.zero_apply, map_eq_zero] at h2
    simpa using h2
  have hIsoV : X.IsIsoV (fun τ : X.Ψ => Data.emb τ.1 v) := by
    intro τ
    refine ⟨?_, hemb0 τ⟩
    show hermC τ.1 X.Gm (Data.emb τ.1 v) (Data.emb τ.1 v) = 0
    rw [hermC_emb, hvv, map_zero]
  have hc : ∀ τ : X.Ψ, X.c τ = X.k0 := by
    intro τ
    show 2 * ‖τ.1 X.ξ0‖ = X.k0
    rw [X.ξ0_abs τ]; ring
  have hmaj : ∀ τ : X.Ψ, 0 < X.maj z0 τ (Data.emb τ.1 v) :=
    fun τ => Data.maj_pos (X := X.toData) hz0 τ (hemb0 τ)
  have httV : ∀ (s : ℂ) (τ : X.Ψ), s.im / X.ttV (fun τ : X.Ψ => Data.emb τ.1 v) z0 τ =
      s.im * (X.k0 * X.maj z0 τ (Data.emb τ.1 v)) := by
    intro s τ
    show s.im / (1 / (X.c τ * X.maj z0 τ (Data.emb τ.1 v))) = _
    rw [hc τ, one_div, div_inv_eq_mul]

  have hdomiff : ∀ ζ : ℂ, X.flow v (fun _ => ζ) z0 ∈ X.dom ↔
      ∀ τ : X.Ψ, 0 < 1 + ζ.im * (X.k0 * X.maj z0 τ (Data.emb τ.1 v)) := by
    intro ζ
    have h := (flowDomainCriterion_holds (E := E) r X.toData (fun τ : X.Ψ => Data.emb τ.1 v) hIsoV z0 hz0
      (fun _ => ζ)).1
    rw [show X.flow v (fun _ => ζ) z0 =
      X.flowV (fun τ : X.Ψ => Data.emb τ.1 v) (fun _ => ζ) z0 from rfl, h]
    exact forall_congr' fun τ => by rw [httV ζ τ]

  have hcc : cc (1 : E) = 1 := by simp [cc]
  obtain ⟨γ, hγΓ, hχ, hγmap⟩ := htr v hv hvv 1 hcc isIntegral_one
  have hP' := hP
  obtain ⟨⟨⟨hSecD, -, hSecΓ⟩, -⟩, -⟩ := hP'
  have hflowmat : ∀ (ζ : ℂ) (τ : X.Ψ),
      mat (X.flow v (fun _ => ζ) z0) τ = X.flowMat v τ ζ * mat z0 τ := fun _ _ => rfl
  have hshift : ∀ ζ : ℂ, X.flow v (fun _ => ζ + (M : ℂ)) z0 =
      lact γ (X.flow v (fun _ => ζ) z0) := by
    intro ζ
    funext τ
    show X.flowMat v τ (ζ + (M : ℂ)) * mat z0 τ =
      (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat (X.flow v (fun _ => ζ) z0) τ
    rw [hγmap τ, map_one, mul_one, hflowmat ζ τ, ← Matrix.mul_assoc,
      EmbeddingHermitianPairs.flowMat_mul (X := X.toData) hvv τ (M : ℂ) ζ, add_comm]
  obtain ⟨G, hG⟩ : ∃ G : ℂ → ℂ, ∀ ζ, G ζ =
      if (∀ τ : X.Ψ, 0 < 1 + ζ.im * (X.k0 * X.maj z0 τ (Data.emb τ.1 v)))
      then P (X.flow v (fun _ => ζ) z0) else 0 := ⟨_, fun _ => rfl⟩
  have hGper : Function.Periodic G (M : ℂ) := by
    intro ζ
    have him : (ζ + (M : ℂ)).im = ζ.im := by simp
    rw [hG, hG]
    simp only [him]
    split_ifs with hcond
    · rw [hshift ζ, hSecΓ γ hγΓ _ ((hdomiff ζ).2 hcond), hχ, one_mul]
    · rfl

  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = 1 / (2 * X.k0 * ε) := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = 1 / (X.k0 * ε) := ⟨_, rfl⟩
  have hkε : 0 < X.k0 * ε := mul_pos hk0 hεpos
  have htpos : 0 < t := by rw [ht]; positivity
  have hTpos : 0 < T := by rw [hT]; positivity
  have htT : t < T := by
    rw [ht, hT]
    apply one_div_lt_one_div_of_lt hkε
    nlinarith
  have hTk : T * (X.k0 * ε) = 1 := by
    rw [hT, div_mul_eq_mul_div, one_mul, div_self hkε.ne']
  have htk : t * (X.k0 * ε) = 1 / 2 := by
    rw [ht, div_mul_eq_mul_div, one_mul, div_eq_iff (by positivity)]
    ring
  have hcondT : ∀ ζ : ℂ, -T < ζ.im →
      ∀ τ : X.Ψ, 0 < 1 + ζ.im * (X.k0 * X.maj z0 τ (Data.emb τ.1 v)) := by
    intro ζ hζ τ
    have hpos' : 0 < X.k0 * X.maj z0 τ (Data.emb τ.1 v) := mul_pos hk0 (hmaj τ)
    have hb : X.k0 * X.maj z0 τ (Data.emb τ.1 v) < X.k0 * ε :=
      mul_lt_mul_of_pos_left (hcon τ) hk0
    nlinarith [mul_pos (show 0 < ζ.im + T by linarith) hpos',
      mul_pos hTpos (show 0 < X.k0 * ε - X.k0 * X.maj z0 τ (Data.emb τ.1 v) by linarith)]
  have hdom0 : ∀ ζ : ℂ, 0 ≤ ζ.im → X.flow v (fun _ => ζ) z0 ∈ X.dom := by
    intro ζ hζ
    exact (hdomiff ζ).2 (hcondT ζ (by linarith))

  have hφd : Differentiable ℂ (fun ζ : ℂ => X.flow v (fun _ => ζ) z0) := by
    rw [differentiable_pi]; intro τ
    rw [differentiable_pi]; intro a
    rw [differentiable_pi]; intro b
    simp only [Data.flow, Data.flowMat, mat, Matrix.mul_apply, Matrix.of_apply]
    fun_prop
  have hdiff : ∀ z : ℂ, -T < z.im → DifferentiableAt ℂ G z := by
    intro z hz
    have hU : IsOpen {ζ : ℂ | -T < ζ.im} := isOpen_lt continuous_const Complex.continuous_im
    have hmem : ∀ ζ : ℂ, -T < ζ.im → X.flow v (fun _ => ζ) z0 ∈ X.dom :=
      fun ζ h => (hdomiff ζ).2 (hcondT ζ h)
    have h1 : DifferentiableWithinAt ℂ (fun ζ : ℂ => P (X.flow v (fun _ => ζ) z0))
        {ζ : ℂ | -T < ζ.im} z :=
      (hSecD _ (hmem z hz)).comp z (hφd z).differentiableWithinAt (fun ζ h => hmem ζ h)
    have h2 := h1.differentiableAt (hU.mem_nhds hz)
    refine h2.congr_of_eventuallyEq ?_
    filter_upwards [hU.mem_nhds hz] with ζ hζ
    rw [hG, if_pos (hcondT ζ hζ)]
  have hzero : Tendsto G (comap im atTop) (𝓝 0) :=
    flowTermNormDecay.tendsto_zero X la P hP hz0 hv hvv hv0 hdom0 G (fun ζ hζ => by
      rw [hG, if_pos (hcondT ζ (by linarith))])

  have hpn : ∀ x, X.pnorm la P x = ‖P x‖ * X.nfac la x := fun _ => rfl
  have hnf_nonneg : ∀ x, 0 ≤ X.nfac la x := by
    intro x
    unfold Data.nfac
    exact Finset.prod_nonneg fun τ _ => Finset.prod_nonneg fun i _ =>
      Real.rpow_nonneg (norm_nonneg _) _
  have hN0 : 0 < X.nfac la z0 := by
    have h := hpos
    rw [hpn] at h
    rcases (hnf_nonneg z0).lt_or_eq with h' | h'
    · exact h'
    · rw [← h', mul_zero] at h; exact absurd h (lt_irrefl 0)
  have hK : ∀ z : ℂ, z.im = -t →
      ‖G z‖ ≤ 2 * X.pnorm la P z0 * (2 : ℝ) ^ (w / 2) / X.nfac la z0 := by
    intro z hz
    have hcz := hcondT z (by rw [hz]; linarith)
    have hy := (hdomiff z).2 hcz
    rw [hG, if_pos hcz]
    have hN := m3bNorm_holds (E := E) r X.toData (fun τ : X.Ψ => Data.emb τ.1 v) hIsoV la z0 hz0
      (fun _ => z) hy
    dsimp only at hN
    have hq : ∀ τ : X.Ψ, 1 / 2 < 1 + z.im / X.ttV (fun τ : X.Ψ => Data.emb τ.1 v) z0 τ ∧
        1 + z.im / X.ttV (fun τ : X.Ψ => Data.emb τ.1 v) z0 τ ≤ 1 := by
      intro τ
      rw [httV z τ, hz]
      have ha := mul_pos hk0 (hmaj τ)
      have hb : X.k0 * X.maj z0 τ (Data.emb τ.1 v) < X.k0 * ε :=
        mul_lt_mul_of_pos_left (hcon τ) hk0
      constructor
      · nlinarith [mul_lt_mul_of_pos_left hb htpos]
      · nlinarith [mul_pos htpos ha]
    have hmax : ∏ τ : X.Ψ, max (1 + z.im / X.ttV (fun τ : X.Ψ => Data.emb τ.1 v) z0 τ)
          (1 + z.im / X.ttV (fun τ : X.Ψ => Data.emb τ.1 v) z0 τ)⁻¹ ^ (X.spread la τ / 2)
        ≤ (2 : ℝ) ^ (w / 2) := by
      calc _ ≤ ∏ τ : X.Ψ, (2 : ℝ) ^ (X.spread la τ / 2) := by
            apply Finset.prod_le_prod
            · intro τ _
              obtain ⟨h1, -⟩ := hq τ
              exact Real.rpow_nonneg (le_trans (by linarith) (le_max_left _ _)) _
            · intro τ _
              obtain ⟨h1, h2⟩ := hq τ
              apply Real.rpow_le_rpow (le_trans (by linarith) (le_max_left _ _)) _
                (div_nonneg (flowTermNormDecay.spread_nonneg' X.toData la τ) (by norm_num))
              apply max_le (by linarith)
              rw [inv_le_comm₀ (by linarith) (by norm_num)]
              linarith
        _ = (2 : ℝ) ^ (∑ τ : X.Ψ, X.spread la τ / 2) :=
            (Real.rpow_sum_of_pos (by norm_num) _ _).symm
        _ ≤ (2 : ℝ) ^ (w / 2) := by
            apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
            rw [← Finset.sum_div]
            linarith
    have hmin : 0 < ∏ τ : X.Ψ, min (1 + z.im / X.ttV (fun τ : X.Ψ => Data.emb τ.1 v) z0 τ)
          (1 + z.im / X.ttV (fun τ : X.Ψ => Data.emb τ.1 v) z0 τ)⁻¹ ^ (X.spread la τ / 2) := by
      apply Finset.prod_pos
      intro τ _
      obtain ⟨h1, -⟩ := hq τ
      exact Real.rpow_pos_of_pos (lt_min (by linarith) (inv_pos.mpr (by linarith))) _
    have hratio : 0 < X.nfac la z0 / X.nfac la (X.flow v (fun _ => z) z0) :=
      lt_of_lt_of_le hmin hN.1
    have hNy : 0 < X.nfac la (X.flow v (fun _ => z) z0) := by
      rcases (hnf_nonneg (X.flow v (fun _ => z) z0)).lt_or_eq with h | h
      · exact h
      · rw [← h, div_zero] at hratio; exact absurd hratio (lt_irrefl 0)
    have hr2 : X.nfac la z0 / X.nfac la (X.flow v (fun _ => z) z0) ≤ (2 : ℝ) ^ (w / 2) :=
      le_trans hN.2 hmax
    have hN0le : X.nfac la z0 ≤ (2 : ℝ) ^ (w / 2) * X.nfac la (X.flow v (fun _ => z) z0) := by
      rw [div_le_iff₀ hNy] at hr2; linarith
    have hPy := hhalf _ hy
    rw [hpn] at hPy
    have hPn := norm_nonneg (P (X.flow v (fun _ => z) z0))
    have hK0 : 0 ≤ (2 : ℝ) ^ (w / 2) := by positivity
    rw [le_div_iff₀ hN0]
    nlinarith [mul_le_mul_of_nonneg_left hN0le hPn, mul_le_mul_of_nonneg_left hPy hK0]

  have hS := PeriodicSchwarzLemma.periodic_schwarz hM htpos htT hGper hdiff hzero hK
  have hG0 : G 0 = P z0 := by
    rw [hG, if_pos (fun τ => by simp)]
    congr 1
    funext τ
    show X.flowMat v τ 0 * mat z0 τ = z0 τ
    rw [EmbeddingHermitianPairs.flowMat_zero (X := X.toData) v τ, Matrix.one_mul]
    rfl
  rw [hG0] at hS
  have h1' := mul_le_mul_of_nonneg_right hS hN0.le
  have h1 : X.pnorm la P z0 ≤
      Real.exp (-2 * π * t / M) * (2 * X.pnorm la P z0 * (2 : ℝ) ^ (w / 2)) := by
    calc X.pnorm la P z0 = ‖P z0‖ * X.nfac la z0 := hpn z0
      _ ≤ _ := h1'
      _ = _ := by rw [mul_assoc, div_mul_cancel₀ _ hN0.ne']
  have h2 : 1 ≤ Real.exp (-2 * π * t / M) * (2 * (2 : ℝ) ^ (w / 2)) := by
    by_contra hh
    push_neg at hh
    nlinarith [mul_lt_mul_of_pos_left hh hpos]

  have hkey : ((fdeg E : ℝ) * w + 2) * Real.log 2 ≤ 2 * π * t / M := by
    have he : 2 * π * t / M = π / (M * X.k0 * ε) := by
      rw [ht]; field_simp <;> ring
    rw [he, le_div_iff₀ (by positivity)]
    calc ((fdeg E : ℝ) * w + 2) * Real.log 2 * (M * X.k0 * ε)
        = ε * (M * ((fdeg E : ℝ) * w + 2) * X.k0 * Real.log 2) := by ring
      _ ≤ π := hε2
  have hfin : Real.exp (-2 * π * t / M) * (2 * (2 : ℝ) ^ (w / 2)) < 1 := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    rw [show (2 : ℝ) * Real.exp (Real.log 2 * (w / 2)) =
        Real.exp (Real.log 2) * Real.exp (Real.log 2 * (w / 2)) by
          rw [Real.exp_log (by norm_num)],
      ← Real.exp_add, ← Real.exp_add]
    refine lt_of_lt_of_eq (Real.exp_lt_exp.mpr ?_) Real.exp_zero
    have hneg : -2 * π * t / M = -(2 * π * t / M) := by ring
    rw [hneg]
    nlinarith [hkey, mul_le_mul_of_nonneg_right hf (le_of_lt (mul_pos hw0 hlog2)),
      mul_pos hw0 hlog2]
  exact absurd h2 (not_le.mpr hfin)

end ReciprocityTheory.ChartRestriction.G.FD
