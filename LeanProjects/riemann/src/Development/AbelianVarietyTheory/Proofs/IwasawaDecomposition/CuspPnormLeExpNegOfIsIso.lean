import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPosLowerBoundNearMax

open NumberField Complex Filter ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate Topology Real

namespace GlobalTheory

theorem cusp_pnorm_le_exp_neg_of_isIso (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ)
    (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (v : Fin r → E) (hP : P ∈ X.SS la)
    (hξ : X.IsIso v) :
    ∃ C c : ℝ, 0 < c ∧ ∀ x ∈ X.dom, ∀ t : ℝ, 1 ≤ t → (∀ τ, t ≤ X.tt v x τ) →
      X.pnorm la P x ≤ C * Real.exp (-c * t) := by
  obtain ⟨M, hM, htrans⟩ := HalfMax.exists_period X la
  obtain ⟨C0, hC0⟩ := hP.1.2
  set w : ℝ := ∑ τ, X.spread la τ with hw
  have hpi := Real.pi_pos
  refine ⟨2 ^ (w / 2) * C0, π / M, by positivity, fun z0 hz0 t' ht' htt' => ?_⟩
  obtain ⟨hv, hvv, hv0⟩ := id hξ
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
  set t : ℝ := t' / 2 with ht
  have ht0 : 0 < t := by linarith
  have htt : ∀ τ, 2 * t ≤ X.ttV e z0 τ := by
    intro τ
    have h : t' ≤ X.ttV e z0 τ := htt' τ
    linarith
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
    HalfMax.tendsto_zero X la P hP hz0 hξ
      (fun ζ hζ => hdom ζ (by linarith)) g
      (fun ζ hζ => by simp only [hg, if_pos (show -(2 * t) < ζ.im by linarith)])
  have hnz : 0 < X.nfac la z0 := flowTermNormDecay.nfac_pos X la hz0
  set B : ℝ := 2 ^ (w / 2) * C0 / X.nfac la z0 with hB
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
    have h1 : ‖P y‖ * X.nfac la y ≤ C0 := hC0 y hyd
    have h2 : X.nfac la z0 ≤ 2 ^ (w / 2) * X.nfac la y := by
      rw [div_le_iff₀ hnf] at hratio
      exact hratio.trans (mul_le_mul_of_nonneg_right hprod hnf.le)
    rw [hB, le_div_iff₀ hnz]
    calc ‖P y‖ * X.nfac la z0 ≤ ‖P y‖ * (2 ^ (w / 2) * X.nfac la y) := by gcongr
      _ = 2 ^ (w / 2) * (‖P y‖ * X.nfac la y) := by ring
      _ ≤ 2 ^ (w / 2) * C0 := by gcongr
  have hsch := PeriodicSchwarzLemma.periodic_schwarz hM ht0 (show t < 2 * t by linarith) hper hdiff hzero hBd
  have hg0 : g 0 = P z0 := by
    simp only [hg, Complex.zero_im, if_pos (show -(2 * t) < (0 : ℝ) by linarith)]
    congr 1
    exact EmbeddingHermitianPairs.flow_zero X v z0
  rw [hg0] at hsch
  have hexp : -2 * π * t / M = -(π / M) * t' := by
    rw [ht]
    ring
  rw [hexp, hB, ← mul_div_assoc, le_div_iff₀ hnz] at hsch
  calc X.pnorm la P z0 = ‖P z0‖ * X.nfac la z0 := rfl
    _ ≤ _ := hsch
    _ = _ := mul_comm _ _

end GlobalTheory
