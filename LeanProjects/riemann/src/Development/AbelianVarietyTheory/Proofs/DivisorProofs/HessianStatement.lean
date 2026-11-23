import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelSt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LieAlgebraMaps
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.AApproxA
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubharmonicLogConvexityQuotientStatement

set_option autoImplicit false

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts
open GlobalTheory.ShFam GlobalTheory.ChernReg
open scoped ContDiff

namespace GlobalTheory.HessReg

theorem leviV_eq_leviForm {n : ℕ} {g : ReciprocityTheory.L2DbarEstimates.V n → ℝ} {y : ReciprocityTheory.L2DbarEstimates.V n}
    (hg : ContDiffAt ℝ 2 g y) (ξ : Fin n → ℂ) :
    ReciprocityTheory.L2DbarEstimates.leviV n (fun v => (g v : ℂ)) y ξ =
      GlobalTheory.leviForm g y (WithLp.toLp 2 ξ) (WithLp.toLp 2 ξ) := by
  rw [ReciprocityTheory.L2DbarEstimates.Y.leviV_eq_dv (GlobalTheory.contDiffAt_ofReal_comp hg), GlobalTheory.leviForm_eq_del_dbar hg]
  have e : (fun v => ReciprocityTheory.L2DbarEstimates.Y.dbv (fderiv ℝ (fun v => (g v : ℂ)) v) (WithLp.toLp 2 ξ)) =
      fun x => GlobalTheory.dbar (fun y => (g y : ℂ)) x (WithLp.toLp 2 ξ) := by
    funext x
    rw [GlobalTheory.dbar_apply, ReciprocityTheory.L2DbarEstimates.Y.dbv]
    simp only [smul_eq_mul]
    ring
  rw [e, GlobalTheory.del_apply, ReciprocityTheory.L2DbarEstimates.Y.dv]
  simp only [smul_eq_mul]
  ring

section Core

variable {k : Type} [CommRing k] {Y : AlgebraicGeometry.Scheme.{0}} {p : Y ⟶ ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k}
  {σ : k →+* ℂ} {d : ℕ}

theorem kae_zero {R : GlobalTheory.AnRead p σ d} {a : ChartForm p σ d} (ha : IsKaehlerForm R a) {c : GlobalTheory.AlgChart p σ d}
    {y : GlobalTheory.CxPts p σ} (hy : y ∈ c.e.source) : a c y 0 = 0 := by
  have := (continuous_and_smul ha hy).2 0 0
  simpa using this

theorem kae_nonneg {R : GlobalTheory.AnRead p σ d} {a : ChartForm p σ d} (ha : IsKaehlerForm R a) {c : GlobalTheory.AlgChart p σ d}
    {y : GlobalTheory.CxPts p σ} (hy : y ∈ c.e.source) (ξ : Fin d → ℂ) : 0 ≤ a c y ξ := by
  by_cases h : ξ = 0
  · rw [h, kae_zero ha hy]
  · exact (ha.2 c y hy ξ h).le

theorem isOpen_ann (δ : ℝ) : IsOpen {w : ℂ | 0 < ‖w‖ ∧ ‖w‖ < δ} :=
  (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)

theorem core {R : GlobalTheory.AnRead p σ d} {a θ : ChartForm p σ d} {Ψ : GlobalTheory.CxPts p σ → ℝ → ℝ} {A K δ : ℝ}
    (h : IsRegConst a θ Ψ A K δ) (ha : IsKaehlerForm R a) (hθ : ∀ c y, θ c y 0 = 0)
    {Cl t₁ : ℝ} (hCl : 0 ≤ Cl) (ht₁ : 0 < t₁) (ht₁δ : t₁ < δ) (ht₁1 : t₁ < 1)
    (hlow : ∀ t, 0 < t → t ≤ t₁ → ∀ y, -(Cl * Real.log (Real.log (1 / t))) ≤ Ψ y t + K * t ^ 2 ∧
      Ψ y t + K * t ^ 2 ≤ Cl)
    (t : ℝ) (ht : 0 < t) (htt : t ≤ t₁ ^ 2) (hte : t ≤ Real.exp (-Real.exp 1)) :
    R.SmoothOn Set.univ (fun y => Ψ y t + K * t ^ 2) ∧ ∀ c : GlobalTheory.AlgChart p σ d, ∀ y ∈ c.e.source, ∀ ξ,
      -((2 * A * (2 * Cl + 5 * K) + K) * (Real.log (Real.log (1 / t)) / Real.log (1 / t)) * a c y ξ) ≤
        θ c y ξ + ddcForm (fun z => Ψ z t + K * t ^ 2) c y ξ := by
  have hA := h.A_nonneg
  have hK := h.K_nonneg
  have hδ := h.δ_pos
  have htt₁ : t < t₁ := lt_of_le_of_lt htt (by nlinarith)
  have htδ : t < δ := htt₁.trans ht₁δ
  have hnt : ‖(t : ℂ)‖ = t := by simp [abs_of_pos ht]
  have hmem : ∀ (c : GlobalTheory.AlgChart p σ d) v, v ∈ c.e.target →
      (v, (t : ℂ)) ∈ c.e.target ×ˢ {w : ℂ | 0 < ‖w‖ ∧ ‖w‖ < δ} := fun c v hv =>
    ⟨hv, by simp only [Set.mem_setOf_eq, hnt]; exact ⟨ht, htδ⟩⟩
  have hφ : ContDiff ℝ ∞ (fun v : ReciprocityTheory.L2DbarEstimates.V d => (v, (t : ℂ))) := contDiff_id.prodMk contDiff_const
  refine ⟨fun i => ?_, fun c y hy ξ => ?_⟩
  · have hc := (h.smooth (R.chart i)).comp hφ.contDiffOn (s := (R.chart i).e.target ∩ (R.chart i).e.symm ⁻¹' Set.univ)
      (fun v (hv : v ∈ (R.chart i).e.target ∩ _) => hmem _ v hv.1)
    refine (hc.add (contDiffOn_const (c := K * t ^ 2))).congr fun v _ => ?_
    simp only [Function.comp_apply, hnt]

  · have hF := h.smooth c
    have hopen : IsOpen (c.e.target ×ˢ {w : ℂ | 0 < ‖w‖ ∧ ‖w‖ < δ}) := c.e.open_target.prod (isOpen_ann δ)
    have hF2 : ∀ q ∈ c.e.target ×ˢ {w : ℂ | 0 < ‖w‖ ∧ ‖w‖ < δ},
        ContDiffAt ℝ 2 (fun q : ReciprocityTheory.L2DbarEstimates.V d × ℂ => Ψ (c.e.symm q.1) ‖q.2‖) q :=
      fun q hq => (hF.contDiffAt (hopen.mem_nhds hq)).of_le (WithTop.coe_le_coe.2 le_top)
    have hy' := c.e.map_source hy
    have hinv := c.e.left_inv hy
    set g : ℝ → ℝ := fun s => Ψ y s with hg_def
    have hg : ContDiffOn ℝ 2 g (Set.Ioo 0 δ) := by
      have hψ : ContDiff ℝ ∞ (fun s : ℝ => (c.e y, (s : ℂ))) :=
        contDiff_const.prodMk Complex.ofRealCLM.contDiff
      refine ((hF.comp hψ.contDiffOn (s := Set.Ioo 0 δ) fun s hs => ⟨hy', ?_⟩).of_le
        (WithTop.coe_le_coe.2 le_top)).congr fun s hs => ?_
      · simp only [Set.mem_setOf_eq, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs.1]; exact hs
      · simp only [g, Function.comp_apply, hinv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs.1]
    have hLevi : ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ < δ →
        -(Real.pi * K) ≤ (GlobalTheory.leviForm (fun z : ℂ => g ‖z‖) w 1 1).re := by
      intro w hw1 hw2
      have H := h.hess c y hy w hw1 hw2 0 1
      have hφ2 : ContDiffAt ℂ 2 (fun z : ℂ => ((c.e y : ReciprocityTheory.L2DbarEstimates.V d), z)) w :=
        (contDiff_const.prodMk contDiff_id).contDiffAt
      have hd : fderiv ℂ (fun z : ℂ => ((c.e y : ReciprocityTheory.L2DbarEstimates.V d), z)) w 1 = (0, 1) := by
        have hh : HasFDerivAt (fun z : ℂ => ((c.e y : ReciprocityTheory.L2DbarEstimates.V d), z))
            ((0 : ℂ →L[ℂ] ReciprocityTheory.L2DbarEstimates.V d).prod (ContinuousLinearMap.id ℂ ℂ)) w :=
          (hasFDerivAt_const _ w).prodMk (hasFDerivAt_id w)
        rw [hh.fderiv]; simp
      have e0 := GlobalTheory.leviForm_comp_holo (hF2 _ ⟨hy', hw1, hw2⟩) hφ2 1 1
      rw [hd] at e0
      have e1 : (fun x : ℂ => Ψ (c.e.symm ((fun z : ℂ => ((c.e y : ReciprocityTheory.L2DbarEstimates.V d), z)) x).1)
          ‖((fun z : ℂ => ((c.e y : ReciprocityTheory.L2DbarEstimates.V d), z)) x).2‖) = fun z => g ‖z‖ := by
        funext z; simp only [g, hinv]
      rw [e1] at e0
      rw [e0]
      have h0 : ((0 : ReciprocityTheory.L2DbarEstimates.V d)).ofLp = 0 := rfl
      rw [h0, kae_zero ha hy, hθ] at H
      have H' : -K ≤ (GlobalTheory.leviForm (fun q : ReciprocityTheory.L2DbarEstimates.V d × ℂ => Ψ (c.e.symm q.1) ‖q.2‖) (c.e y, w)
          (0, 1) (0, 1)).re / Real.pi := by
        simpa using H
      have := (le_div_iff₀ Real.pi_pos).1 H'
      linarith

    have hsl := GlobalTheory.T.subharmonic_log_convexity_quotient g δ (Real.pi * K) hδ hg hLevi t t₁ ht htt₁ ht₁δ
    have hgd : DifferentiableAt ℝ g t :=
      (hg.differentiableOn (by norm_num) t ⟨ht, htδ⟩).differentiableAt (Ioo_mem_nhds ht htδ)
    have hder : deriv (fun s => Ψ y s + K * s ^ 2) t = deriv g t + K * (2 * t) := by
      have := (hgd.hasDerivAt.add ((hasDerivAt_pow 2 t).const_mul K)).deriv
      have e : (fun s => Ψ y s + K * s ^ 2) = g + fun s => K * s ^ 2 := rfl
      rw [e, this]; push_cast; ring
    set L := Real.log (1 / t) with hL_def
    set LL := Real.log L with hLL_def
    have hlogt : Real.log t ≤ -Real.exp 1 := by
      have := Real.log_le_log ht hte; rwa [Real.log_exp] at this
    have hL : L = -Real.log t := by rw [hL_def, one_div, Real.log_inv]
    have hLe : Real.exp 1 ≤ L := by rw [hL]; linarith
    have hLpos : 0 < L := lt_of_lt_of_le (Real.exp_pos 1) hLe
    have hLL : 1 ≤ LL := by rw [hLL_def]; exact (Real.le_log_iff_exp_le hLpos).2 hLe
    have hlogt₁ : Real.log t ≤ 2 * Real.log t₁ := by
      have := Real.log_le_log ht htt; rwa [Real.log_pow, Nat.cast_ofNat] at this
    have hD : L / 2 ≤ Real.log (t₁ / t) := by
      rw [Real.log_div ht₁.ne' ht.ne', hL]; linarith
    have hup := (hlow t₁ ht₁ le_rfl y).2
    have hdn := (hlow t ht htt₁.le y).1
    have ht₁sq : t₁ ^ 2 ≤ 1 := by nlinarith
    have htsq : t ^ 2 ≤ 1 := by nlinarith
    have hN : g t₁ + Real.pi * K * t₁ ^ 2 - (g t + Real.pi * K * t ^ 2) ≤ (2 * Cl + 5 * K) * LL := by
      simp only [g]
      have h1 : Real.pi * K * t₁ ^ 2 ≤ Real.pi * K * 1 :=
        mul_le_mul_of_nonneg_left ht₁sq (mul_nonneg Real.pi_pos.le hK)
      have h2 : Real.pi * K ≤ 4 * K := mul_le_mul_of_nonneg_right Real.pi_le_four hK
      have h3 : Cl + 5 * K ≤ (Cl + 5 * K) * LL := le_mul_of_one_le_right (by linarith) hLL
      have h4 : 0 ≤ Real.pi * K * t ^ 2 := by positivity
      have h5 : 0 ≤ K * t₁ ^ 2 := by positivity
      have h6 : K * t ^ 2 ≤ K := mul_le_of_le_one_right hK htsq
      have h7 : (2 * Cl + 5 * K) * LL = (Cl + 5 * K) * LL + Cl * LL := by ring
      rw [h7]
      linarith
    have hM0 : 0 ≤ (2 * Cl + 5 * K) * LL := mul_nonneg (by linarith) (by linarith)
    have hT : t * deriv (fun s => Ψ y s + K * s ^ 2) t ≤ 2 * (2 * Cl + 5 * K) * (LL / L) := by
      rw [hder]
      have hDpos : 0 < Real.log (t₁ / t) := lt_of_lt_of_le (half_pos hLpos) hD
      have h1 : t * deriv g t + 2 * (Real.pi * K) * t ^ 2 ≤ (2 * Cl + 5 * K) * LL / Real.log (t₁ / t) :=
        hsl.trans (div_le_div_of_nonneg_right hN hDpos.le)
      have h2 : (2 * Cl + 5 * K) * LL / Real.log (t₁ / t) ≤ (2 * Cl + 5 * K) * LL / (L / 2) :=
        div_le_div_of_nonneg_left hM0 (half_pos hLpos) hD
      have h3 : (2 * Cl + 5 * K) * LL / (L / 2) = 2 * (2 * Cl + 5 * K) * (LL / L) := by
        field_simp
      have h4 : t * (deriv g t + K * (2 * t)) ≤ t * deriv g t + 2 * (Real.pi * K) * t ^ 2 := by
        nlinarith [mul_nonneg (by linarith [Real.pi_gt_three] : (0 : ℝ) ≤ Real.pi - 1) (mul_nonneg hK (sq_nonneg t))]
      linarith
    have ht2 : t ^ 2 ≤ LL / L := by
      rw [le_div_iff₀ hLpos]
      have h1 : L ≤ 1 / t - 1 := Real.log_le_sub_one_of_pos (by positivity)
      have h2 : t ^ 2 * L ≤ t ^ 2 * (1 / t) := mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg t)
      have h3 : t ^ 2 * (1 / t) = t := by field_simp
      have h4 : t ≤ 1 := by nlinarith
      linarith
    have H := h.hess c y hy (t : ℂ) (by rw [hnt]; exact ht) (by rw [hnt]; exact htδ) (WithLp.toLp 2 ξ) 0
    rw [hnt] at H
    simp only [WithLp.ofLp_toLp, norm_zero, mul_zero, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow] at H
    have hξa := kae_nonneg ha hy ξ
    have hddc : ddcForm (fun z => Ψ z t + K * t ^ 2) c y ξ =
        (GlobalTheory.leviForm (fun q : ReciprocityTheory.L2DbarEstimates.V d × ℂ => Ψ (c.e.symm q.1) ‖q.2‖) (c.e y, (t : ℂ))
          (WithLp.toLp 2 ξ, 0) (WithLp.toLp 2 ξ, 0)).re / Real.pi := by
      have hFt := hF2 _ (hmem c _ hy')
      have hφt : ContDiffAt ℂ 2 (fun v : ReciprocityTheory.L2DbarEstimates.V d => (v, (t : ℂ))) (c.e y) :=
        (contDiff_id.prodMk contDiff_const).contDiffAt
      have hh : HasFDerivAt (fun v : ReciprocityTheory.L2DbarEstimates.V d => (v, (t : ℂ)))
          ((ContinuousLinearMap.id ℂ (ReciprocityTheory.L2DbarEstimates.V d)).prod (0 : ReciprocityTheory.L2DbarEstimates.V d →L[ℂ] ℂ)) (c.e y) :=
        (hasFDerivAt_id _).prodMk (hasFDerivAt_const _ _)
      have hd : fderiv ℂ (fun v : ReciprocityTheory.L2DbarEstimates.V d => (v, (t : ℂ))) (c.e y) (WithLp.toLp 2 ξ) =
          (WithLp.toLp 2 ξ, 0) := by
        rw [hh.fderiv]; simp
      have e0 := GlobalTheory.leviForm_comp_holo (φ := fun v : ReciprocityTheory.L2DbarEstimates.V d => (v, (t : ℂ))) (z := c.e y) hFt hφt
        (WithLp.toLp 2 ξ) (WithLp.toLp 2 ξ)
      rw [hd] at e0
      have hG : ContDiffAt ℝ 2 (fun v : ReciprocityTheory.L2DbarEstimates.V d => Ψ (c.e.symm v) ‖(t : ℂ)‖) (c.e y) :=
        hFt.comp (g := fun q : ReciprocityTheory.L2DbarEstimates.V d × ℂ => Ψ (c.e.symm q.1) ‖q.2‖) (c.e y) (hφt.restrict_scalars ℝ)
      have e2 : (fun v : ReciprocityTheory.L2DbarEstimates.V d => Ψ (c.e.symm v) t + K * t ^ 2) =
          fun v => Ψ (c.e.symm v) ‖(t : ℂ)‖ + K * t ^ 2 := by
        funext v; rw [hnt]
      have hG2 : ContDiffAt ℝ 2 (fun v : ReciprocityTheory.L2DbarEstimates.V d => Ψ (c.e.symm v) t + K * t ^ 2) (c.e y) :=
        e2 ▸ hG.add contDiffAt_const
      unfold ddcForm GlobalTheory.AlgChart.levi
      rw [leviV_eq_leviForm hG2, e2, GlobalTheory.leviForm_add_const _ hG]
      exact congrArg (fun z : ℂ => z.re / Real.pi) e0
    rw [hddc]
    have h1 : A * (t * deriv (fun s => Ψ y s + K * s ^ 2) t) ≤ A * (2 * (2 * Cl + 5 * K) * (LL / L)) :=
      mul_le_mul_of_nonneg_left hT hA
    have h2 : K * t ^ 2 ≤ K * (LL / L) := mul_le_mul_of_nonneg_left ht2 hK
    have h3 : (A * (t * deriv (fun s => Ψ y s + K * s ^ 2) t) + K * t ^ 2) * a c y ξ ≤
        (2 * A * (2 * Cl + 5 * K) + K) * (LL / L) * a c y ξ :=
      mul_le_mul_of_nonneg_right (by linarith) hξa
    have e1 : (A * (t * deriv (fun s => Ψ y s + K * s ^ 2) t) + K * t ^ 2) * a c y ξ =
        A * (t * deriv (fun s => Ψ y s + K * s ^ 2) t) * a c y ξ + K * (t ^ 2 * a c y ξ) := by ring
    rw [e1] at h3
    linarith

end Core

theorem hessSt : ConstSt → LowSt → HessSt := by
  intro hc hl D O x P hC hN hR
  obtain ⟨Cl, t₀, hCl, ht₀, hlow⟩ := hl D O x P hC hN hR
  obtain ⟨hA, hK, hδ, hreg⟩ := hc D O x P hC hN hR
  set t₁ := min (min t₀ (P.δ / 2)) (1 / 2) with ht₁_def
  have ht₁ : 0 < t₁ := lt_min (lt_min ht₀ (half_pos hδ)) one_half_pos
  have ht₁t₀ : t₁ ≤ t₀ := (min_le_left _ _).trans (min_le_left _ _)
  have ht₁δ : t₁ < P.δ := lt_of_le_of_lt ((min_le_left _ _).trans (min_le_right _ _)) (half_lt_self hδ)
  have ht₁1 : t₁ < 1 := lt_of_le_of_lt (min_le_right _ _) one_half_lt_one
  refine ⟨2 * P.a * (2 * Cl + 5 * P.K) + P.K, min (t₁ ^ 2) (Real.exp (-Real.exp 1)),
    add_nonneg (mul_nonneg (mul_nonneg zero_le_two hA) (by linarith)) hK, lt_min (pow_pos ht₁ 2) (Real.exp_pos _), ?_⟩
  intro t ht htle c σ τ i hi
  have e : P.regFund c σ τ i = fun t z =>
      rho (P.om c σ) (P.exph c σ) (phW (metsOf x O.Φ) (refMet x O.Φ) c σ (fund τ i)) z t + P.K * t ^ 2 := by
    funext t z
    simp only [PolDat.regFund, if_pos hi]
  rw [e]
  refine core (hreg c σ τ i hi) (P.om_kaehler c σ) (fun ch y => ?_) hCl ht₁ ht₁δ ht₁1 (fun s hs hst y => ?_) t ht
    (htle.trans (min_le_left _ _)) (htle.trans (min_le_right _ _))
  · simp [thW, curvMet, ddcForm, GlobalTheory.AlgChart.levi, ReciprocityTheory.L2DbarEstimates.leviV]
  · have := hlow s hs (hst.trans ht₁t₀) c σ τ i hi y
    rw [e] at this
    exact ⟨this.1, this.2.1⟩

end GlobalTheory.HessReg
