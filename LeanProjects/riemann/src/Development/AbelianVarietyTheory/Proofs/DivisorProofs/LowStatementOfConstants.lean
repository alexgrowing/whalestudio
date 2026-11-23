import Development.AbelianVarietyTheory.Definitions.Divisors.KernelSt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LieAlgebraMaps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightGreenVanishesOffBoundaryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightGreenContinuousOffBoundaryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KaehlerExponentialChartLimitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogMetricCutoffIntegrableStatement

open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts
open AlgebraicGeometry MeasureTheory GlobalTheory.ChernReg GlobalTheory.ShFam GlobalTheory.CxPts Filter Topology

namespace GlobalTheory.RegLow

theorem mean_le_of_le {d : ℕ} {q f : (Fin d → ℂ) → ℝ} (hc : Continuous q) (hh : ∀ (t : ℝ) ξ, q (t • ξ) = t ^ 2 * q ξ)
    (hp : ∀ ξ, ξ ≠ 0 → 0 < q ξ) {M : ℝ} (hM : 0 ≤ M) (hf : ∀ ξ, f ξ ≤ M) : mean q f ≤ M := by
  have hm := mass_pos hc hh hp
  rw [mean, div_le_iff₀ hm]
  by_cases hi : Integrable fun ξ => f ξ * GlobalTheory.ChernReg.cutoff (q ξ)
  · rw [← integral_const_mul]
    exact integral_mono hi ((integrable_cutoff hc hh hp).const_mul M) fun ξ =>
      mul_le_mul_of_nonneg_right (hf ξ) (cutoff_nonneg (q ξ)) |>.trans_eq (by ring)
  · rw [integral_undef hi]; positivity

theorem le_mean_of {d : ℕ} {q f g : (Fin d → ℂ) → ℝ} (hc : Continuous q) (hh : ∀ (t : ℝ) ξ, q (t • ξ) = t ^ 2 * q ξ)
    (hp : ∀ ξ, ξ ≠ 0 → 0 < q ξ) {A B : ℝ} (hA : 0 ≤ A) (hg : Integrable fun ξ => g ξ * GlobalTheory.ChernReg.cutoff (q ξ))
    (hB : mean q g ≤ B) (hfg : ∀ ξ, -(A * g ξ) ≤ f ξ) : min 0 (-(A * B)) ≤ mean q f := by
  have hm := mass_pos hc hh hp
  by_cases hi : Integrable fun ξ => f ξ * GlobalTheory.ChernReg.cutoff (q ξ)
  · refine (min_le_right _ _).trans ?_
    have h1 : ∫ ξ, -(A * g ξ) * GlobalTheory.ChernReg.cutoff (q ξ) ≤ ∫ ξ, f ξ * GlobalTheory.ChernReg.cutoff (q ξ) :=
      integral_mono ((hg.const_mul A).neg.congr (ae_of_all _ fun ξ => by simp only [Pi.neg_apply]; ring)) hi
        fun ξ => mul_le_mul_of_nonneg_right (hfg ξ) (cutoff_nonneg (q ξ))
    have e : ∫ ξ, -(A * g ξ) * GlobalTheory.ChernReg.cutoff (q ξ) = -A * ∫ ξ, g ξ * GlobalTheory.ChernReg.cutoff (q ξ) := by
      rw [← integral_const_mul]; congr 1; ext ξ; ring
    rw [e] at h1
    have h2 : -(A * B) ≤ -A * mean q g := by
      have := mul_le_mul_of_nonneg_left hB hA; linarith
    refine h2.trans ?_
    rw [mean, mean, mul_div_assoc']
    exact div_le_div_of_nonneg_right h1 hm.le
  · rw [mean, integral_undef hi, zero_div]; exact min_le_left _ _

theorem L_zero : ∀ (D : D7) (O : Setup D) (x : ToroidalCompactificationData O.s) (c : O.s.Comp) (σ : D.what₂.LL →+* ℂ) (τ : D.what₂.Tau) (i : Fin O.N)
    (y : GlobalTheory.TrueGeo.Pts (O.var c) σ), y ∉ offBd O.Φ c σ → GlobalTheory.HeightParts.psi O x c σ τ i y = 0 := GlobalTheory.T.height_green_vanishes_off_boundary

theorem L_cont : ∀ (D : D7) (O : Setup D) (x : ToroidalCompactificationData O.s) (c : O.s.Comp) (σ : D.what₂.LL →+* ℂ) (τ : D.what₂.Tau) (i : Fin O.N)
    (ch : GlobalTheory.AlgChart (O.var c).str σ (O.var c).dim) (y : GlobalTheory.TrueGeo.Pts (O.var c) σ), y ∈ ch.e.source → y ∈ offBd O.Φ c σ →
    ∃ U ∈ 𝓝 (ch.e y), ContinuousOn (GlobalTheory.HeightParts.psi O x c σ τ i ∘ ch.e.symm) U := GlobalTheory.T.height_green_continuous_off_boundary

theorem L_lim : GlobalTheory.HeightParts.KernelSt → ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (p : Y ⟶ ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k) (σ : k →+* ℂ) (d : ℕ)
    [SmoothOfRelativeDimension d p] (a : ChartForm p σ d) (E : ChartMap p σ d), IsKaehlerForm (GlobalTheory.AnRead.all p σ d) a →
    IsExph a E → ∀ (f : GlobalTheory.CxPts p σ → ℝ) (c : GlobalTheory.AlgChart p σ d) (y : GlobalTheory.CxPts p σ), y ∈ c.e.source →
    (∃ U ∈ 𝓝 (c.e y), ContinuousOn (f ∘ c.e.symm) U) → Tendsto (fun t => rho a E f y t) (𝓝[>] 0) (𝓝 (f y)) := GlobalTheory.T.kaehler_exponential_chart_limit

theorem L_logm : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.CovHt.HypothesesH → GlobalTheory.HeightParts.KernelSt → GlobalTheory.HeightParts.OnCore fun _ O _ P =>
    ∃ C t₀ : ℝ, 0 < C ∧ 0 < t₀ ∧ ∀ t : ℝ, 0 < t → t ≤ t₀ → ∀ (c : O.s.Comp) (σ : _ →+* ℂ)
      (ch : GlobalTheory.AlgChart (O.var c).str σ (O.var c).dim) (y : GlobalTheory.TrueGeo.Pts (O.var c) σ), y ∈ ch.e.source →
      Integrable (fun ξ => Real.log (O.met.r c σ (P.exph c σ ch y (t • ξ))) * GlobalTheory.ChernReg.cutoff (P.om c σ ch y ξ)) ∧
      rhoIn (P.om c σ) (P.exph c σ) (fun z => Real.log (O.met.r c σ z)) ch y t ≤ Real.log (C * Real.log (1 / t)) := GlobalTheory.T.log_metric_cutoff_integrable

theorem lowSt : Hypotheses2 → HypothesesH → KernelSt → SizeSt → ConstSt → LowSt := by
  intro h2 hH hK hS hC D O x P hcw hf hr
  obtain ⟨C₀, hC₀, hS'⟩ := hS D O x P hcw hf hr
  obtain ⟨-, hKn, hδ, hreg⟩ := hC D O x P hcw hf hr
  obtain ⟨C₁, t₁, hC₁, ht₁, hlog⟩ := L_logm h2 hH hK D O x P hcw hf hr
  have hcore : O.Core := ⟨x, P, hcw⟩
  set t₀ := min (min t₁ (P.δ / 2)) (Real.exp (-Real.exp 1)) with ht₀
  have ht₀p : 0 < t₀ := lt_min (lt_min ht₁ (by linarith)) (Real.exp_pos _)
  refine ⟨C₀ + P.K * t₀ ^ 2 + C₀ * (1 + |Real.log C₁|), t₀, by positivity, ht₀p, fun t ht htt c σ τ i hi y => ?_⟩
  have htt1 : t ≤ t₁ := htt.trans ((min_le_left _ _).trans (min_le_left _ _))
  have httδ : t < P.δ := htt.trans_lt (((min_le_left _ _).trans (min_le_right _ _)).trans_lt (by linarith))
  have htte : t ≤ Real.exp (-Real.exp 1) := htt.trans (min_le_right _ _)
  set ψ := GlobalTheory.HeightParts.psi O x c σ τ i with hψ
  have hψle : ∀ z, ψ z ≤ C₀ := fun z => by
    by_cases hz : z ∈ offBd O.Φ c σ
    · exact (hS' c σ τ i z hz).2
    · rw [hψ, L_zero D O x c σ τ i z hz]; exact hC₀
  have hψge : ∀ z, -(C₀ * Real.log (O.met.r c σ z)) ≤ ψ z := fun z => by
    by_cases hz : z ∈ offBd O.Φ c σ
    · exact (hS' c σ τ i z hz).1
    · rw [hψ, L_zero D O x c σ τ i z hz]
      have : 0 ≤ Real.log (O.met.r c σ z) :=
        Real.log_nonneg (le_trans (by linarith [Real.add_one_le_exp (1 : ℝ)]) (hcore.exp_le_r c σ z))
      nlinarith
  have e : P.regFund c σ τ i t y = rho (P.om c σ) (P.exph c σ) ψ y t + P.K * t ^ 2 := by
    rw [PolDat.regFund, if_pos hi]
  have hy₀ := (GlobalTheory.AlgChart.exists_mem_source (D := (O.var c).dim) y).choose_spec
  have ha := P.om_kaehler c σ
  have hq := continuous_and_smul ha hy₀
  have hpd := ha.2 _ y hy₀

  have hL1 : Real.exp 1 ≤ Real.log (1 / t) := by
    rw [one_div, Real.log_inv, le_neg]
    exact (Real.log_le_log ht htte).trans_eq (Real.log_exp _)
  have hLpos : 0 < Real.log (1 / t) := lt_of_lt_of_le (Real.exp_pos 1) hL1
  have hLL : 1 ≤ Real.log (Real.log (1 / t)) := by
    have := Real.log_le_log (Real.exp_pos 1) hL1; rwa [Real.log_exp] at this
  refine ⟨?_, ?_, fun hyo => ?_⟩
  ·
    obtain ⟨hint, hmean⟩ := hlog t ht htt1 c σ _ y hy₀
    have hm := le_mean_of hq.1 hq.2 hpd hC₀ hint hmean (fun ξ => hψge _)
    have hm' : min 0 (-(C₀ * Real.log (C₁ * Real.log (1 / t)))) ≤ rho (P.om c σ) (P.exph c σ) ψ y t := hm
    rw [e]
    rw [Real.log_mul hC₁.ne' hLpos.ne'] at hm'
    have hab : Real.log C₁ ≤ |Real.log C₁| * Real.log (Real.log (1 / t)) :=
      (le_abs_self _).trans (le_mul_of_one_le_right (abs_nonneg _) hLL)
    have h3 : -((C₀ + P.K * t₀ ^ 2 + C₀ * (1 + |Real.log C₁|)) * Real.log (Real.log (1 / t))) ≤
        min 0 (-(C₀ * (Real.log C₁ + Real.log (Real.log (1 / t))))) := by
      have hLL0 : 0 ≤ Real.log (Real.log (1 / t)) := by linarith
      have hK0 : 0 ≤ P.K * t₀ ^ 2 := by positivity
      refine le_min ?_ ?_
      · have : 0 ≤ (C₀ + P.K * t₀ ^ 2 + C₀ * (1 + |Real.log C₁|)) * Real.log (Real.log (1 / t)) := by positivity
        linarith
      · have h4 := mul_le_mul_of_nonneg_left hab hC₀
        nlinarith [mul_nonneg hK0 hLL0, mul_nonneg hC₀ hLL0]
    have : 0 ≤ P.K * t ^ 2 := by positivity
    linarith
  ·
    rw [e]
    have h1 : rho (P.om c σ) (P.exph c σ) ψ y t ≤ C₀ := mean_le_of_le hq.1 hq.2 hpd hC₀ fun ξ => hψle _
    have h2 : P.K * t ^ 2 ≤ P.K * t₀ ^ 2 := by gcongr
    have h3 : 0 ≤ C₀ * (1 + |Real.log C₁|) := by positivity
    linarith
  ·
    rw [e]
    have hmono := (hreg c σ τ i hi).mono y
    obtain ⟨U, hU, hcU⟩ := L_cont D O x c σ τ i _ y hy₀ hyo
    have hlim := L_lim hK _ _ _ _ _ _ _ ha (P.exph_is c σ) ψ _ y hy₀ ⟨U, hU, hcU⟩
    have hlim' : Tendsto (fun s => rho (P.om c σ) (P.exph c σ) ψ y s + P.K * s ^ 2) (𝓝[>] 0) (𝓝 (ψ y + P.K * 0 ^ 2)) :=
      hlim.add ((continuous_const.mul (continuous_pow 2)).tendsto 0 |>.mono_left nhdsWithin_le_nhds)
    rw [zero_pow two_ne_zero, mul_zero, add_zero] at hlim'
    refine le_of_tendsto hlim' ?_
    filter_upwards [Ioo_mem_nhdsGT ht] with s hs
    exact hmono ⟨hs.1, hs.2.trans httδ⟩ ⟨ht, httδ⟩ hs.2.le

end GlobalTheory.RegLow
