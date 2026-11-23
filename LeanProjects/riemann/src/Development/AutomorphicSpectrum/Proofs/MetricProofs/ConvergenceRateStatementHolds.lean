import Mathlib
import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
import ReciprocityTheory.AnalyticForms.LeviForms.TailCut
import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes
import ReciprocityTheory.AnalyticForms.PotentialTheory.MaMeasure
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MaMeasureEqOfConst
import Development.AutomorphicSpectrum.Proofs.MetricProofs.TailBoundStatementHolds
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.Giv.Rate

theorem mInt_congr_φ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (Φ Ψ : Fin e → LocPot X) (h : ∀ i, (Φ i).φ = (Ψ i).φ) (g : X → ℝ) :
    mInt A Φ g = mInt A Ψ g := by
  have hD : locDens A Φ = locDens A Ψ := by
    funext j y
    simp only [locDens, h]
  unfold mInt integralWith
  rw [hD]

theorem maMeasure_univ_eq {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X] (A : FinHolAtlas e X) (Θ : LocPot X)
    (th : Fin e → LocPot X) (u : Fin e → X → ℝ) (hΘ : IsPotential A Θ)
    (hth : ∀ i, IsPotential A (th i)) (hu : ∀ i, A.Smooth (u i))
    (hP : ∀ i, IsPotential A (th i + LocPot.ofFun (u i) + Θ))
    (hPsh : ∀ i, IsPsh A (th i + LocPot.ofFun (u i) + Θ)) :
    maMeasure A (fun i => th i + LocPot.ofFun (u i) + Θ) Set.univ =
      ENNReal.ofReal (mInt A (fun i => th i + Θ) (fun _ => 1)) := by
  obtain ⟨hfin, hg⟩ := maMeasure_thm A _ hP hPsh
  have hI : Integrable (fun _ : X => (1 : ℝ)) (maMeasure A (fun i => th i + LocPot.ofFun (u i) + Θ)) :=
    integrable_const 1
  have hM := (hg _ measurable_const).1.2 hI
  have h2 := (hg _ measurable_const).2 hM
  have h3 : mInt A (fun i => th i + LocPot.ofFun (u i) + Θ) (fun _ => 1) =
      mInt A (fun i => (th i + Θ) + LocPot.ofFun (u i)) (fun _ => 1) := by
    refine mInt_congr_φ A _ _ (fun i => ?_) _
    funext x y
    show (th i).φ x y + u i y + Θ.φ x y = (th i).φ x y + Θ.φ x y + u i y
    ring
  rw [massIndep A (fun i => th i + Θ) u (fun i => isPotentialAdd A _ _ (hth i) hΘ) hu] at h3
  rw [← h3, h2, integral_const, smul_eq_mul, mul_one, ofReal_measureReal (measure_ne_top _ _)]

end GlobalTheory.CompanionTheory.Ar.Giv.Rate

namespace GlobalTheory.CompanionTheory.Ar.Giv

open GlobalTheory.CompanionTheory.Ar.Giv.Rate in

theorem convergenceRate_holds : ConvergenceRateStatement := by
  intro e X _ _ _ _ _ A Θ L s n m W hΘ hpos hL hS hSNC hnorm th ph phT th₀ ph₀ phT₀ C₅ C t₀
    hW hR hW₀ hR₀
  obtain ⟨K, t₂, ht₂, -, hT⟩ := tail_uniform tailBound_holds A Θ L s m W hΘ hpos hL hS hSNC hnorm
    th ph phT C₅ C t₀ hW hR
  have ht₀ : 0 < t₀ := hR₀.1
  refine ⟨(3 + |C|) * |mInt A (fun i => th i + Θ) (fun _ => 1)| + (|C| + |C₅|) * |K|,
    min t₂ (min t₀ (Real.exp (-Real.exp 1))), lt_min ht₂ (lt_min ht₀ (Real.exp_pos _)), ?_⟩
  intro t t' ht' htt' ht1 c
  have htpos : 0 < t := ht'.trans_le htt'
  have ht_t₂ : t ≤ t₂ := ht1.trans (min_le_left _ _)
  have ht_t₀ : t ≤ t₀ := ht1.trans ((min_le_right _ _).trans (min_le_left _ _))
  have ht_e : t ≤ Real.exp (-Real.exp 1) := ht1.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hlogt : Real.log (1 / t) = -Real.log t := by rw [one_div, Real.log_inv]
  have hℓe : Real.exp 1 ≤ Real.log (1 / t) := by
    have := Real.log_le_log htpos ht_e
    rw [Real.log_exp] at this
    linarith
  have he2 : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ, Real.log (1 / t) = ℓ := ⟨_, rfl⟩
  rw [hℓ] at hℓe hlogt
  rw [hℓ]
  have hℓpos : 0 < ℓ := by linarith
  have hlogℓ : 1 ≤ Real.log ℓ := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hℓe
  have hℓu : ∀ u, 0 < u → u ≤ t → ℓ ≤ Real.log (1 / u) := fun u hu hut =>
    hℓ ▸ Real.log_le_log (by positivity) (one_div_le_one_div_of_le hu hut)

  have heps : ∀ u, 0 < u → u ≤ t → epsT C u ≤ |C| * (Real.log ℓ / ℓ) := by
    intro u hu hut
    have hlu := hℓu u hu hut
    have hmono := Real.log_div_self_antitoneOn (Set.mem_Ici.2 hℓe) (Set.mem_Ici.2 (hℓe.trans hlu)) hlu
    have hnn : 0 ≤ Real.log (Real.log (1 / u)) / Real.log (1 / u) :=
      div_nonneg (Real.log_nonneg (by linarith)) (by linarith)
    unfold epsT
    rw [mul_div_assoc]
    calc C * (Real.log (Real.log (1 / u)) / Real.log (1 / u))
        ≤ |C| * (Real.log (Real.log (1 / u)) / Real.log (1 / u)) :=
          mul_le_mul_of_nonneg_right (le_abs_self C) hnn
      _ ≤ |C| * (Real.log ℓ / ℓ) := mul_le_mul_of_nonneg_left hmono (abs_nonneg C)
  have hrpow : ∀ u, 0 < u → u ≤ t → u ^ ((1 : ℝ) / 3) ≤ 3 / ℓ := by
    intro u hu hut
    refine (Real.rpow_le_rpow hu.le hut (by norm_num)).trans ?_
    rw [Real.rpow_def_of_pos htpos]
    have h3 : Real.log t * (1 / 3) = -(ℓ / 3) := by rw [hlogt]; ring
    rw [h3, Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by positivity), inv_div]
    linarith [Real.add_one_le_exp (ℓ / 3)]
  obtain ⟨q, hq⟩ : ∃ q, q = Real.log ℓ ^ 2 / ℓ := ⟨_, rfl⟩
  have hq0 : 0 ≤ q := by rw [hq]; positivity
  have hq1 : 1 / ℓ ≤ q := hq ▸ div_le_div_of_nonneg_right (by nlinarith) hℓpos.le
  have hq2 : Real.log ℓ / ℓ ≤ q := hq ▸ div_le_div_of_nonneg_right (by nlinarith) hℓpos.le
  have hsmall : ∀ u, 0 < u → u ≤ t → u ^ ((1 : ℝ) / 3) + epsT C u ≤ (3 + |C|) * q := by
    intro u hu hut
    have h1 := hrpow u hu hut
    have h2 := heps u hu hut
    have h3 : |C| * (Real.log ℓ / ℓ) ≤ |C| * q := mul_le_mul_of_nonneg_left hq2 (abs_nonneg C)
    have h4 : 3 / ℓ = 3 * (1 / ℓ) := by ring
    nlinarith

  obtain ⟨-, hCt, hat, -, -, hdt, -, -⟩ := hR₀.2.2 t htpos ht_t₀
  obtain ⟨-, hCt', hat', -, -, hdt', -, -⟩ := hR₀.2.2 t' ht' (htt'.trans ht_t₀)
  have hsw := hW₀.2.2.2
  have hin : ∀ y ∉ bdry s, rW L s y < ℓ → |phT₀ t y - phT₀ t' y| ≤ (3 + |C|) * q := by
    intro y hy hry
    have h1 := hdt y hy (by rw [hℓ]; exact hry.le)
    have h2 := hdt' y hy (hry.le.trans (hℓu t' ht' htt'))
    have h3 := hsmall t htpos le_rfl
    have h4 := hsmall t' ht' htt'
    have h5 := hat y hy
    have h6 := hat' y hy
    rw [abs_le]
    constructor <;> linarith
  have hout : ∀ y ∉ bdry s, ℓ ≤ rW L s y →
      |phT₀ t y - phT₀ t' y| ≤ (|C| + |C₅|) * Real.log (rW L s y) := by
    intro y hy hry
    have hr1 : 1 ≤ Real.log (rW L s y) := by
      rw [← Real.log_exp 1]
      exact Real.log_le_log (Real.exp_pos 1) (hℓe.trans hry)
    have h1 := hCt y
    have h2 := hCt' y
    have h5 := hat y hy
    have h6 := hat' y hy
    have h7 := (hsw y hy).1
    have h8 : C ≤ |C| * Real.log (rW L s y) := (le_abs_self C).trans (by nlinarith [abs_nonneg C])
    have h9 : C₅ * Real.log (rW L s y) ≤ |C₅| * Real.log (rW L s y) :=
      mul_le_mul_of_nonneg_right (le_abs_self C₅) (by linarith)
    rw [abs_le]
    constructor <;> nlinarith

  have hτ : ∀ i, 0 < (fun i => if c i then t else t') i ∧ (fun i => if c i then t else t') i ≤ t₂ := by
    intro i
    by_cases h : c i
    · simp only [h, if_true]; exact ⟨htpos, ht_t₂⟩
    · simp only [h]; exact ⟨ht', htt'.trans ht_t₂⟩
  obtain ⟨hPP, hTR⟩ := hT _ hτ
  obtain ⟨-, hlogR⟩ := hTR ℓ hℓe
  beta_reduce at hPP hlogR
  have hsm : ∀ i, A.Smooth (phT i (if c i then t else t')) := by
    intro i
    by_cases h : c i
    · simp only [h, if_true]; exact ((hR i).2.2 t htpos ht_t₀).1
    · simp only [h]; exact ((hR i).2.2 t' ht' (htt'.trans ht_t₀)).1
  have hmass := maMeasure_univ_eq A Θ th (fun i => phT i (if c i then t else t')) hΘ
    (fun i => (hW i).1) hsm (fun i => (hPP i).1) (fun i => (hPP i).2)
  have hnull : maMeasure A (fun i => th i + LocPot.ofFun (phT i (if c i then t else t')) + Θ)
      (bdry s) = 0 := bdry_null A L s m W hL hS hSNC _ (fun i => (hPP i).1)
  have hae := measure_eq_zero_iff_ae_notMem.1 hnull
  set μ := maMeasure A (fun i => th i + LocPot.ofFun (phT i (if c i then t else t')) + Θ) with hμ
  set M := mInt A (fun i => th i + Θ) (fun _ => (1 : ℝ)) with hM
  set k := |C| + |C₅| with hkdef
  have hk : 0 ≤ k := by positivity
  have ha : 0 ≤ (3 + |C|) * q := mul_nonneg (by positivity) hq0
  have hpt : ∀ᵐ y ∂μ, ENNReal.ofReal |phT₀ t y - phT₀ t' y| ≤
      ENNReal.ofReal ((3 + |C|) * q) + ((bdry s)ᶜ ∩ {y | ℓ ≤ rW L s y}).indicator
        (fun y => ENNReal.ofReal k * ENNReal.ofReal (Real.log (rW L s y))) y := by
    filter_upwards [hae] with y hy
    by_cases hry : ℓ ≤ rW L s y
    · rw [Set.indicator_of_mem (show y ∈ (bdry s)ᶜ ∩ {y | ℓ ≤ rW L s y} from ⟨hy, hry⟩),
        ← ENNReal.ofReal_mul hk]
      exact (ENNReal.ofReal_le_ofReal (hout y hy hry)).trans le_add_self
    · rw [Set.indicator_of_notMem (fun h => hry h.2), add_zero]
      exact ENNReal.ofReal_le_ofReal (hin y hy (not_le.1 hry))
  have hsec : ∫⁻ y, ((bdry s)ᶜ ∩ {y | ℓ ≤ rW L s y}).indicator
        (fun y => ENNReal.ofReal k * ENNReal.ofReal (Real.log (rW L s y))) y ∂μ ≤
      ENNReal.ofReal k * ENNReal.ofReal (|K| * q) := by
    refine (lintegral_indicator_le _ _).trans ?_
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    have hKq : K * Real.log ℓ ^ 2 / ℓ ≤ |K| * q := by
      rw [hq, mul_div_assoc]
      exact mul_le_mul_of_nonneg_right (le_abs_self K) (by positivity)
    gcongr
    exact hlogR.trans (ENNReal.ofReal_le_ofReal hKq)
  calc ∫⁻ y, ENNReal.ofReal |phT₀ t y - phT₀ t' y| ∂μ
      ≤ ∫⁻ y, (ENNReal.ofReal ((3 + |C|) * q) + ((bdry s)ᶜ ∩ {y | ℓ ≤ rW L s y}).indicator
          (fun y => ENNReal.ofReal k * ENNReal.ofReal (Real.log (rW L s y))) y) ∂μ :=
        lintegral_mono_ae hpt
    _ = ENNReal.ofReal ((3 + |C|) * q) * μ Set.univ + ∫⁻ y, ((bdry s)ᶜ ∩ {y | ℓ ≤ rW L s y}).indicator
          (fun y => ENNReal.ofReal k * ENNReal.ofReal (Real.log (rW L s y))) y ∂μ := by
        rw [lintegral_add_left measurable_const, lintegral_const]
    _ ≤ ENNReal.ofReal ((3 + |C|) * q) * ENNReal.ofReal |M| +
          ENNReal.ofReal k * ENNReal.ofReal (|K| * q) := by
        rw [hmass]
        gcongr
        exact le_abs_self _
    _ = ENNReal.ofReal ((3 + |C|) * q * |M| + k * (|K| * q)) := by
        rw [← ENNReal.ofReal_mul ha, ← ENNReal.ofReal_mul hk,
          ← ENNReal.ofReal_add (mul_nonneg ha (abs_nonneg _)) (mul_nonneg hk (mul_nonneg (abs_nonneg _) hq0))]
    _ ≤ ENNReal.ofReal (((3 + |C|) * |M| + k * |K|) * Real.log ℓ ^ 2 / ℓ) :=
        ENNReal.ofReal_le_ofReal (le_of_eq (by rw [hq]; ring))

end GlobalTheory.CompanionTheory.Ar.Giv
