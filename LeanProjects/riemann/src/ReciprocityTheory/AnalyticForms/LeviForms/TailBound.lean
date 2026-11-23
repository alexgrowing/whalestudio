import ReciprocityTheory.AnalyticForms.LeviForms.TailCut
import ReciprocityTheory.AnalyticForms.PotentialTheory.PLLocalStatement
import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes
import ReciprocityTheory.AnalyticForms.PotentialTheory.PotentialContDiffAt
import ReciprocityTheory.AnalyticForms.PotentialTheory.SNCAtlas
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShift
import ReciprocityTheory.AnalyticForms.LeviForms.TailBoundB

namespace ReciprocityTheory.AnForm.P

open MeasureTheory ReciprocityTheory.AnForm.M FinHolAtlas

noncomputable section

def TailTransferStatement : Prop :=
  ∀ {X : Type} [MeasurableSpace X] [TopologicalSpace X] [OpensMeasurableSpace X]
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (V : Set X), IsOpen V →
    μ.restrict V = ν.restrict V → μ Set.univ = ν Set.univ → μ Vᶜ = ν Vᶜ

theorem measure_compl_eq_of_restrict_eq {X : Type} [MeasurableSpace X] [TopologicalSpace X] [OpensMeasurableSpace X]
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (V : Set X) (hV : IsOpen V)
    (h1 : μ.restrict V = ν.restrict V) (h2 : μ Set.univ = ν Set.univ) : μ Vᶜ = ν Vᶜ := by
  have hm : MeasurableSet V := hV.measurableSet
  have hVV : μ V = ν V := by
    have := congrArg (fun m : Measure X => m Set.univ) h1
    simpa [Measure.restrict_apply MeasurableSet.univ] using this
  rw [measure_compl hm (measure_ne_top μ V), measure_compl hm (measure_ne_top ν V), hVV, h2]

theorem lintegral_log_tail_shells_le {X : Type} [MeasurableSpace X] (μ : Measure X) (ρ : X → ℝ) (K : ℝ)
    (hρ : Measurable ρ) (hK : 0 ≤ K)
    (h : ∀ R : ℝ, Real.exp 1 ≤ R → μ {y | R ≤ ρ y} ≤ ENNReal.ofReal (K * Real.log R / R))
    (R : ℝ) (hR : Real.exp 1 ≤ R) :
    ∫⁻ y in {y | R ≤ ρ y}, ENNReal.ofReal (Real.log (ρ y)) ∂μ ≤
      ENNReal.ofReal (16 * K * Real.log R ^ 2 / R) := by
  have hR0 : 0 < R := lt_of_lt_of_le (Real.exp_pos 1) hR
  have hlogR : 1 ≤ Real.log R := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hR
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2' : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9; linarith
  set ind : ℕ → X → ENNReal := fun j => Set.indicator {y | 2 ^ j * R ≤ ρ y} (fun _ => (1 : ENNReal))
    with hind
  have hmeas : ∀ c : ℝ, MeasurableSet {y | c ≤ ρ y} := fun c => measurableSet_le measurable_const hρ
  have hpt : ∀ y, R ≤ ρ y → ENNReal.ofReal (Real.log (ρ y)) ≤
      ENNReal.ofReal (Real.log R) + ENNReal.ofReal (Real.log 2) * ∑' j : ℕ, ind j y := by
    intro y hy
    have hex : ∃ N : ℕ, ρ y < 2 ^ N * R := by
      obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (ρ y / R) (by norm_num : (1:ℝ) < 2)
      exact ⟨N, by rwa [div_lt_iff₀ hR0] at hN⟩
    classical
    have hN : ρ y < 2 ^ Nat.find hex * R := Nat.find_spec hex
    have hmin : ∀ j < Nat.find hex, 2 ^ j * R ≤ ρ y := fun j hj => not_lt.1 (Nat.find_min hex hj)
    have hsum : ((Nat.find hex : ℕ) : ENNReal) ≤ ∑' j : ℕ, ind j y := by
      calc ((Nat.find hex : ℕ) : ENNReal) = ∑ j ∈ Finset.range (Nat.find hex), ind j y := by
            rw [Finset.sum_congr rfl (fun j hj => Set.indicator_of_mem
              (show y ∈ {y | 2 ^ j * R ≤ ρ y} from hmin j (Finset.mem_range.1 hj)) _)]
            simp
        _ ≤ _ := ENNReal.sum_le_tsum _
    have hρpos : 0 < ρ y := lt_of_lt_of_le hR0 hy
    have hlog : Real.log (ρ y) ≤ Real.log R + Real.log 2 * (Nat.find hex : ℕ) := by
      have := Real.log_lt_log hρpos hN
      rw [Real.log_mul (by positivity) hR0.ne', Real.log_pow] at this
      linarith
    calc ENNReal.ofReal (Real.log (ρ y))
        ≤ ENNReal.ofReal (Real.log R + Real.log 2 * (Nat.find hex : ℕ)) :=
          ENNReal.ofReal_le_ofReal hlog
      _ = ENNReal.ofReal (Real.log R) + ENNReal.ofReal (Real.log 2) * ((Nat.find hex : ℕ) : ENNReal) := by
          rw [ENNReal.ofReal_add (by linarith) (by positivity), ENNReal.ofReal_mul hlog2.le]
          simp
      _ ≤ _ := by gcongr
  set S := {y | R ≤ ρ y}
  have hS := hmeas R

  have hterm : ∀ j : ℕ, μ {y | 2 ^ j * R ≤ ρ y} ≤
      ENNReal.ofReal (K * Real.log R / R * ((j + 1) * (1 / 2 : ℝ) ^ j)) := by
    intro j
    have h2j : Real.exp 1 ≤ 2 ^ j * R := le_trans hR (le_mul_of_one_le_left hR0.le (one_le_pow₀ (by norm_num)))
    refine (h _ h2j).trans (ENNReal.ofReal_le_ofReal ?_)
    have hlj : Real.log (2 ^ j * R) ≤ (j + 1) * Real.log R := by
      rw [Real.log_mul (by positivity) hR0.ne', Real.log_pow]
      nlinarith
    have hpos : (0 : ℝ) < 2 ^ j * R := by positivity
    rw [div_le_iff₀ hpos]
    have : K * Real.log R / R * ((↑j + 1) * (1 / 2) ^ j) * (2 ^ j * R) = K * ((j + 1) * Real.log R) := by
      rw [one_div_pow]; field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_left hlj hK
  have hsumm : Summable (fun j : ℕ => ((j : ℝ) + 1) * (1 / 2 : ℝ) ^ j) := by
    have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 (r := (1 / 2 : ℝ)) (by norm_num)
    have h2 := summable_geometric_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
    simpa [add_mul] using h1.add h2
  have htsum : ∑' j : ℕ, ((j : ℝ) + 1) * (1 / 2 : ℝ) ^ j = 4 := by
    have h1 := tsum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℝ) (r := 1 / 2) (by norm_num)
    have h2 := tsum_geometric_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
    have hs1 : Summable (fun j : ℕ => (j : ℝ) * (1 / 2 : ℝ) ^ j) := by
      simpa using summable_pow_mul_geometric_of_norm_lt_one 1 (r := (1 / 2 : ℝ)) (by norm_num)
    have hs2 := summable_geometric_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
    simp only [add_mul, one_mul]
    rw [hs1.tsum_add hs2, h1, h2]
    norm_num
  have hKR : 0 ≤ K * Real.log R / R := by positivity
  calc ∫⁻ y in S, ENNReal.ofReal (Real.log (ρ y)) ∂μ
      ≤ ∫⁻ y in S, (ENNReal.ofReal (Real.log R) + ENNReal.ofReal (Real.log 2) * ∑' j : ℕ, ind j y) ∂μ :=
        lintegral_mono_ae ((ae_restrict_iff' hS).2 (Filter.Eventually.of_forall hpt))
    _ = ENNReal.ofReal (Real.log R) * μ S + ENNReal.ofReal (Real.log 2) * ∑' j : ℕ, ∫⁻ y in S, ind j y ∂μ := by
        rw [lintegral_add_left measurable_const, lintegral_const, Measure.restrict_apply MeasurableSet.univ,
          Set.univ_inter, lintegral_const_mul _ (Measurable.ennreal_tsum fun j =>
            (measurable_const.indicator (hmeas _))), lintegral_tsum fun j =>
            (measurable_const.indicator (hmeas _)).aemeasurable]
    _ ≤ ENNReal.ofReal (Real.log R) * ENNReal.ofReal (K * Real.log R / R) +
          ENNReal.ofReal (Real.log 2) * ∑' j : ℕ,
            ENNReal.ofReal (K * Real.log R / R * ((j + 1) * (1 / 2 : ℝ) ^ j)) := by
        gcongr with j
        · exact h R hR
        · rw [hind, lintegral_indicator_const (hmeas _), one_mul, Measure.restrict_apply (hmeas _)]
          exact (measure_mono Set.inter_subset_left).trans (hterm j)
    _ = ENNReal.ofReal (Real.log R * (K * Real.log R / R) + Real.log 2 * (K * Real.log R / R * 4)) := by
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity) (hsumm.mul_left _), tsum_mul_left,
          htsum, ← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_mul hlog2.le,
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ ENNReal.ofReal (16 * K * Real.log R ^ 2 / R) := by
        apply ENNReal.ofReal_le_ofReal
        have e1 : Real.log R * (K * Real.log R / R) = K * Real.log R ^ 2 / R := by ring
        have e2 : Real.log 2 * (K * Real.log R / R * 4) ≤ 4 * (K * Real.log R ^ 2 / R) := by
          have : Real.log 2 * Real.log R ≤ Real.log R ^ 2 := by nlinarith
          have h3 : Real.log 2 * (K * Real.log R / R * 4) = 4 * (K / R) * (Real.log 2 * Real.log R) := by ring
          have h4 : 4 * (K * Real.log R ^ 2 / R) = 4 * (K / R) * Real.log R ^ 2 := by ring
          rw [h3, h4]; gcongr
        have e3 : 0 ≤ K * Real.log R ^ 2 / R := by positivity
        have e4 : 16 * K * Real.log R ^ 2 / R = 16 * (K * Real.log R ^ 2 / R) := by ring
        rw [e1, e4]; linarith

theorem tail_transfer : TailTransferStatement :=
  fun μ ν _ _ V hV h1 h2 => measure_compl_eq_of_restrict_eq μ ν V hV h1 h2

def TailChernBoundStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X)
    (Θ L : LocPot X), IsPotential A Θ → IsPosPot A Θ → IsPotential A L →
      ∃ C : ℝ, 0 ≤ C ∧ IsPsh A (Θ.rsmul C + L) ∧ IsPsh A (Θ.rsmul C + L.rsmul (-1))

theorem tail_chern_bound : TailChernBoundStatement :=
  fun A Θ L hΘ hΘp hL => TailBoundAlt.exists_psh_chern_bound A Θ L hΘ hΘp hL

def EnergyBoundStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X]
    [BorelSpace X] (A : FinHolAtlas e X) (Θ : Fin e → LocPot X) (L : LocPot X) (s : X → X → ℂ)
    {n : ℕ} (m : Fin n → ℕ) (W : Fin n → Set X), (∀ i, IsPotential A (Θ i)) →
    (∀ i, IsPosPot A (Θ i)) → IsPotential A L → IsSection A L s → IsSNC A L s m W →
    (∀ y, logNormSec L s y ≤ 0) →
    ∃ C : ℝ, ∀ (M : ℝ) (v : Fin e → X → ℝ), 0 ≤ M → (∀ i, A.Smooth (v i)) →
      (∀ i, IsPsh A (Θ i + LocPot.ofFun (v i))) → (∀ i y, -M - 1 ≤ v i y ∧ v i y ≤ 0) →
        ∫⁻ y in (bdry s)ᶜ, ENNReal.ofReal (rW L s y)
            ∂maMeasure A (fun i => Θ i + LocPot.ofFun (v i)) ≤
          ENNReal.ofReal (C * (M + 1))

def TailShellsStatement : Prop :=
  ∀ {X : Type} [MeasurableSpace X] (μ : Measure X) (ρ : X → ℝ) (K : ℝ), Measurable ρ → 0 ≤ K →
    (∀ R : ℝ, Real.exp 1 ≤ R → μ {y | R ≤ ρ y} ≤ ENNReal.ofReal (K * Real.log R / R)) →
      ∀ R : ℝ, Real.exp 1 ≤ R →
        ∫⁻ y in {y | R ≤ ρ y}, ENNReal.ofReal (Real.log (ρ y)) ∂μ ≤
          ENNReal.ofReal (16 * K * Real.log R ^ 2 / R)

theorem tail_shells : TailShellsStatement :=
  fun μ ρ K hρ hK h R hR => lintegral_log_tail_shells_le μ ρ K hρ hK h R hR

end

end ReciprocityTheory.AnForm.P
