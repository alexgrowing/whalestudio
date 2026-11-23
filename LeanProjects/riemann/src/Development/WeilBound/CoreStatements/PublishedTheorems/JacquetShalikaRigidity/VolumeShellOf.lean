import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.ColumnConjugationMeasure

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace ShellSummation

set_option synthInstance.maxHeartbeats 400000

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {k : ℕ}

omit [IsTotallyComplex E] in
theorem uu_eq_one {u : GA E k} {j : ℕ} (hj : k ≤ j) (hu : UU j u) : u = 1 :=
  Units.ext <| Matrix.ext fun i c => by rw [hu.2.2 i c (by omega), Units.val_one]

omit [IsTotallyComplex E] in

theorem map_wd (μ : Measure (GA E k)) [μ.IsMulLeftInvariant] (β : GA E k → ℝ≥0∞) (z : GA E k) :
    Measure.map (fun g => z * g) (μ.withDensity β) = μ.withDensity (fun g => β (z⁻¹ * g)) := by
  ext s hs
  have key := lintegral_mul_left_eq_self (μ := μ) (s.indicator fun g => β (z⁻¹ * g)) z
  rw [Measure.map_apply (measurable_const_mul z) hs, withDensity_apply _ (measurable_const_mul z hs),
    withDensity_apply _ hs, ← lintegral_indicator (measurable_const_mul z hs), ← lintegral_indicator hs, ← key]
  refine lintegral_congr fun x => ?_
  by_cases hx : z * x ∈ s
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (show x ∈ (fun g => z * g) ⁻¹' s from hx),
      inv_mul_cancel_left]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (show x ∉ (fun g => z * g) ⁻¹' s from hx)]

omit [IsTotallyComplex E] in

theorem wt_shift {ν : Measure (GA E k)} (β : GA E k → ℝ≥0∞) (hβ : IsWt ν β) (z : GA E k)
    (hz : ∀ g, z * g = g * z) : IsWt ν (fun g => β (z⁻¹ * g)) := by
  refine ⟨hβ.1.comp (measurable_const_mul _), fun g => ?_⟩
  have hc : ∀ h : GA E k, z⁻¹ * (h * g) = h * (z⁻¹ * g) := fun h => by
    have : z⁻¹ * h = h * z⁻¹ := ((Commute.inv_left (hz h))).eq
    rw [← mul_assoc, this, mul_assoc]
  simp only [hc]
  exact hβ.2 _

omit [IsTotallyComplex E] [NumberField E] in
variable (E k) in

def shell (a : ℝ) (j : ℤ) : Set (GA E k) :=
  {g | Real.exp (a * j) ≤ Dt g ∧ Dt g < Real.exp (a * j) * Real.exp a}

theorem exists_shell (a D : ℝ) (ha : 0 < a) (hD : 0 < D) :
    ∃ j : ℤ, Real.exp (a * j) ≤ D ∧ D < Real.exp (a * j) * Real.exp a := by
  refine ⟨⌊Real.log D / a⌋, ?_, ?_⟩
  · have h := Int.floor_le (Real.log D / a)
    rw [le_div_iff₀ ha] at h
    calc Real.exp (a * ⌊Real.log D / a⌋) ≤ Real.exp (Real.log D) :=
          Real.exp_le_exp.mpr (by linarith [mul_comm a (⌊Real.log D / a⌋ : ℝ)])
      _ = D := Real.exp_log hD
  · have h := Int.lt_floor_add_one (Real.log D / a)
    rw [div_lt_iff₀ ha] at h
    rw [← Real.exp_add]
    calc D = Real.exp (Real.log D) := (Real.exp_log hD).symm
      _ < _ := Real.exp_lt_exp.mpr (by linarith [mul_comm a (⌊Real.log D / a⌋ : ℝ)])

theorem min_le_bnd (a ε D : ℝ) (ha : 0 < a) (hε : 0 < ε) (hD : 0 < D) (j : ℤ)
    (h1 : Real.exp (a * j) ≤ D) (h2 : D < Real.exp (a * j) * Real.exp a) :
    min D D⁻¹ ^ ε ≤ Real.exp (a * ε) * Real.exp (-(a * ε) * |(j : ℝ)|) := by
  have key : min D D⁻¹ ≤ Real.exp (a - a * |(j : ℝ)|) := by
    rcases le_or_gt 0 (j : ℝ) with hj | hj
    · rw [abs_of_nonneg hj]
      calc min D D⁻¹ ≤ D⁻¹ := min_le_right _ _
        _ ≤ (Real.exp (a * j))⁻¹ := inv_anti₀ (Real.exp_pos _) h1
        _ = Real.exp (-(a * j)) := (Real.exp_neg _).symm
        _ ≤ Real.exp (a - a * j) := Real.exp_le_exp.mpr (by linarith)
    · rw [abs_of_neg hj]
      calc min D D⁻¹ ≤ D := min_le_left _ _
        _ ≤ Real.exp (a * j) * Real.exp a := h2.le
        _ = Real.exp (a - a * -(j : ℝ)) := by rw [← Real.exp_add]; congr 1; ring
  calc min D D⁻¹ ^ ε ≤ Real.exp (a - a * |(j : ℝ)|) ^ ε :=
        Real.rpow_le_rpow (le_min hD.le (inv_nonneg.mpr hD.le)) key hε.le
    _ = Real.exp ((a - a * |(j : ℝ)|) * ε) := (Real.exp_mul _ _).symm
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem summ (c : ℝ) (hc : 0 < c) : Summable fun j : ℤ => Real.exp (-c * |(j : ℝ)|) := by
  have hr : Real.exp (-c) < 1 := by
    rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith)
  have hg : Summable fun n : ℕ => Real.exp (-c * n) :=
    (summable_geometric_of_lt_one (Real.exp_pos _).le hr).congr fun n => by
      rw [← Real.exp_nat_mul, mul_comm]
  refine Summable.of_nat_of_neg ?_ ?_
  · simpa using hg
  · simpa using hg

end ShellSummation

open ShellSummation in
set_option synthInstance.maxHeartbeats 400000 in
theorem volume_shell_of : Q1 → Q2 → D0 → N3 → W0 → V1 := by
  intro hQ1 hQ2 hD0 hN3 hW0 E _ _ _ k μ _ hk β hβ
  obtain ⟨hpos, hmul, hcont, hrat, -, -, hcen, hcomm, -⟩ := hD0 E k
  obtain ⟨hsf, hinv, hae⟩ := (hN3 E k).2.1 k le_rfl
  have hH : ∀ᵐ h ∂nuB E k k, h ∈ {x : GA E k | ∃ γ, ratGL E k γ = x} := by
    filter_upwards [hae] with h hh'
    obtain ⟨γ, u, -, hu, hh⟩ := hh'
    rw [hh, uu_eq_one le_rfl hu, mul_one]
    exact ⟨γ, rfl⟩
  have T1 : ∀ β₁, IsWt (nuB E k k) β₁ → ∀ Φ : GA E k → ℝ≥0∞, Measurable Φ → RatInv Φ →
      ∫⁻ g, Φ g ∂μ.withDensity β = ∫⁻ g, Φ g ∂μ.withDensity β₁ := by
    intro β₁ hβ₁ Φ hΦ hΦi
    have := hQ1 (GA E k) μ (nuB E k k) (Measure.dirac 1) {x : GA E k | ∃ γ, ratGL E k γ = x} β β₁ hinv hH hβ
      hβ₁.1 (fun g => by simp only [lintegral_dirac, inv_one, one_mul]; exact hβ₁.2 g) Φ hΦ
      (by rintro _ ⟨γ, rfl⟩ g; exact hΦi γ g)
    rw [this]
    simp only [lintegral_dirac, one_mul]
  have T2 : ∀ β₁, IsWt (nuB E k k) β₁ → ∀ Φ : GA E k → ℂ, Measurable Φ → RatInv Φ →
      Integrable Φ (μ.withDensity β) → ∫ g, Φ g ∂μ.withDensity β = ∫ g, Φ g ∂μ.withDensity β₁ := by
    intro β₁ hβ₁ Φ hΦ hΦi hint
    have := (hQ2 (GA E k) μ (nuB E k k) (Measure.dirac 1) {x : GA E k | ∃ γ, ratGL E k γ = x} β β₁ hinv hH hβ
      hβ₁.1 (fun g => by simp only [lintegral_dirac, inv_one, one_mul]; exact hβ₁.2 g) Φ hΦ
      (by rintro _ ⟨γ, rfl⟩ g; exact hΦi γ g) hint).2
    rw [this]
    simp only [integral_dirac, one_mul]
  have hshift : ∀ t, IsWt (nuB E k k) (fun g => β ((splitCentre E k t)⁻¹ * g)) := fun t =>
    wt_shift β hβ _ (hcomm t)
  have P1 : ∀ (t : ℝ) (Φ : GA E k → ℝ≥0∞), Measurable Φ → RatInv Φ →
      ∫⁻ g, Φ (splitCentre E k t * g) ∂μ.withDensity β = ∫⁻ g, Φ g ∂μ.withDensity β := by
    intro t Φ hΦ hΦi
    rw [T1 _ (hshift t) Φ hΦ hΦi, ← map_wd μ β (splitCentre E k t),
      lintegral_map hΦ (measurable_const_mul _)]
  have P2 : ∀ (t : ℝ) (Φ : GA E k → ℂ), Measurable Φ → RatInv Φ → Integrable Φ (μ.withDensity β) →
      ∫ g, Φ (splitCentre E k t * g) ∂μ.withDensity β = ∫ g, Φ g ∂μ.withDensity β := by
    intro t Φ hΦ hΦi hint
    rw [T2 _ (hshift t) Φ hΦ hΦi hint, ← map_wd μ β (splitCentre E k t),
      integral_map (measurable_const_mul _).aemeasurable hΦ.aestronglyMeasurable]
  refine ⟨P1, P2, fun ε hε => ?_⟩
  obtain ⟨a, ha, hcen'⟩ : ∃ a : ℝ, 0 < a ∧ ∀ t, Dt (splitCentre E k t) = Real.exp (a * t) :=
    ⟨_, mul_pos (Nat.cast_pos.mpr (by omega)) (Nat.cast_pos.mpr Module.finrank_pos), hcen⟩
  have hD : Measurable (Dt : GA E k → ℝ) := hcont.measurable
  have hz : ∀ t g, Dt (splitCentre E k t * g) = Real.exp (a * t) * Dt g := fun t g => by
    rw [hmul, hcen']
  have hband : MeasurableSet (band E k) := by
    rw [show band E k = {g | 1 ≤ Dt g} ∩ {g | Dt g < Dt (splitCentre E k 1)} from rfl]
    exact (measurableSet_le measurable_const hD).inter (measurableSet_lt hD measurable_const)
  have hS : ∀ j, MeasurableSet (shell E k a j) := fun j => by
    rw [show shell E k a j = {g | Real.exp (a * j) ≤ Dt g} ∩ {g | Dt g < Real.exp (a * j) * Real.exp a} from rfl]
    exact (measurableSet_le measurable_const hD).inter (measurableSet_lt hD measurable_const)
  have hBfin : μ.withDensity β (band E k) < ∞ := (hW0 E k μ hk).2 β hβ
  have hSμ : ∀ j, μ.withDensity β (shell E k a j) ≤ μ.withDensity β (band E k) := by
    intro j
    have hP := P1 (-(j : ℝ)) ((band E k).indicator 1) (measurable_one.indicator hband) (by
      intro γ g
      have hmem : ratGL E k γ * g ∈ band E k ↔ g ∈ band E k := by
        simp only [band, Set.mem_ofPred_eq, hmul, hrat, one_mul]
      by_cases hg : g ∈ band E k
      · rw [Set.indicator_of_mem hg, Set.indicator_of_mem (hmem.2 hg)]; rfl
      · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem (fun h => hg (hmem.1 h))])
    rw [lintegral_indicator_one hband] at hP
    rw [← hP, ← lintegral_indicator_one (hS j)]
    refine lintegral_mono fun g => ?_
    refine Set.indicator_le (g := fun g => (band E k).indicator 1 (splitCentre E k (-(j : ℝ)) * g))
      (fun g hg => ?_) g
    simp only [shell, Set.mem_ofPred_eq] at hg
    obtain ⟨h1, h2⟩ := hg
    have e1 : Real.exp (a * -(j : ℝ)) * Real.exp (a * j) = 1 := by
      rw [← Real.exp_add, show a * -(j : ℝ) + a * j = 0 by ring, Real.exp_zero]
    have e0 : 0 < Real.exp (a * -(j : ℝ)) := Real.exp_pos _
    have hmem : splitCentre E k (-(j : ℝ)) * g ∈ band E k := by
      show 1 ≤ Dt _ ∧ Dt _ < Dt (splitCentre E k 1)
      rw [hz, hcen', mul_one]
      constructor
      · have := mul_le_mul_of_nonneg_left h1 e0.le
        linarith
      · have := mul_lt_mul_of_pos_left h2 e0
        rw [← mul_assoc, e1, one_mul] at this
        exact this
    rw [Set.indicator_of_mem hmem]
    exact le_rfl
  have hf : Measurable fun g : GA E k => min (Dt g) (Dt g)⁻¹ ^ ε := (hD.min hD.inv).pow_const ε
  have hsum := (summ (a * ε) (mul_pos ha hε)).mul_left (Real.exp (a * ε))
  have hnn : ∀ j : ℤ, 0 ≤ Real.exp (a * ε) * Real.exp (-(a * ε) * |(j : ℝ)|) := fun j => by positivity
  refine ⟨hf.aestronglyMeasurable, ?_⟩
  rw [HasFiniteIntegral]
  calc ∫⁻ g, ‖min (Dt g) (Dt g)⁻¹ ^ ε‖ₑ ∂μ.withDensity β
      ≤ ∫⁻ g, ∑' j : ℤ, (shell E k a j).indicator
          (fun _ => ENNReal.ofReal (Real.exp (a * ε) * Real.exp (-(a * ε) * |(j : ℝ)|))) g ∂μ.withDensity β := by
        refine lintegral_mono fun g => ?_
        obtain ⟨j, h1, h2⟩ := exists_shell a (Dt g) ha (hpos g)
        have hmem : g ∈ shell E k a j := by simp only [shell, Set.mem_ofPred_eq]; exact ⟨h1, h2⟩
        calc ‖min (Dt g) (Dt g)⁻¹ ^ ε‖ₑ = ENNReal.ofReal (min (Dt g) (Dt g)⁻¹ ^ ε) :=
              Real.enorm_eq_ofReal (Real.rpow_nonneg (le_min (hpos g).le (inv_nonneg.mpr (hpos g).le)) ε)
          _ ≤ ENNReal.ofReal (Real.exp (a * ε) * Real.exp (-(a * ε) * |(j : ℝ)|)) :=
              ENNReal.ofReal_le_ofReal (min_le_bnd a ε (Dt g) ha hε (hpos g) j h1 h2)
          _ = (shell E k a j).indicator
                (fun _ => ENNReal.ofReal (Real.exp (a * ε) * Real.exp (-(a * ε) * |(j : ℝ)|))) g :=
              by rw [Set.indicator_of_mem hmem]
          _ ≤ _ := ENNReal.le_tsum (f := fun j : ℤ => (shell E k a j).indicator
                (fun _ => ENNReal.ofReal (Real.exp (a * ε) * Real.exp (-(a * ε) * |(j : ℝ)|))) g) j
    _ = ∑' j : ℤ, ENNReal.ofReal (Real.exp (a * ε) * Real.exp (-(a * ε) * |(j : ℝ)|)) *
          μ.withDensity β (shell E k a j) := by
        rw [lintegral_tsum fun j => (measurable_const.indicator (hS j)).aemeasurable]
        exact tsum_congr fun j => lintegral_indicator_const (hS j) _
    _ ≤ ∑' j : ℤ, ENNReal.ofReal (Real.exp (a * ε) * Real.exp (-(a * ε) * |(j : ℝ)|)) *
          μ.withDensity β (band E k) := ENNReal.tsum_le_tsum fun j => by exact mul_le_mul_of_nonneg_left (hSμ j) (zero_le)
    _ = (∑' j : ℤ, ENNReal.ofReal (Real.exp (a * ε) * Real.exp (-(a * ε) * |(j : ℝ)|))) *
          μ.withDensity β (band E k) := ENNReal.tsum_mul_right
    _ < ∞ := by
        refine ENNReal.mul_lt_top ?_ hBfin
        rw [← ENNReal.ofReal_tsum_of_nonneg hnn hsum]
        exact ENNReal.ofReal_lt_top

end PositivityTheory.AdelicQuotientData

end
