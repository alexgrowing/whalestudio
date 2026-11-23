import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvUAbsU

open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG

noncomputable section

namespace GlobalTheory

namespace ShellSum

open Function

def shell {X : Type} (H : ℕ → Set X) : ℕ → Set X
  | 0 => H 0
  | j + 1 => H (j + 1) \ H j

def shellVal (q : ℕ) (b : ℂ) : ℕ → ℂ
  | 0 => 1
  | j + 1 => (b / q) ^ (j + 1)

def shellMass (q : ℕ) : ℕ → ℝ
  | 0 => 1
  | j + 1 => (q : ℝ) ^ (j + 1) - (q : ℝ) ^ j

theorem shellMass_nonneg (q : ℕ) (hq : 2 ≤ q) (j : ℕ) : 0 ≤ shellMass q j := by
  cases j with
  | zero => simp [shellMass]
  | succ j =>
    simp only [shellMass, sub_nonneg]
    exact pow_le_pow_right₀ (by exact_mod_cast (by omega : 1 ≤ q)) (Nat.le_succ j)

theorem hasSum_shell (q : ℕ) (hq : 2 ≤ q) (b : ℂ) (hb : ‖b‖ < 1) :
    HasSum (fun j => shellVal q b j * (shellMass q j : ℂ)) (cSL q b) := by
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  have h1 : HasSum (fun j : ℕ => b ^ j * (b * (1 - (q : ℂ)⁻¹))) ((1 - b)⁻¹ * (b * (1 - (q : ℂ)⁻¹))) :=
    (hasSum_geometric_of_norm_lt_one hb).mul_right _
  have hb1 : (1 - b) ≠ 0 := by
    intro h
    have : b = 1 := by linear_combination -h
    rw [this] at hb; simp at hb
  have e1 : (fun n : ℕ => shellVal q b (n + 1) * (shellMass q (n + 1) : ℂ)) =
      fun j => b ^ j * (b * (1 - (q : ℂ)⁻¹)) := by
    funext j; simp only [shellVal, shellMass, div_pow]; push_cast; field_simp; ring
  have e2 : cSL q b - ∑ i ∈ Finset.range 1, shellVal q b i * (shellMass q i : ℂ) =
      (1 - b)⁻¹ * (b * (1 - (q : ℂ)⁻¹)) := by
    simp only [Finset.range_one, Finset.sum_singleton, shellVal, shellMass, cSL, Complex.ofReal_one]
    field_simp; ring
  refine (hasSum_nat_add_iff' 1).1 ?_
  show HasSum (fun n : ℕ => shellVal q b (n + 1) * (shellMass q (n + 1) : ℂ))
    (cSL q b - ∑ i ∈ Finset.range 1, shellVal q b i * (shellMass q i : ℂ))
  rw [e1, e2]; exact h1

theorem mem_shell_iff {X : Type} {H : ℕ → Set X} (hmono : Monotone H) (j : ℕ) (x : X) :
    x ∈ shell H j ↔ x ∈ H j ∧ ∀ i < j, x ∉ H i := by
  cases j with
  | zero => simp [shell]
  | succ j =>
    simp only [shell, Set.mem_diff]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun i hi hx => h2 (hmono (Nat.lt_succ_iff.1 hi) hx)⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, h2 j (Nat.lt_succ_self j)⟩

theorem shell_disjoint {X : Type} {H : ℕ → Set X} (hmono : Monotone H) :
    Pairwise (Disjoint on shell H) := by
  have key : ∀ i j, i < j → Disjoint (shell H i) (shell H j) := by
    intro i j hij
    rw [Set.disjoint_left]
    intro x hi hj
    exact ((mem_shell_iff hmono j x).1 hj).2 i hij ((mem_shell_iff hmono i x).1 hi).1
  intro i j hij
  rcases Nat.lt_or_gt_of_ne hij with h | h
  · exact key i j h
  · exact (key j i h).symm

theorem iUnion_shell {X : Type} {H : ℕ → Set X} (hmono : Monotone H) (hU : ⋃ j, H j = Set.univ) :
    ⋃ j, shell H j = Set.univ := by
  classical
  apply Set.eq_univ_of_forall
  intro x
  have hex : ∃ n, x ∈ H n := Set.mem_iUnion.1 (hU ▸ Set.mem_univ x)
  exact Set.mem_iUnion.2 ⟨Nat.find hex, (mem_shell_iff hmono _ x).2
    ⟨Nat.find_spec hex, fun i hi => Nat.find_min hex hi⟩⟩

theorem integral_geom_on_shells {X : Type} [MeasurableSpace X] (μ : Measure X) (q : ℕ) (hq : 2 ≤ q) (a : ℂ)
    (ha : ‖a‖ < 1) (H : ℕ → Set X) (hH : ∀ j, MeasurableSet (H j)) (hmono : Monotone H)
    (hU : ⋃ j, H j = Set.univ) (hμ : ∀ j, μ (H j) = (q : ENNReal) ^ j) (F : X → ℂ)
    (hF0 : ∀ x ∈ H 0, F x = 1) (hF : ∀ j x, x ∈ H (j + 1) → x ∉ H j → F x = (a / q) ^ (j + 1)) :
    Integrable F μ ∧ ∫ x, F x ∂μ = cSL q a ∧ ∫⁻ x, ‖F x‖ₑ ∂μ = ‖cSL q ((‖a‖ : ℝ) : ℂ)‖ₑ := by
  set S := shell H with hSdef
  have hSm : ∀ j, MeasurableSet (S j) := by
    intro j; cases j with
    | zero => exact hH 0
    | succ j => exact (hH _).diff (hH _)
  have hSd : Pairwise (Disjoint on S) := shell_disjoint hmono
  have hSU : ⋃ j, S j = Set.univ := iUnion_shell hmono hU
  have hSF : ∀ j, ∀ x ∈ S j, F x = shellVal q a j := by
    intro j x hx; cases j with
    | zero => exact hF0 x hx
    | succ j => exact hF j x hx.1 hx.2
  have hSμ : ∀ j, μ (S j) = ENNReal.ofReal (shellMass q j) := by
    intro j; cases j with
    | zero => simp [hSdef, shell, shellMass, hμ]
    | succ j =>
      show μ (H (j + 1) \ H j) = _
      rw [measure_diff (hmono (Nat.le_succ j)) (hH j).nullMeasurableSet
          (by rw [hμ]; exact ENNReal.pow_ne_top (by simp)),
        hμ, hμ, shellMass, ENNReal.ofReal_sub _ (by positivity), ENNReal.ofReal_pow (by positivity),
        ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_natCast]
  have hSr : ∀ j, μ.real (S j) = shellMass q j := by
    intro j; rw [Measure.real, hSμ, ENNReal.toReal_ofReal (shellMass_nonneg q hq j)]
  have hmeas : AEStronglyMeasurable F μ := by
    rw [← Measure.restrict_univ (μ := μ), ← hSU, aestronglyMeasurable_iUnion_iff]
    intro j
    refine (aestronglyMeasurable_const (b := shellVal q a j)).congr ?_
    filter_upwards [ae_restrict_mem (hSm j)] with x hx
    exact (hSF j x hx).symm
  set s : ℝ := (1 - (q : ℝ)⁻¹ * ‖a‖) / (1 - ‖a‖) with hsdef
  have hq1 : (q : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast (by omega : 1 ≤ q))
  have hs0 : 0 ≤ s := by
    apply div_nonneg
    · have : (q : ℝ)⁻¹ * ‖a‖ ≤ 1 := mul_le_one₀ hq1 (norm_nonneg a) ha.le
      linarith
    · linarith
  have hsC : ((s : ℝ) : ℂ) = cSL q ((‖a‖ : ℝ) : ℂ) := by
    rw [hsdef]; unfold cSL; push_cast; ring
  have hreal : HasSum (fun j => ‖shellVal q a j‖ * shellMass q j) s := by
    have e : (fun j => ((‖shellVal q a j‖ * shellMass q j : ℝ) : ℂ)) =
        fun j => shellVal q ((‖a‖ : ℝ) : ℂ) j * (shellMass q j : ℂ) := by
      funext j
      cases j with
      | zero => simp [shellVal]
      | succ j => simp [shellVal, norm_pow, norm_div]
    refine Complex.hasSum_ofReal.1 ?_
    show HasSum (fun j => ((‖shellVal q a j‖ * shellMass q j : ℝ) : ℂ)) ((s : ℝ) : ℂ)
    rw [e, hsC]
    exact hasSum_shell q hq ((‖a‖ : ℝ) : ℂ) (by simpa using ha)
  have hL : ∫⁻ x, ‖F x‖ₑ ∂μ = ‖cSL q ((‖a‖ : ℝ) : ℂ)‖ₑ := by
    rw [← setLIntegral_univ, ← hSU, lintegral_iUnion hSm hSd]
    have hterm : ∀ j, ∫⁻ x in S j, ‖F x‖ₑ ∂μ = ENNReal.ofReal (‖shellVal q a j‖ * shellMass q j) := by
      intro j
      rw [setLIntegral_congr_fun (hSm j) (fun x hx => by rw [hSF j x hx]), setLIntegral_const, hSμ,
        ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm_eq_enorm]
    simp_rw [hterm]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => mul_nonneg (norm_nonneg _) (shellMass_nonneg q hq j))
      hreal.summable, hreal.tsum_eq, ← hsC, ← ofReal_norm_eq_enorm, Complex.norm_real,
      Real.norm_of_nonneg hs0]
  have hint : Integrable F μ := by
    refine ⟨hmeas, ?_⟩
    rw [hasFiniteIntegral_iff_enorm, hL]
    exact enorm_lt_top
  refine ⟨hint, ?_, hL⟩
  have h1 := hasSum_integral_iUnion hSm hSd hint.integrableOn
  rw [hSU, Measure.restrict_univ] at h1
  refine h1.unique ?_
  have e3 : (fun n => ∫ x in S n, F x ∂μ) = fun j => shellVal q a j * (shellMass q j : ℂ) := by
    funext j
    rw [setIntegral_congr_fun (hSm j) (fun x hx => hSF j x hx), setIntegral_const, hSr, Complex.real_smul,
      mul_comm]
  rw [e3]
  exact hasSum_shell q hq a ha

end ShellSum

theorem integral_geometric_shells : ∀ {X : Type} [MeasurableSpace X] (μ : Measure X) (q : ℕ), 2 ≤ q →
    ∀ (a : ℂ), ‖a‖ < 1 →
    ∀ (H : ℕ → Set X), (∀ j, MeasurableSet (H j)) → Monotone H → ⋃ j, H j = Set.univ →
    (∀ j, μ (H j) = (q : ENNReal) ^ j) → ∀ (F : X → ℂ), (∀ x ∈ H 0, F x = 1) →
    (∀ j x, x ∈ H (j + 1) → x ∉ H j → F x = (a / q) ^ (j + 1)) →
    Integrable F μ ∧ ∫ x, F x ∂μ = cSL q a ∧ ∫⁻ x, ‖F x‖ₑ ∂μ = ‖cSL q ((‖a‖ : ℝ) : ℂ)‖ₑ :=
  fun μ q hq a ha H hH hmono hU hμ F hF0 hF =>
    ShellSum.integral_geom_on_shells μ q hq a ha H hH hmono hU hμ F hF0 hF

end GlobalTheory

end
