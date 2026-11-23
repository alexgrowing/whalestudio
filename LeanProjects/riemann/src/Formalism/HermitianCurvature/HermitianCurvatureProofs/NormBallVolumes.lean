import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.FrobeniusBoundOfMulNearOne
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LiftingTheory

open Matrix MeasureTheory Filter Topology Metric
open scoped ComplexConjugate ENNReal NNReal

noncomputable section

namespace Formalism.FourierDecayAlt.P.NormBallVolumes

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem gnLower : GNLower := fun _ _ _ hg => Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one hg

theorem gN_meas (k r : ℕ) : Measurable fun g : Mt k r => gN (Matrix.of g) := by
  unfold gN
  apply Measurable.sqrt
  refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_
  have h1 : Measurable fun g : Mt k r => g i j := (measurable_pi_apply j).comp (measurable_pi_apply i)
  exact Complex.continuous_normSq.measurable.comp h1

theorem ae_mem {k r : ℕ} {U : Set (Mat k r)} {μ : Measure (Mt k r)} (h : IsHaarOn U μ) :
    ∀ᵐ g ∂μ, Matrix.of g ∈ U := by
  rw [ae_iff]
  exact h.conc

theorem one_mem (k r : ℕ) : (1 : Mat k r) ∈ GV k r := by
  show (1 : Mat k r)ᴴ * Hpk k r * 1 = Hpk k r
  simp

def iv {k r : ℕ} (g : Mat k r) : Mat k r := Hpk k r * gᴴ * Hpk k r

theorem iv_mul {k r : ℕ} {g : Mat k r} (hg : g ∈ GV k r) : iv g * g = 1 := by
  have h : gᴴ * Hpk k r * g = Hpk k r := hg
  unfold iv
  rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, h]
  exact Formalism.FourierDecayAlt.P.BetaSesquilinearity.Hsq k r

theorem iv_mem {k r : ℕ} {g : Mat k r} (hg : g ∈ GV k r) : iv g ∈ GV k r := by
  rw [← Matrix.inv_eq_left_inv (iv_mul hg)]
  exact Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_inv hg

theorem sigmaFinite_of_haar {k r : ℕ} {U : Set (Mat k r)} {μ : Measure (Mt k r)} (h : IsHaarOn U μ) : SigmaFinite μ := by
  have : IsFiniteMeasureOnCompacts μ := ⟨fun K hK => h.finite_compact K hK⟩
  infer_instance

theorem lmulM_cont {k r : ℕ} (a : Mat k r) : Continuous (lmulM a : Mt k r → Mt k r) := by
  have hof : Continuous (fun x : Mt k r => (Matrix.of x : Mat k r)) := continuous_id
  exact (continuous_const (y := a)).matrix_mul hof

theorem volCrude : VolCrude :=
  _root_.UpperTheory.Reformulated.B.LiftingTheory.volCrude

theorem shellInt : ShellInt := by
  intro X _ μ N C d A hN h1 hd hV hA
  have hA0 : 0 < A := lt_of_le_of_lt hd hA
  let S : ℕ → Set X := fun j => {x | N x ≤ (2 : ℝ) ^ (j + 1)}
  let c : ℕ → ℝ := fun j => ((2 : ℝ) ^ j) ^ (-A)
  have hSm : ∀ j, MeasurableSet (S j) := fun j => measurableSet_le hN measurable_const
  have hpt : ∀ᵐ x ∂μ, ENNReal.ofReal (N x ^ (-A)) ≤ ∑' j, (S j).indicator (fun _ => ENNReal.ofReal (c j)) x := by
    filter_upwards [h1] with x hx
    obtain ⟨j, hj1, hj2⟩ := exists_nat_pow_near hx one_lt_two
    refine le_trans ?_ (ENNReal.le_tsum j)
    rw [Set.indicator_of_mem (show x ∈ S j from hj2.le)]
    apply ENNReal.ofReal_le_ofReal
    exact Real.rpow_le_rpow_of_nonpos (by positivity) hj1 (by linarith)
  have hterm : ∀ j : ℕ, c j * (C * ((2 : ℝ) ^ (j + 1)) ^ d) = C * (2 : ℝ) ^ d * ((2 : ℝ) ^ (d - A)) ^ j := by
    intro j
    have h2 : (0 : ℝ) < 2 := two_pos
    have e1 : c j = (2 : ℝ) ^ ((j : ℝ) * (-A)) := by
      show ((2 : ℝ) ^ j) ^ (-A) = _
      rw [← Real.rpow_natCast 2 j, ← Real.rpow_mul h2.le]
    have e2 : ((2 : ℝ) ^ (j + 1)) ^ d = (2 : ℝ) ^ (((j : ℝ) + 1) * d) := by
      rw [← Real.rpow_natCast 2 (j + 1), ← Real.rpow_mul h2.le]
      push_cast
      rfl
    have e3 : ((2 : ℝ) ^ (d - A)) ^ j = (2 : ℝ) ^ ((d - A) * (j : ℝ)) := by
      rw [Real.rpow_mul_natCast h2.le]
    rw [e1, e2, e3]
    have e4 : (2 : ℝ) ^ ((j : ℝ) * (-A)) * (2 : ℝ) ^ (((j : ℝ) + 1) * d) = (2 : ℝ) ^ d * (2 : ℝ) ^ ((d - A) * (j : ℝ)) := by
      rw [← Real.rpow_add h2, ← Real.rpow_add h2]
      congr 1
      ring
    calc (2 : ℝ) ^ ((j : ℝ) * (-A)) * (C * (2 : ℝ) ^ (((j : ℝ) + 1) * d))
        = C * ((2 : ℝ) ^ ((j : ℝ) * (-A)) * (2 : ℝ) ^ (((j : ℝ) + 1) * d)) := by ring
      _ = _ := by rw [e4]; ring
  have hsum : Summable fun j : ℕ => c j * (C * ((2 : ℝ) ^ (j + 1)) ^ d) := by
    simp only [hterm]
    apply Summable.mul_left
    exact summable_geometric_of_lt_one (Real.rpow_nonneg two_pos.le _)
      (Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith))
  calc (∫⁻ x, ENNReal.ofReal (N x ^ (-A)) ∂μ)
      ≤ ∫⁻ x, ∑' j, (S j).indicator (fun _ => ENNReal.ofReal (c j)) x ∂μ := lintegral_mono_ae hpt
    _ = ∑' j, ∫⁻ x, (S j).indicator (fun _ => ENNReal.ofReal (c j)) x ∂μ :=
        lintegral_tsum fun j => (measurable_const.indicator (hSm j)).aemeasurable
    _ = ∑' j, ENNReal.ofReal (c j) * μ (S j) := by
        congr 1
        funext j
        exact lintegral_indicator_const (hSm j) _
    _ ≤ ∑' j, ENNReal.ofReal (c j) * ENNReal.ofReal (C * ((2 : ℝ) ^ (j + 1)) ^ d) := by
        refine ENNReal.tsum_le_tsum fun j => ?_
        gcongr
        exact hV _ (one_le_pow₀ one_le_two)
    _ = ∑' j, ENNReal.ofReal (c j * (C * ((2 : ℝ) ^ (j + 1)) ^ d)) := by
        congr 1
        funext j
        rw [ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity) _)]
    _ < ∞ := hsum.tsum_ofReal_lt_top

end Formalism.FourierDecayAlt.P.NormBallVolumes

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.P.NormBallVolumes

theorem norm_power_integrable_crude_of_volume : Formalism.FourierDecayAlt.B2.GNIntCrudeFromVol := by
  intro hS hL hV k r μG A hμ hA
  obtain ⟨C, hC⟩ := hV k r μG hμ
  refine hS (Mt k r) μG (fun g => gN (Matrix.of g)) C _ A (gN_meas k r) ?_ (by positivity) hC hA
  filter_upwards [ae_mem hμ] with g hg using hL k r _ hg

theorem matrix_coefficient_bound_by_norm : Formalism.FourierDecayAlt.B2.CCFromGN := by
  intro k r Wp Wq _ _ _ _ D A h F c _ hb
  have hae : ∀ᵐ g ∂D.μG, ‖F (Matrix.of g)‖ₑ ≤ ENNReal.ofReal |c| * ENNReal.ofReal (gN (Matrix.of g) ^ (-A)) := by
    filter_upwards [ae_mem D.haarG] with g hg
    have h1 := hb _ hg
    have hpos : 0 < gN (Matrix.of g) := lt_of_lt_of_le one_pos (gnLower k r _ hg)
    have hp : 0 < gN (Matrix.of g) ^ A := Real.rpow_pos_of_pos hpos A
    rw [← ENNReal.ofReal_mul (abs_nonneg c), ← ofReal_norm]
    apply ENNReal.ofReal_le_ofReal
    rw [Real.rpow_neg hpos.le, ← div_eq_mul_inv, le_div_iff₀ hp]
    calc ‖F (Matrix.of g)‖ * gN (Matrix.of g) ^ A = gN (Matrix.of g) ^ A * ‖F (Matrix.of g)‖ := mul_comm _ _
      _ ≤ c := h1
      _ ≤ |c| := le_abs_self c
  calc (∫⁻ g : Mt k r, ‖F (Matrix.of g)‖ₑ ∂D.μG)
      ≤ ∫⁻ g : Mt k r, ENNReal.ofReal |c| * ENNReal.ofReal (gN (Matrix.of g) ^ (-A)) ∂D.μG := lintegral_mono_ae hae
    _ = ENNReal.ofReal |c| * ∫⁻ g : Mt k r, ENNReal.ofReal (gN (Matrix.of g) ^ (-A)) ∂D.μG :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top h

theorem matrix_coefficient_integrable_of_parts : Formalism.FourierDecayAlt.B2.AssembleCCInt := by
  intro h1 h2 k r Wp Wq _ _ _ _ D A hA
  exact h1 k r Wp Wq D A (h2 k r D.μG A D.haarG hA)

theorem matrix_coefficient_integrable_double : Formalism.FourierDecayAlt.B2.CCIntDouble := by
  intro hX k r Wp Wq _ _ _ _ _ _ D A hA
  by_cases hT : ∃ T : Wq →L[ℂ] Wp, T ≠ 0
  · obtain ⟨T, hT0⟩ := hT
    apply matrix_coefficient_bound_by_norm k r Wp Wq D A
    have hA1 : AB k r ≤ A / 2 := by linarith
    obtain ⟨Ξ, ⟨C, hC⟩, _⟩ := hX k r Wp Wq D (A / 2) hA1
    set F : Mat k r → (Wq →L[ℂ] Wp) := fun g => ((gN g ^ (-(A / 2)) : ℝ) : ℂ) • T with hF
    have hm : AEStronglyMeasurable (fun g : Mt k r => F (Matrix.of g)) D.μG := by
      have h1 : Measurable fun g : Mt k r => ((gN (Matrix.of g) ^ (-(A / 2)) : ℝ) : ℂ) :=
        Complex.measurable_ofReal.comp ((gN_meas k r).pow_const _)
      exact h1.aestronglyMeasurable.smul_const T
    have hn : ∀ g : Mat k r, 0 < gN g → ‖F g‖ = gN g ^ (-(A / 2)) * ‖T‖ := by
      intro g hg
      simp only [hF, norm_smul, Complex.norm_real]
      rw [Real.norm_of_nonneg (Real.rpow_nonneg hg.le _)]
    have hb : ∀ g ∈ GV k r, gN g ^ (A / 2) * ‖F g‖ ≤ ‖T‖ := by
      intro g hg
      have hpos : 0 < gN g := lt_of_lt_of_le one_pos (gnLower k r g hg)
      rw [hn g hpos, ← mul_assoc, ← Real.rpow_add hpos]
      simp
    have hmain := hC F F ‖T‖ ‖T‖ hm hm hb hb 1 (one_mem k r) 1 (one_mem k r)
    have key : ∀ᵐ g ∂D.μG, ‖T‖ₑ * ‖T‖ₑ * ENNReal.ofReal (gN (Matrix.of g) ^ (-A)) =
        ‖F ((1 : Mat k r)⁻¹ * Matrix.of g * 1)‖ₑ * ‖F (Matrix.of g)‖ₑ := by
      filter_upwards [ae_mem D.haarG] with g hg
      have hpos : 0 < gN (Matrix.of g) := lt_of_lt_of_le one_pos (gnLower k r _ hg)
      have e1 : (1 : Mat k r)⁻¹ * Matrix.of g * 1 = Matrix.of g := by simp
      rw [e1, ← ofReal_norm (F (Matrix.of g)), hn _ hpos, ← ofReal_norm T,
        ← ENNReal.ofReal_mul (norm_nonneg T), ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      have : gN (Matrix.of g) ^ (-A) = gN (Matrix.of g) ^ (-(A / 2)) * gN (Matrix.of g) ^ (-(A / 2)) := by
        rw [← Real.rpow_add hpos]; congr 1; ring
      rw [this]; ring
    have hfin : (∫⁻ g : Mt k r, ‖T‖ₑ * ‖T‖ₑ * ENNReal.ofReal (gN (Matrix.of g) ^ (-A)) ∂D.μG) < ∞ := by
      rw [lintegral_congr_ae key]
      refine lt_of_le_of_lt hmain ?_
      exact ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.coe_lt_top) ENNReal.coe_lt_top
    have hc : ‖T‖ₑ * ‖T‖ₑ ≠ ∞ := ENNReal.mul_ne_top enorm_ne_top enorm_ne_top
    rw [lintegral_const_mul' _ _ hc] at hfin
    rcases ENNReal.mul_lt_top_iff.mp hfin with h | h | h
    · exact h.2
    · exfalso
      have : ‖T‖ₑ = 0 := by
        rcases mul_eq_zero.mp h with h | h <;> exact h
      exact hT0 (enorm_eq_zero.mp this)
    · rw [h]; exact ENNReal.zero_lt_top
  · simp only [not_exists, not_not] at hT
    intro F c _ _
    simp [hT]

theorem matrix_coefficient_integrable_crude_all : Formalism.FourierDecayAlt.B2.CCIntCrudeAll := by
  intro k r Wp Wq _ _ _ _ D A hA
  exact matrix_coefficient_bound_by_norm k r Wp Wq D A
    (norm_power_integrable_crude_of_volume shellInt gnLower volCrude k r D.μG A D.haarG hA)

end Formalism.FourierDecayAlt.P

namespace Formalism.FourierDecayAlt.P.NormBallVolumes

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

end Formalism.FourierDecayAlt.P.NormBallVolumes
