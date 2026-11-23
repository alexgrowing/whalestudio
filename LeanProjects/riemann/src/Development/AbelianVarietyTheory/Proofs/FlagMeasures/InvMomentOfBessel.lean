import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OnePlaceKF
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DegVand
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsNormalFormStabilizerMeasure
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MomAllP
import Formalism.LocalRingCardinality.DataTies
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AbsOfRange
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralTranslate
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MassLowTypesSecond
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp GlobalTheory.TypeAsm Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal Pointwise

noncomputable section

namespace GlobalTheory.TwoSidedMoments

open GlobalTheory.AmpMoments

theorem size_bound_inv {b v g x Cg Cu CT : ℝ} {r : ℕ} (hb : Real.exp 1 < b) (hv : 1 ≤ v) (hvb : 2 * v ≤ b)
    (hg : 1 ≤ g) (hgb : g ≤ b ^ (2 * Cg)) (hCg : 8 ≤ Cg) (hx0 : 0 ≤ x)
    (hx : x ≤ max (Real.pi / v / g) (Real.pi / v / g)⁻¹ ^ r) :
    x * (b ^ max 2 Cu) ^ (2 * r) ≤ b ^ ((2 * Cg + 2 + |CT| + 10 * max 2 Cu) * (2 * r + 2 : ℝ)) := by
  have hb2 : 2 < b := lt_trans (by have := Real.exp_one_gt_d9; linarith) hb
  have hb1 : 1 ≤ b := by linarith
  have hb0 : 0 < b := by linarith
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hB : (2 : ℝ) ≤ max 2 Cu := le_max_left _ _
  have hp := Real.pi_gt_three
  have hg2 : 1 ≤ b ^ (2 * Cg) := hg.trans hgb
  have hM : max (Real.pi / v / g) (Real.pi / v / g)⁻¹ ≤ b ^ (2 * Cg + 2) := by
    rw [Real.rpow_add hb0, Real.rpow_two]
    refine max_le ?_ ?_
    · have : Real.pi / v / g ≤ Real.pi :=
        (div_le_self (by positivity) hg).trans (div_le_self (by positivity) hv)
      have := Real.pi_le_four
      nlinarith
    · rw [div_div, inv_div, div_le_iff₀ (by positivity)]
      have h1 : v * g ≤ b ^ 2 * b ^ (2 * Cg) := mul_le_mul (by nlinarith) hgb (by linarith) (by positivity)
      have : 0 ≤ b ^ (2 * Cg) * b ^ 2 := by positivity
      nlinarith
  have h1 : x ≤ b ^ ((2 * Cg + 2) * r) := by
    rw [Real.rpow_mul_natCast hb0.le]
    exact hx.trans (pow_le_pow_left₀ (le_max_of_le_left (by positivity)) hM r)
  calc x * (b ^ max 2 Cu) ^ (2 * r) ≤ b ^ ((2 * Cg + 2) * r) * (b ^ max 2 Cu) ^ (2 * r) := by gcongr
    _ = b ^ ((2 * Cg + 2) * r + max 2 Cu * ((2 * r : ℕ) : ℝ)) := by
        rw [Real.rpow_add hb0, Real.rpow_mul_natCast hb0.le (max 2 Cu)]
    _ ≤ _ := by
        refine Real.rpow_le_rpow_of_exponent_le hb1 ?_
        push_cast
        have := abs_nonneg CT
        nlinarith [mul_nonneg this hr, mul_nonneg (by linarith : 0 ≤ Cg) hr, mul_nonneg (by linarith : 0 ≤ max 2 Cu) hr]

theorem rpow_bridge {b C x : ℝ} {q : ℕ} (hb : 0 ≤ b) : b ^ (2 * C * x * q) = (b ^ (C * x)) ^ (2 * q) := by
  rw [← Real.rpow_mul_natCast hb]; congr 1; push_cast; ring

end GlobalTheory.TwoSidedMoments

namespace GlobalTheory.TwoSidedMoments

open GlobalTheory.AmpMoments

theorem hypTT_self (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ) (hZ : HypZ D large₂ C' Cl Cg cb Cu cT CT C0)
    (w : D.what₂.Word) : HypTT D w w := by
  obtain ⟨⟨-, -, -, -, -, -, -, -, -, -, -, hg1, -, hg2, -, -, -, -, -, -, -, -, -, -, -⟩, hDat, -⟩ := hZ
  obtain ⟨-, -, -, -, -, -, -, -, hmod, -⟩ := hDat
  have hk : (1 : ℝ) ≤ D.R.k := by have := D.R.m_add_three_le_k; exact_mod_cast (by omega : 1 ≤ D.R.k)
  have hL : 1 < large₂.sc.L := Real.one_lt_rpow large₂.sc.one_lt_alt large₂.sc.eps_pos
  have hbe : Real.exp 1 < large₂.sc.b := Real.exp_lt_exp.2 hL
  have hb2 : 2 < large₂.sc.b := lt_trans (by have := Real.exp_one_gt_d9; linarith) hbe
  have hkb : 2 < (D.R.k : ℝ) * large₂.sc.b := by nlinarith
  have hg : (2 : ℝ) < D.host.g 0 := lt_of_lt_of_le hkb ((le_self_pow₀ (by linarith) (by norm_num)).trans hg1)
  have hg' : 2 < D.host.g 0 := by exact_mod_cast hg
  have hgg : (2 : ℝ) < D.host.g 1 := lt_of_lt_of_le hkb ((le_self_pow₀ (by linarith) (by norm_num)).trans hg2)
  have hgg' : 2 < D.host.g 1 := by exact_mod_cast hgg
  have hp := (D.mem w).A.T_prime
  have h3 : 3 ≤ (D.mem w).A.T := by
    rcases (D.mem w).A.T_prime.two_le.eq_or_lt with h | h
    · exfalso
      have hm := (hmod w).2
      rw [← h] at hm
      have hN : 4 < (D.host.g 0 * D.host.g 1) ^ 2 := by
        have h9 : 9 ≤ D.host.g 0 * D.host.g 1 := Nat.mul_le_mul (show 3 ≤ D.host.g 0 from hg') (show 3 ≤ D.host.g 1 from hgg')
        nlinarith
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hm
      omega
    · omega
  exact ⟨hp, hp, h3, h3, Int.ModEq.refl _⟩

end GlobalTheory.TwoSidedMoments

namespace GlobalTheory.TwoSidedMoments

open GlobalTheory.AmpMoments

theorem rd_le_b (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ) (hCl : 1000 ≤ Cl)
    (hZ : HypZ D large₂ C' Cl Cg cb Cu cT CT C0) : D.host.rdE ≤ large₂.sc.b := by
  obtain ⟨⟨-, -, -, -, -, -, -, -, -, -, hrdL, -, -, -, -, -, -, -, hv, -⟩, -, -⟩ := hZ
  have hL : 1 < large₂.sc.L := Real.one_lt_rpow large₂.sc.one_lt_alt large₂.sc.eps_pos
  have hrd : D.host.rdE = 2 * D.host.v := by unfold Host.v; ring
  have h0 : 0 < D.host.rdE := by rw [hrd]; linarith
  have h1 : large₂.sc.L / Cl ≤ large₂.sc.L := div_le_self (by linarith) (by linarith)
  show D.host.rdE ≤ Real.exp large₂.sc.L
  exact (Real.log_le_iff_le_exp h0).1 (hrdL.trans h1)

end GlobalTheory.TwoSidedMoments
