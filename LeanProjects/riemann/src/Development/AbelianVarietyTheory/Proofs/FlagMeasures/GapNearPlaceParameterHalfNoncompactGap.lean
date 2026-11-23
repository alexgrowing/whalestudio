import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OnePlaceKF
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DegVand
import Formalism.LocalRingCardinality.DataTies
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilyFormalDegreeLowerBound
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MomentPieriNumericsOfSizeHyps
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NumericalFamilyShapeGaps

open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.GapNear

theorem gap_near : ∀ Cn : ℝ, ∃ m₀ : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ), HypZ D large₂ C' Cl Cg cb Cu cT CT C0 → 1000 ≤ Cl → m₀ ≤ D.R.m → ∀ (τ : D.what₂.Tau) (lam' : Fin (2 * D.R.rS + D.R.k + 1) → ℝ), l1dist lam' (lamD D τ) ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3 + D.R.r → GapAtLeast (epsSH D.R) lam' ((D.R.r : ℝ) ^ 19 / 2) ∧ Formalism.FourierDecayAlt.ThreeDimData.GapOK D.R.k D.R.rS ((D.R.r : ℝ) ^ 19 / 2) := by
  intro Cn
  refine ⟨max Cn 1000, fun D large₂ C' Cl Cg cb Cu cT CT C0 hZ hCl hm₀ τ lam' hl => ?_⟩
  have hdim := dimS_eq D.R
  have hrr : D.R.r = D.R.k + D.R.m - 1 := rfl
  have hmk := D.R.m_add_three_le_k
  have hm2 := D.R.two_le_m
  have hnR : (D.R.r : ℝ) = 2 * D.R.rS + D.R.k + 1 := by rw [← hdim]; push_cast; ring
  have hmC : Cn ≤ (D.R.m : ℝ) := le_trans (le_max_left _ _) hm₀
  have hm1000 : (1000 : ℝ) ≤ D.R.m := le_trans (le_max_right _ _) hm₀
  have hkr : (D.R.k : ℝ) ≤ D.R.r := by exact_mod_cast (by omega : D.R.k ≤ D.R.r)
  have hmr : (D.R.m : ℝ) ≤ D.R.r := by exact_mod_cast (by omega : D.R.m ≤ D.R.r)
  have hr1000 : (1000 : ℝ) ≤ D.R.r := le_trans hm1000 hmr
  have hk0 : (0 : ℝ) ≤ D.R.k := Nat.cast_nonneg _

  have hsize : Cn * D.R.k * (D.R.m : ℝ) ^ 3 + D.R.r ≤ (D.R.r : ℝ) ^ 19 / 2 := by
    have h1 : Cn * D.R.k * (D.R.m : ℝ) ^ 3 ≤ (D.R.m : ℝ) * D.R.k * (D.R.m : ℝ) ^ 3 := by
      have := mul_le_mul_of_nonneg_right hmC (show (0 : ℝ) ≤ D.R.k * (D.R.m : ℝ) ^ 3 by positivity)
      linarith [show Cn * D.R.k * (D.R.m : ℝ) ^ 3 = Cn * (D.R.k * (D.R.m : ℝ) ^ 3) by ring,
        show (D.R.m : ℝ) * D.R.k * (D.R.m : ℝ) ^ 3 = (D.R.m : ℝ) * (D.R.k * (D.R.m : ℝ) ^ 3) by ring]
    have h2 : (D.R.m : ℝ) * D.R.k * (D.R.m : ℝ) ^ 3 ≤ (D.R.r : ℝ) ^ 5 := by
      have e : (D.R.m : ℝ) * D.R.k * (D.R.m : ℝ) ^ 3 = D.R.k * (D.R.m : ℝ) ^ 4 := by ring
      have e' : (D.R.r : ℝ) ^ 5 = D.R.r * (D.R.r : ℝ) ^ 4 := by ring
      rw [e, e']
      exact mul_le_mul hkr (pow_le_pow_left₀ (by positivity) hmr 4) (by positivity) (by positivity)
    have h3 : (D.R.r : ℝ) ≤ (D.R.r : ℝ) ^ 5 := le_self_pow₀ (by linarith) (by norm_num)
    have h4 : (4 : ℝ) ≤ (D.R.r : ℝ) ^ 14 := le_trans (by norm_num) (le_trans hr1000 (le_self_pow₀ (by linarith) (by norm_num)))
    have h5 : 4 * (D.R.r : ℝ) ^ 5 ≤ (D.R.r : ℝ) ^ 19 := by
      have := mul_le_mul_of_nonneg_left h4 (show (0 : ℝ) ≤ (D.R.r : ℝ) ^ 5 by positivity)
      linarith [show (D.R.r : ℝ) ^ 5 * (D.R.r : ℝ) ^ 14 = (D.R.r : ℝ) ^ 19 by ring]
    linarith

  have hf : 1 ≤ D.R.f := by
    have := D.R.m_le_f
    unfold Ranks.f Ranks.n
    omega
  have hL : 1 ≤ large₂.sc.L := Real.one_le_rpow large₂.sc.one_lt_alt.le large₂.sc.eps_pos.le
  have hG0 := Formalism.MainNotions.BridgeLemma.szh_gap hZ.1 τ
  have hG : (D.R.r : ℝ) ^ 19 ≤ Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * large₂.sc.L := by
    have hf' : (1 : ℝ) ≤ (D.R.f : ℝ) ^ 5 := one_le_pow₀ (by exact_mod_cast hf)
    have h5 : (1 : ℝ) ≤ Cl * ((D.R.f : ℝ) ^ 5 * large₂.sc.L) :=
      one_le_mul_of_one_le_of_one_le (by linarith) (one_le_mul_of_one_le_of_one_le hf' hL)
    have h6 := mul_le_mul_of_nonneg_left h5 (show (0 : ℝ) ≤ (D.R.r : ℝ) ^ 19 by positivity)
    have h7 : (D.R.r : ℝ) ^ 19 * (Cl * ((D.R.f : ℝ) ^ 5 * large₂.sc.L)) =
      Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * large₂.sc.L := by ring
    linarith
  refine ⟨fun a b hne => ?_, ?_⟩
  · have hab : a ≠ b := fun e => hne (e ▸ rfl)
    have g := hG0 a b hne
    change _ ≤ |lamD D τ a - lamD D τ b| at g
    have hpair : |lam' a - lamD D τ a| + |lam' b - lamD D τ b| ≤ l1dist lam' (lamD D τ) := by
      unfold l1dist
      rw [← Finset.sum_pair (f := fun i => |lam' i - lamD D τ i|) hab]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => abs_nonneg _)
    have tri : |lamD D τ a - lamD D τ b| ≤ |lam' a - lam' b| + |lam' a - lamD D τ a| + |lam' b - lamD D τ b| := by
      rw [abs_le]
      constructor <;>
      linarith [le_abs_self (lam' a - lam' b), neg_abs_le (lam' a - lam' b), le_abs_self (lam' a - lamD D τ a),
        neg_abs_le (lam' a - lamD D τ a), le_abs_self (lam' b - lamD D τ b), neg_abs_le (lam' b - lamD D τ b)]
    linarith
  · have hok := (GlobalTheory.SizeNum.gapOK D.R.k D.R.rS D.R.r hnR (by omega) hr1000).1
    exact GlobalTheory.NumFam.gapOK_mono D.R.k D.R.rS (by linarith [show (0:ℝ) ≤ (D.R.r : ℝ) ^ 19 by positivity]) hok

end GlobalTheory.GapNear
