import Development.WeilBound.RepresentationTheoryGL.TubeMeasures.DisjointTubes.TubeSt

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open GlobalTheory.CovTop.VolUp
open scoped ENNReal

noncomputable section

namespace MainStatements.Tam.N

theorem fac_le (r i : ℕ) (hi : i < r) : ((i.factorial : ℕ) : ℝ) ≤ (r : ℝ) ^ r := by
  have h1 : i.factorial ≤ i ^ i := Nat.factorial_le_pow i
  have h2 : i ^ i ≤ r ^ i := Nat.pow_le_pow_left hi.le i
  have h3 : r ^ i ≤ r ^ r := Nat.pow_le_pow_right (by omega) hi.le
  exact_mod_cast h1.trans (h2.trans h3)

theorem factor_lower (r i : ℕ) (hi : i < r) :
    ((r : ℝ) ^ r)⁻¹ ≤ 2 * Real.pi ^ (i + 1) / (i.factorial : ℝ) := by
  have hf : (0 : ℝ) < (i.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos i
  have hp : (1 : ℝ) ≤ Real.pi ^ (i + 1) := one_le_pow₀ (by linarith [Real.pi_gt_three])
  have hnum : (1 : ℝ) ≤ 2 * Real.pi ^ (i + 1) := by linarith
  calc ((r : ℝ) ^ r)⁻¹ = 1 / (r : ℝ) ^ r := by rw [one_div]
    _ ≤ 1 / (i.factorial : ℝ) := one_div_le_one_div_of_le hf (fac_le r i hi)
    _ ≤ 2 * Real.pi ^ (i + 1) / (i.factorial : ℝ) := div_le_div_of_nonneg_right hnum hf.le

theorem factor_upper (r i : ℕ) (hi : i < r) :
    2 * Real.pi ^ (i + 1) / (i.factorial : ℝ) ≤ (13 : ℝ) ^ r := by
  have hf : (1 : ℝ) ≤ (i.factorial : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero i)
  have hpos : (0 : ℝ) ≤ 2 * Real.pi ^ (i + 1) := by positivity
  have h1 : 2 * Real.pi ^ (i + 1) / (i.factorial : ℝ) ≤ 2 * Real.pi ^ (i + 1) := div_le_self hpos hf
  have h2 : Real.pi ^ (i + 1) ≤ (4 : ℝ) ^ (i + 1) := pow_le_pow_left₀ Real.pi_pos.le Real.pi_le_four _
  have h3 : (4 : ℝ) ^ (i + 1) ≤ (4 : ℝ) ^ r := pow_le_pow_right₀ (by norm_num) (by omega)
  have h4 : (2 : ℝ) ≤ (2 : ℝ) ^ r := by
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ r := pow_le_pow_right₀ (by norm_num) (by omega)
  have h5 : (2 : ℝ) * 4 ^ r ≤ 2 ^ r * 4 ^ r := by
    have : (0 : ℝ) ≤ 4 ^ r := by positivity
    nlinarith
  have h6 : (2 : ℝ) ^ r * 4 ^ r ≤ 13 ^ r := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by norm_num) (by norm_num) _
  nlinarith

end MainStatements.Tam.N

namespace MainStatements.Tam

theorem num : NumSt := by
  intro r hr
  constructor
  · have e : ((r : ℝ) ^ (r ^ 2))⁻¹ = ∏ _i ∈ Finset.range r, ((r : ℝ) ^ r)⁻¹ := by
      rw [Finset.prod_const, Finset.card_range, inv_pow, ← pow_mul, sq]
    rw [e]
    unfold ReciprocityTheory.ChartRestriction.DS.volU
    exact Finset.prod_le_prod (fun i _ => by positivity)
      (fun i hi => MainStatements.Tam.N.factor_lower r i (Finset.mem_range.mp hi))
  · have e : (13 : ℝ) ^ (r ^ 2) = ∏ _i ∈ Finset.range r, (13 : ℝ) ^ r := by
      rw [Finset.prod_const, Finset.card_range, ← pow_mul, sq]
    rw [e]
    unfold ReciprocityTheory.ChartRestriction.DS.volU
    exact Finset.prod_le_prod (fun i _ => by positivity)
      (fun i hi => MainStatements.Tam.N.factor_upper r i (Finset.mem_range.mp hi))

end MainStatements.Tam
