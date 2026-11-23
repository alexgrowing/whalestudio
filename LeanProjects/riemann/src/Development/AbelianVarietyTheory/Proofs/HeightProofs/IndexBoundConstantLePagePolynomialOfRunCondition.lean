import Mathlib
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.ConclOfInputs4
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NoCommonZeroSt
import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie

set_option autoImplicit false

namespace GlobalTheory.FinalJoin

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin GlobalTheory.RunIn GlobalTheory.FinalJoin

theorem indexBound_threeTerm_constant_le_real (n m4 u r C Z : ℝ) (hZ : 2000 ≤ Z) (hC : 1 ≤ C) (hn0 : 0 ≤ n) (hn : n ≤ C * Z ^ 4)
    (hm0 : 0 ≤ m4) (hm : m4 ≤ Z) (hu1 : 1 ≤ u) (hu : u ^ 4 ≤ 16 * Z ^ 5) (hr : r ≤ Z) :
    max (16200 * Real.pi * n * m4 * u ^ 4) (max (u ^ 4 * n + 2 * u ^ 3) (r * u ^ 3)) ≤ C * Z ^ 12 := by
  have hZ1 : (1 : ℝ) ≤ Z := by linarith
  have hZ0 : (0 : ℝ) ≤ Z := by linarith
  have hC0 : (0 : ℝ) ≤ C := by linarith
  have hu0 : (0 : ℝ) ≤ u := by linarith
  have h34 : u ^ 3 ≤ 16 * Z ^ 5 := (pow_le_pow_right₀ hu1 (by norm_num)).trans hu
  have hZ2 : (4000000 : ℝ) ≤ Z ^ 2 := by nlinarith
  have hW0 : 0 ≤ C * Z ^ 10 := by positivity
  have hW : 4000000 * (C * Z ^ 10) ≤ C * Z ^ 12 := by
    calc 4000000 * (C * Z ^ 10) ≤ Z ^ 2 * (C * Z ^ 10) := mul_le_mul_of_nonneg_right hZ2 hW0
      _ = C * Z ^ 12 := by ring
  have hk : ∀ k : ℕ, k ≤ 10 → Z ^ k ≤ C * Z ^ 10 := fun k hk =>
    (pow_le_pow_right₀ hZ1 hk).trans (le_mul_of_one_le_left (by positivity) hC)
  refine max_le ?_ (max_le ?_ ?_)
  · have hpi : Real.pi ≤ 4 := Real.pi_le_four
    have hpi0 : 0 ≤ Real.pi := Real.pi_pos.le
    calc 16200 * Real.pi * n * m4 * u ^ 4 ≤ 16200 * 4 * (C * Z ^ 4) * Z * (16 * Z ^ 5) := by gcongr
      _ = 1036800 * (C * Z ^ 10) := by ring
      _ ≤ C * Z ^ 12 := by linarith
  · have a1 : u ^ 4 * n ≤ (16 * Z ^ 5) * (C * Z ^ 4) := by gcongr
    have a2 : C * Z ^ 9 ≤ C * Z ^ 10 := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hZ1 (by norm_num)) hC0
    have a3 := hk 5 (by norm_num)
    have a4 : (16 * Z ^ 5) * (C * Z ^ 4) = 16 * (C * Z ^ 9) := by ring
    linarith
  · have a1 : r * u ^ 3 ≤ Z * (16 * Z ^ 5) := by gcongr
    have a3 := hk 6 (by norm_num)
    have a4 : Z * (16 * Z ^ 5) = 16 * Z ^ 6 := by ring
    linarith

theorem indexBoundConstant_le_pagePolynomial_of_runConditions : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ), InR D j → PageRun large₂ X H C2 A2 CT ka wL wF Tn nP nW h0 → flipOneThree D nW ≤ WeightFamilies.PPv D large₂ C2 A2 := by
  intro D B P j X large₂ H C2 A2 CT ka wL wF Tn nP nW h0 _ hP
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hnW, -, -, -, -, -, -, -, -, -, -, -, -, -, hd⟩ := hP.hyp.2.1
  rw [hP.tie.1] at hd
  have hA : 12 ≤ A2 := hP.tie.2.2.2.2.2
  obtain ⟨hC, hCZ, -, -, -, -, -, -, h12, -⟩ := hd
  have e : Zb D large₂ = zBase large₂ := rfl
  rw [e] at hCZ h12
  have hZ : 2000 ≤ zBase large₂ := by
    have h1 : (1000 : ℝ) ^ 20 ≤ C2 ^ 20 := pow_le_pow_left₀ (by norm_num) hC 20
    have h2 : (2000 : ℝ) ≤ 1000 ^ 20 := by norm_num
    linarith
  have hL : 1 ≤ large₂.sc.L := by
    unfold Scale.L; exact Real.one_le_rpow large₂.sc.one_lt_alt.le large₂.sc.eps_pos.le
  have hfr : (D.R.f : ℝ) * D.R.r ≤ zBase large₂ := by
    unfold zBase
    exact le_mul_of_one_le_right (by positivity) hL
  have hm1 : (1 : ℝ) ≤ (D.R.m : ℝ) := by
    have : 1 ≤ D.R.m := by have := D.R.two_le_m; omega
    exact_mod_cast this
  have hr1 : (1 : ℝ) ≤ (D.R.r : ℝ) := by
    have : 1 ≤ D.R.r := by unfold Ranks.r; have := D.R.two_le_m; omega
    exact_mod_cast this
  have hf8 : (8 : ℝ) ≤ (D.R.f : ℝ) := by exact_mod_cast D.eight_le_f
  have hf : (D.R.f : ℝ) ≤ zBase large₂ := (le_mul_of_one_le_right (by positivity) hr1).trans hfr
  have hr : (D.R.r : ℝ) ≤ zBase large₂ := (le_mul_of_one_le_left (by positivity) (by linarith)).trans hfr
  have hm : (D.R.m : ℝ) ^ 4 ≤ zBase large₂ := (lift_index_pow_four_le_degree hP.page).trans hf
  have hu1 : 1 ≤ 2 * (D.R.f : ℝ) * (D.R.m : ℝ) := by nlinarith
  have hu : (2 * (D.R.f : ℝ) * (D.R.m : ℝ)) ^ 4 ≤ 16 * zBase large₂ ^ 5 := by
    calc (2 * (D.R.f : ℝ) * (D.R.m : ℝ)) ^ 4 = 16 * ((D.R.f : ℝ) ^ 4 * (D.R.m : ℝ) ^ 4) := by ring
      _ ≤ 16 * (zBase large₂ ^ 4 * zBase large₂) := by gcongr
      _ = 16 * zBase large₂ ^ 5 := by ring
  have key := indexBound_threeTerm_constant_le_real (nW : ℝ) ((D.R.m : ℝ) ^ 4) (2 * (D.R.f : ℝ) * (D.R.m : ℝ)) (D.R.r : ℝ) C2 (zBase large₂) hZ
    (by linarith) (Nat.cast_nonneg _) (hnW.trans h12) (by positivity) hm hu1 hu hr
  have hZA : zBase large₂ ^ (12 : ℕ) ≤ zBase large₂ ^ A2 := by
    calc zBase large₂ ^ (12 : ℕ) = zBase large₂ ^ ((12 : ℕ) : ℝ) := (Real.rpow_natCast _ _).symm
      _ ≤ zBase large₂ ^ A2 := Real.rpow_le_rpow_of_exponent_le (by linarith) (by exact_mod_cast hA)
  unfold flipOneThree WeightFamilies.PPv
  exact key.trans (mul_le_mul_of_nonneg_left hZA (by linarith))

end GlobalTheory.FinalJoin
