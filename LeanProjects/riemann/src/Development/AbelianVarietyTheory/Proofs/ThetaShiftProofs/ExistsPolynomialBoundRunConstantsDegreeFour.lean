import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.CarchAt
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsBoundedByPowerOfAtLeastTwoInvD4ep0
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.LogLeSelf

section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

namespace GlobalTheory.SplitConst

theorem constants_bounded_sq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r p0 g NA NC : ℕ) (c₁ w Z : ℝ), 3 ≤ r → 1 ≤ p0 → p0 ≤ r → 1 ≤ g → 1 ≤ NA → 1 ≤ NC → 0 < c₁ → 1 ≤ w → 1 ≤ Z → (fdeg E : ℝ) ≤ Z → (r : ℝ) ≤ Z → Real.log (dE E) ≤ Z → Real.log g ≤ Z → Real.log NA ≤ Z → Real.log NC ≤ Z → Real.log c₁ ≤ Z → Real.log w ≤ Z → Real.log (nQ E r g NA NC c₁ w) ≤ 200 * Z ^ 2 ∧ Real.log (LaQ E r p0 g NA NC c₁ w) ≤ 200 * Z ^ 2 := by
  intro E _ _ _ r p0 g NA NC c w Z hr hp hpr hg hNA hNC hc hw hZ hfZ hrZ hdZ hgZ hNAZ hNCZ hcZ hwZ
  have hZX : Z + 1 ≤ Real.exp Z := Real.add_one_le_exp Z
  set X := Real.exp Z with hXdef
  have hX : 2 ≤ X := by linarith
  have le_of_log : ∀ a : ℝ, 0 < a → Real.log a ≤ Z → a ≤ X := fun a ha h => (Real.log_le_iff_le_exp ha).1 h
  have hd : 1 ≤ dE E := by
    unfold dE
    have := NumberField.discr_ne_zero E
    have h2 : (1 : ℤ) ≤ |NumberField.discr E| := Int.one_le_abs this
    exact_mod_cast h2
  have hn : 2 ≤ Module.finrank ℚ E := by
    have h1 := Module.finrank_mul_finrank ℚ (NumberField.maximalRealSubfield E) E
    have h2 : Module.finrank (NumberField.maximalRealSubfield E) E = 2 := Algebra.IsQuadraticExtension.finrank_eq_two _ _
    have h3 : 0 < Module.finrank ℚ (NumberField.maximalRealSubfield E) := Module.finrank_pos
    rw [h2] at h1
    omega
  have hf : (1 : ℝ) ≤ fdeg E := by
    have : 1 ≤ fdeg E := by unfold fdeg; omega
    exact_mod_cast this
  have hg1 : (1 : ℝ) ≤ g := by exact_mod_cast hg
  have hNA1 : (1 : ℝ) ≤ NA := by exact_mod_cast hNA
  have hNC1 : (1 : ℝ) ≤ NC := by exact_mod_cast hNC
  have hd' := le_of_log _ (by linarith) hdZ
  have hg' := le_of_log _ (by linarith) hgZ
  have hNA' := le_of_log _ (by linarith) hNAZ
  have hNC' := le_of_log _ (by linarith) hNCZ
  have hc' := le_of_log _ hc hcZ
  have hw' := le_of_log _ (by linarith) hwZ
  have hf' : (fdeg E : ℝ) ≤ X := by linarith
  have pe := isBoundedByPowerOfAtLeastTwo_inv_d4ep0 hX hg1 hd hf hNA1 hNC1 hc hw hg' hd' hf' hNA' hNC' hc' hw'
  have ph := rh_inv hX hc hw hc' hw'
  have pd := PB.base hX (by linarith) hd'
  have pf := PB.base hX (by linarith) hf'
  have pNA := PB.base hX (by linarith) hNA'
  have pNC := PB.base hX (by linarith) hNC'
  have pr : PB X 1 ((r - 2 : ℕ) : ℝ) := by
    refine PB.base hX (by positivity) ?_
    have : ((r - 2 : ℕ) : ℝ) ≤ r := by exact_mod_cast Nat.sub_le r 2
    linarith
  have prd : PB X 1 (rdE E) :=
    pd.of_le (Real.rpow_nonneg (by linarith) _) (rpow_le_self hd (by
      have : 1 ≤ Module.finrank ℚ E := by omega
      exact_mod_cast this))
  have p1 : PB X 0 1 := PB.const hX 0 (by norm_num) (by norm_num)
  have p2 : PB X 1 2 := PB.const hX 1 (by norm_num) (by norm_num)
  have p4 : PB X 2 4 := PB.const hX 2 (by norm_num) (by norm_num)
  have p40 : PB X 6 40 := PB.const hX 6 (by norm_num) (by norm_num)
  have p1000 : PB X 10 1000 := PB.const hX 10 (by norm_num) (by norm_num)
  set ep := flowEpsilonBound g (dE E) (fdeg E) NA NC c w
  set rh := d6rh c w
  have hZ2 : Z ≤ Z ^ 2 := by nlinarith
  constructor
  · have pm := (((pf.mul (((p2.mul pf).mul pr).pow 3)).mul pd).mul pNA).mul ((pNC.pow 2).mul prd |>.mul pe).sqrt
    have py := (p1000.mul pm).mul ph
    have hy : 1000 * frameIndexBound r (fdeg E) (dE E) (rdE E) NA NC ep / rh =
        1000 * ((fdeg E : ℝ) * (2 * (fdeg E : ℝ) * ((r - 2 : ℕ) : ℝ)) ^ 3 * dE E * NA * √((NC : ℝ) ^ 2 * rdE E * ep⁻¹)) * rh⁻¹ := by
      unfold frameIndexBound
      rw [div_eq_mul_inv, div_eq_mul_inv, Nat.cast_mul, Nat.cast_mul, Nat.cast_ofNat]
    rw [← hy] at py
    have pn : PB X 100 (nQ E r g NA NC c w : ℝ) := by
      refine (((py.add p1).add p1).mono (by norm_num)).of_le (by positivity) ?_
      unfold nQ
      push_cast
      have := Nat.ceil_lt_add_one py.2.1
      linarith
    have := pn.log_le (by unfold nQ; positivity)
    push_cast at this
    nlinarith
  · have pmu := ((p4.mul ((pf.mul pr).pow 3)).mul pd).mul pe.sqrt
    have pb := ((p2.mul (((p4.mul pr.sqrt).mul pmu).mul (p40.mul ph))).mono (j := 100) (by norm_num)).pow (2 * p0 - 1)
    have hy : d6La r p0 (fdeg E) (dE E) ep rh =
        (2 * (4 * √((r - 2 : ℕ) : ℝ) * (4 * ((fdeg E : ℝ) * ((r - 2 : ℕ) : ℝ)) ^ 3 * dE E * √(ep⁻¹)) * (40 * rh⁻¹))) ^
          (2 * p0 - 1) := by
      unfold d6La ReciprocityTheory.MultiplicativeHeights.approxR d5mu
      rw [div_eq_mul_inv _ (rh / 40), inv_div, div_eq_mul_inv 40, div_eq_mul_inv, ← Real.sqrt_inv]
    rw [← hy] at pb
    have pL : PB X (100 * (2 * p0 - 1)) (LaQ E r p0 g NA NC c w) := by
      unfold LaQ
      rcases max_choice (1 : ℝ) _ with h | h <;> rw [h]
      · exact p1.mono (Nat.zero_le _)
      · exact pb
    have h1 := pL.log_le (lt_of_lt_of_le one_pos (le_max_left _ _))
    have h2 : ((100 * (2 * p0 - 1) : ℕ) : ℝ) ≤ 200 * r := by
      have : 100 * (2 * p0 - 1) ≤ 200 * r := by omega
      exact_mod_cast this
    have h3 : ((100 * (2 * p0 - 1) : ℕ) : ℝ) * Z ≤ (200 * Z) * Z :=
      mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    nlinarith

theorem constants_bounded_four : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r p0 g NA NC : ℕ) (c₁ w Z : ℝ), 3 ≤ r → 1 ≤ p0 → p0 ≤ r → 1 ≤ g → 1 ≤ NA → 1 ≤ NC → 0 < c₁ → 1 ≤ w → 1 ≤ Z → (fdeg E : ℝ) ≤ Z → (r : ℝ) ≤ Z → Real.log (dE E) ≤ Z → Real.log g ≤ Z → Real.log NA ≤ Z → Real.log NC ≤ Z → Real.log c₁ ≤ Z → Real.log w ≤ Z → Real.log (nQ E r g NA NC c₁ w) ≤ 200 * Z ^ (4 : ℝ) ∧ Real.log (LaQ E r p0 g NA NC c₁ w) ≤ 200 * Z ^ (4 : ℝ) := by
  intro E _ _ _ r p0 g NA NC c w Z hr hp hpr hg hNA hNC hc hw hZ hfZ hrZ hdZ hgZ hNAZ hNCZ hcZ hwZ
  obtain ⟨h1, h2⟩ := constants_bounded_sq E r p0 g NA NC c w Z hr hp hpr hg hNA hNC hc hw hZ hfZ hrZ hdZ hgZ
    hNAZ hNCZ hcZ hwZ
  have h3 : Z ^ 2 ≤ Z ^ (4 : ℝ) := by
    rw [← Real.rpow_two]
    exact Real.rpow_le_rpow_of_exponent_le hZ (by norm_num)
  constructor <;> linarith

end GlobalTheory.SplitConst

end

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.Pj.QAt Formalism.MainNotions Formalism.BasicNotions Formalism.L2.LamCM GlobalTheory.ArcCM

namespace GlobalTheory.ArcCM.Room

set_option maxHeartbeats 1000000 in

theorem room_four : ∃ C₀ : ℝ → ℝ → ℝ → ℝ, (∀ a b c, 0 ≤ C₀ a b c) ∧ ∀ (D : D7) (large₂ : SizeData₂ D) (j : ℕ) (ka : WeightFamilies.Wt D j) (CA CR Ck Tt cc : ℝ), WeightAlgebra.ParA large₂ CA → Real.log (Ideal.absNorm D.host.ccK) ≤ large₂.sc.L → InR D j → j < D.R.m → 3 ≤ D.R.r → 0 ≤ CR → ka.size ≤ Ck * (D.R.k : ℝ) * (D.R.f : ℝ) * large₂.sc.b → 0 < Tt → 0 < cc → Tt * cc ≤ 1 → 1 ≤ zBase large₂ ∧ RoomAt large₂ j ka CR Tt cc (C₀ CA CR Ck) 4 := by
  set C : ℝ := 200 with hCdef
  set A : ℝ := 4 with hAdef
  have hC : 0 ≤ C := by norm_num [hCdef]
  have hA : 1 ≤ A := by norm_num [hAdef]
  have H := GlobalTheory.SplitConst.constants_bounded_four
  rw [← hCdef, ← hAdef] at H
  refine ⟨fun a b c => 17 + 2 * (20 + |a| + |b| * |a| + |c|) + C * (20 + |a| + |b| * |a| + |c|) ^ A,
    fun a b c => by positivity, ?_⟩
  intro D large₂ j ka CA CR Ck Tt cc hpar hNC hj hjm hr3 hCR hka hT hcc hTc
  obtain ⟨-, -, hdE, -, hg, -, hOm, -, -, -⟩ := hpar
  have : IsCMField D.host.E := D.host.isCMField_hostE
  set K : ℝ := 20 + |CA| + |CR| * |CA| + |Ck| with hKdef
  have ha0 := abs_nonneg CA
  have hb0 := abs_nonneg CR
  have hc0 := abs_nonneg Ck
  have hab0 : 0 ≤ |CR| * |CA| := mul_nonneg hb0 ha0
  have hK : 20 ≤ K := by rw [hKdef]; linarith
  have hL1 : 1 ≤ large₂.sc.L := Real.one_le_rpow large₂.sc.one_lt_alt.le large₂.sc.eps_pos.le
  have hfN : 1 ≤ D.R.f := by
    unfold Ranks.f Ranks.n
    have := And.intro (Nat.one_le_two_pow (n := D.R.e)) (show 0 < D.R.ord by positivity)
    omega
  have hf1 : (1 : ℝ) ≤ D.R.f := by exact_mod_cast hfN
  have hr1 : (1 : ℝ) ≤ D.R.r := by exact_mod_cast (by omega : 1 ≤ D.R.r)
  have hm2 := D.R.two_le_m
  have hmk := D.R.m_add_three_le_k
  have hkr : (D.R.k : ℝ) ≤ D.R.r := by
    have : D.R.k ≤ D.R.r := by unfold Ranks.r; omega
    exact_mod_cast this
  have hp1 : 1 ≤ (D.R.sigW j).2 := by unfold Ranks.sigW; simp only; omega
  have hpr : (D.R.sigW j).2 ≤ D.R.r := by unfold Ranks.sigW Ranks.r; simp only; omega
  set z : ℝ := zBase large₂ with hz
  have hzdef : z = (D.R.f : ℝ) * D.R.r * large₂.sc.L := rfl
  have hfr1 : (1 : ℝ) ≤ (D.R.f : ℝ) * D.R.r := one_le_mul_of_one_le_of_one_le hf1 hr1
  have hfrz : (D.R.f : ℝ) * D.R.r ≤ z := le_mul_of_one_le_right (by linarith) hL1
  have hLz : large₂.sc.L ≤ z := le_mul_of_one_le_left (by linarith) hfr1
  have hz1 : 1 ≤ z := by linarith
  have hfz : (D.R.f : ℝ) ≤ z := (le_mul_of_one_le_right (by linarith) hr1).trans hfrz
  have hrz : (D.R.r : ℝ) ≤ z := (le_mul_of_one_le_left (by linarith) hf1).trans hfrz
  have hzK : 20 * z ≤ K * z := mul_le_mul_of_nonneg_right hK (by linarith)
  have hKz : K * z = 20 * z + |CA| * z + |CR| * |CA| * z + |Ck| * z := by rw [hKdef]; ring
  have haz : 0 ≤ |CA| * z := by positivity
  have habz : 0 ≤ |CR| * |CA| * z := by positivity
  have hcz : 0 ≤ |Ck| * z := by positivity
  have hd : Real.log |((discr D.host.E : ℤ) : ℝ)| ≤ |CA| * z := by
    refine hdE.trans ?_
    rw [← hzdef]
    exact mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith)
  have hd1 : (1 : ℝ) ≤ |((discr D.host.E : ℤ) : ℝ)| := by
    have := Int.one_le_abs (discr_ne_zero D.host.E)
    exact_mod_cast this
  have hd0 : 0 ≤ Real.log |((discr D.host.E : ℤ) : ℝ)| := Real.log_nonneg hd1
  have hrd0 : 0 < D.host.rdE := (rdE_pos_le D).1
  have hrd : Real.log D.host.rdE ≤ |CA| * z := by
    have h1 := logdE_eq_rd D
    have h2 : logdE D = Real.log |((discr D.host.E : ℤ) : ℝ)| := rfl
    rw [h2] at h1
    have h3 : 0 ≤ Real.log D.host.rdE := by
      exact nonneg_of_mul_nonneg_right (h1 ▸ hd0) (by linarith)
    exact (le_mul_of_one_le_left h3 (by linarith)).trans (h1 ▸ hd)
  have hfdeg : fdeg D.host.E = D.R.f := by
    unfold fdeg
    rw [D.host.finrank_cmField]
    unfold Ranks.f Ranks.n
    omega
  have hg0 := (D.host.g_prime 0).one_le
  have hg1 := (D.host.g_prime 1).one_le
  have hlg : Real.log ((D.host.g 0 * D.host.g 1 : ℕ) : ℝ) ≤ K * z := by
    have e0 : ((D.host.g 0 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (by omega : D.host.g 0 ≠ 0)
    have e1 : ((D.host.g 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (by omega : D.host.g 1 ≠ 0)
    rw [Nat.cast_mul, Real.log_mul e0 e1]
    have := hg 0
    have := hg 1
    linarith
  have hNA : (((discr D.host.E).natAbs : ℕ) : ℝ) = |((discr D.host.E : ℤ) : ℝ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  have hNA1 : 1 ≤ (discr D.host.E).natAbs := Int.natAbs_pos.2 (discr_ne_zero D.host.E)
  have hNC1 : 1 ≤ Ideal.absNorm D.host.ccK :=
    Nat.one_le_iff_ne_zero.2 (fun h => D.host.ccK_ne_bot (Ideal.absNorm_eq_zero_iff.1 h))
  have hρ1 : (1 : ℝ) ≤ WeightFamilies.rho D j := by exact_mod_cast hp1
  have hρr : (WeightFamilies.rho D j : ℝ) ≤ D.R.r := by exact_mod_cast hpr
  have hdP : (WeightFamilies.dP D j : ℝ) = 2 * D.R.f * WeightFamilies.rho D j := by unfold WeightFamilies.dP; push_cast; ring
  have hdP1 : (1 : ℝ) ≤ WeightFamilies.dP D j := by
    rw [hdP]; exact one_le_mul_of_one_le_of_one_le (by linarith) hρ1
  have hdPz : (WeightFamilies.dP D j : ℝ) ≤ 2 * z := by
    have := mul_le_mul_of_nonneg_left hρr (by linarith : (0 : ℝ) ≤ D.R.f)
    rw [hdP]; linarith
  have hRR : 0 < WeightFamilies.RRv D CR := Real.rpow_pos_of_pos hrd0 _
  have hc1 : 0 < WeightFamilies.c1 D CR Tt cc j := by unfold WeightFamilies.c1; positivity
  have hlc : Real.log (WeightFamilies.c1 D CR Tt cc j) ≤ K * z := by
    have h1 : WeightFamilies.c1 D CR Tt cc j ≤ WeightFamilies.RRv D CR * (WeightFamilies.dP D j : ℝ) ^ 2 * (WeightFamilies.rho D j : ℝ) := by
      have h0 : 0 < WeightFamilies.RRv D CR * (WeightFamilies.dP D j : ℝ) ^ 2 * (WeightFamilies.rho D j : ℝ) := by positivity
      have : WeightFamilies.c1 D CR Tt cc j =
          (WeightFamilies.RRv D CR * (WeightFamilies.dP D j : ℝ) ^ 2 * (WeightFamilies.rho D j : ℝ)) * (Tt * cc) / 2 := by
        unfold WeightFamilies.c1; ring
      rw [this]
      have := mul_le_of_le_one_right h0.le hTc
      linarith
    refine (Real.log_le_log hc1 h1).trans ?_
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_pow]
    have h2 : Real.log (WeightFamilies.RRv D CR) = CR * Real.log D.host.rdE := Real.log_rpow hrd0 _
    have h3 : CR * Real.log D.host.rdE ≤ |CR| * |CA| * z := by
      rw [abs_of_nonneg hCR, mul_assoc]
      exact mul_le_mul_of_nonneg_left hrd hCR
    have h4 := log_le_self' (by linarith : (0 : ℝ) ≤ WeightFamilies.dP D j)
    have h5 := log_le_self' (by linarith : (0 : ℝ) ≤ WeightFamilies.rho D j)
    push_cast
    linarith
  have hs1 := ka.one_le_size
  have hlw : Real.log (ka.size + D.R.r) ≤ K * z := by
    have hb1 : 1 ≤ large₂.sc.b := Real.one_le_exp (by linarith)
    have h1 : Ck * (D.R.k : ℝ) * (D.R.f : ℝ) ≤ |Ck| * z := by
      rw [mul_assoc]
      refine mul_le_mul (le_abs_self _) ?_ (by positivity) hc0
      have := mul_le_mul_of_nonneg_right hkr (by linarith : (0 : ℝ) ≤ D.R.f)
      linarith
    have h2 : ka.size ≤ |Ck| * z * large₂.sc.b := hka.trans (mul_le_mul_of_nonneg_right h1 (by linarith))
    have h3 : ka.size + D.R.r ≤ (|Ck| * z + z) * large₂.sc.b := by
      have := le_mul_of_one_le_right (by linarith : (0 : ℝ) ≤ z) hb1
      linarith
    refine (Real.log_le_log (by linarith) h3).trans ?_
    rw [Real.log_mul (by positivity) (by positivity)]
    have h4 : Real.log large₂.sc.b = large₂.sc.L := Real.log_exp _
    have h5 := log_le_self' (by linarith : (0 : ℝ) ≤ |Ck| * z + z)
    linarith
  obtain ⟨hn, hLa⟩ := H D.host.E D.R.r (D.R.sigW j).2 (D.host.g 0 * D.host.g 1) (discr D.host.E).natAbs
    (Ideal.absNorm D.host.ccK) (WeightFamilies.c1 D CR Tt cc j) (ka.size + D.R.r) (K * z) hr3 hp1 hpr
    (Nat.mul_pos hg0 hg1) hNA1 hNC1 hc1 (by linarith) (by linarith) (by rw [hfdeg]; linarith) (by linarith)
    (by unfold dE; linarith) hlg (by rw [hNA]; linarith) (by linarith) hlc hlw
  rw [Real.mul_rpow (by linarith) (by linarith), ← mul_assoc] at hn hLa
  have hP : z ≤ z ^ A := by
    have := Real.rpow_le_rpow_of_exponent_le hz1 hA
    rwa [Real.rpow_one] at this
  have hmax : Real.log (max 1 (WeightFamilies.c1 D CR Tt cc j)) ≤ K * z := by
    rcases max_choice 1 (WeightFamilies.c1 D CR Tt cc j) with h | h <;> rw [h]
    · rw [Real.log_one]; linarith
    · exact hlc
  have ho : |large₂.logOm| ≤ K * z := by
    have : CA * large₂.sc.L ≤ |CA| * z := mul_le_mul (le_abs_self _) hLz (by linarith) ha0
    linarith
  have hR : Real.log (D.R.r : ℝ) ≤ z := (log_le_self' (by linarith)).trans hrz
  refine ⟨hz1, ?_⟩
  exact assemble K (C * K ^ A) (z ^ A) z ka.size _ _ (Real.log D.host.rdE) _ _ _ _ hz1 hP (by linarith)
    (by positivity) hs1 hmax hLa (by linarith) hR ho (by linarith) hn

end GlobalTheory.ArcCM.Room
