import Mathlib
import Formalism.GL3MeanSquares.PrimeCountAsymptoticInProgressions
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Formalism.CyclotomicNorms.StatementI
import Development.AbelianVarietyTheory.Definitions.Foundations.RayPrimes
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExplZeta
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExplChi
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LogDerOne
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ZeroCount
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DirichletLZerosInWindowFiniteAndPosOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SumIndicatorLeZsumR
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Psi0TruncatedExplicitFormula
open Finset ArithmeticFunction NumberField IsDedekindDomain Filter Topology GlobalTheory.Mem.An Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab
open scoped nonZeroDivisors

namespace GlobalTheory.Mem.An.PsiFix

theorem norm_psi0_le {q : ℕ} (χ : DirichletCharacter ℂ q) (u : ℝ) (hu : 1 ≤ u) :
    ‖GlobalTheoryTheory.psi0 χ u‖ ≤ u * (Real.log u + 1) := by
  have hl : 0 ≤ Real.log u := Real.log_nonneg hu
  unfold GlobalTheoryTheory.psi0
  refine (norm_sub_le _ _).trans ?_
  have h1 : ‖∑ n ∈ Finset.Icc 1 ⌊u⌋₊, (GlobalTheoryTheory.abelian₂ n : ℂ) * χ (n : ZMod q)‖ ≤ u * Real.log u := by
    refine (norm_sum_le _ _).trans ?_
    have : ∀ n ∈ Finset.Icc 1 ⌊u⌋₊, ‖(GlobalTheoryTheory.abelian₂ n : ℂ) * χ (n : ZMod q)‖ ≤ Real.log u := by
      intro n hn
      have hn' := Finset.mem_Icc.1 hn
      have hnu : (n : ℝ) ≤ u := (Nat.cast_le.2 hn'.2).trans (Nat.floor_le (by linarith))
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn'.1
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg vonMangoldt_nonneg]
      calc Λ n * ‖χ (n : ZMod q)‖ ≤ Λ n * 1 :=
            mul_le_mul_of_nonneg_left (χ.norm_le_one _) vonMangoldt_nonneg
        _ ≤ Real.log n := by rw [mul_one]; exact vonMangoldt_le_log
        _ ≤ Real.log u := Real.log_le_log hn0 hnu
    refine (Finset.sum_le_card_nsmul _ _ _ this).trans ?_
    rw [Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (Nat.floor_le (by linarith)) hl
  refine (add_le_add h1 (?_ : _ ≤ u)).trans (le_of_eq (by ring))
  split_ifs
  · rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  · simp; linarith

theorem exists_re_le (hZ : Formalism.ZeroFreeDirichlet.ZFRDirichlet) (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ s : ℝ, 1 ≤ s → Real.log (3 * q) ≤ s →
      ∀ ρ ∈ zerosIn χ 0 (Real.exp s), ρ.re ≤ 1 - c / s := by
  obtain ⟨c0, hc0, hZ⟩ := hZ
  have hfin := (ZeroWindow.finite_and_one_le_zmult q χ 0 0).1
  obtain ⟨δ, hδ, hδ'⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ ρ ∈ zerosIn χ 0 0, ρ.re ≤ 1 - δ := by
    rcases (zerosIn χ 0 0).eq_empty_or_nonempty with h | h
    · exact ⟨1, one_pos, by simp [h]⟩
    · obtain ⟨ρ0, h0, hmax⟩ := Set.exists_max_image _ (fun ρ : ℂ => ρ.re) hfin h
      exact ⟨1 - ρ0.re, by linarith [h0.2.1], fun ρ hρ => by linarith [hmax ρ hρ]⟩
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  refine ⟨min (min (c0 / 2) δ) 1, by positivity, min_le_right _ _, fun s hs hs' ρ hρ => ?_⟩
  have hm1 : min (min (c0 / 2) δ) 1 ≤ c0 / 2 := (min_le_left _ _).trans (min_le_left _ _)
  have hm2 : min (min (c0 / 2) δ) 1 ≤ δ := (min_le_left _ _).trans (min_le_right _ _)
  have hs0 : 0 < s := by linarith
  by_cases him : ρ.im = 0
  · have := hδ' ρ ⟨hρ.1, hρ.2.1, by simp [him], hρ.2.2.2⟩
    have h2 : min (min (c0 / 2) δ) 1 / s ≤ δ := by
      rw [div_le_iff₀ hs0]; nlinarith
    linarith
  · have hne : ρ ≠ 1 := by
      intro h; apply him; simp [h]
    have hnot : ¬ Formalism.ZeroFreeDirichlet.InRegion c0 q ρ := fun h => him (hZ q χ ρ h ⟨Or.inr hne, hρ.2.2.2⟩).2.2.1
    unfold Formalism.ZeroFreeDirichlet.InRegion at hnot
    push Not at hnot
    have hg : |ρ.im| ≤ Real.exp s := by simpa using hρ.2.2.1
    have he : 1 ≤ Real.exp s := Real.one_le_exp hs0.le
    have ha : 0 ≤ |ρ.im| := abs_nonneg _
    have hpos : 0 < Real.log (q * (|ρ.im| + 2)) := Real.log_pos (by nlinarith)
    have hle : Real.log (q * (|ρ.im| + 2)) ≤ 2 * s := by
      calc Real.log (q * (|ρ.im| + 2)) ≤ Real.log ((3 * q) * Real.exp s) :=
            Real.log_le_log (by positivity) (by nlinarith)
        _ = Real.log (3 * q) + s := by
            rw [Real.log_mul (by positivity) (by positivity), Real.log_exp]
        _ ≤ 2 * s := by linarith
    have h3 : min (min (c0 / 2) δ) 1 / s ≤ c0 / Real.log (q * (|ρ.im| + 2)) := by
      calc min (min (c0 / 2) δ) 1 / s ≤ (c0 / 2) / s := div_le_div_of_nonneg_right hm1 hs0.le
        _ = c0 / (2 * s) := by rw [div_div]
        _ ≤ _ := div_le_div_of_nonneg_left hc0.le hpos hle
    linarith

theorem zsumR_recip_split {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (T : ℝ) :
    zsumR χ 0 T (fun ρ => 1 / ‖ρ‖) ≤ zsumR χ 0 1 (fun ρ => 1 / ‖ρ‖) +
      zsumR χ 0 T (fun ρ => if 1 < |ρ.im| then 1 / ‖ρ‖ else 0) := by
  classical
  have h1 := (ZeroWindow.finite_and_one_le_zmult q χ 0 1).1
  have hT := (ZeroWindow.finite_and_one_le_zmult q χ 0 T).1
  rw [zsumR_eq_sum_toFinset χ 0 T _ hT, zsumR_eq_sum_toFinset χ 0 T _ hT, zsumR_eq_sum_toFinset χ 0 1 _ h1]
  rw [← Finset.sum_filter_add_sum_filter_not hT.toFinset (fun ρ : ℂ => 1 < |ρ.im|), add_comm]
  refine add_le_add ?_ (le_of_eq ?_)
  · refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
    intro ρ hρ
    obtain ⟨ha, hb⟩ := Finset.mem_filter.1 hρ
    have ha' : ρ ∈ zerosIn χ 0 T := by simpa using ha
    simp only [Set.Finite.mem_toFinset]
    exact ⟨ha'.1, ha'.2.1, by simpa using hb, ha'.2.2.2⟩
  · rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    split_ifs <;> simp

theorem norm_zsum_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (T u B : ℝ)
    (hB : ∀ ρ ∈ zerosIn χ 0 T, ‖(u : ℂ) ^ ρ‖ ≤ B) :
    ‖zsum χ 0 T (fun ρ => (u : ℂ) ^ ρ / ρ)‖ ≤ B * zsumR χ 0 T (fun ρ => 1 / ‖ρ‖) := by
  have hT := (ZeroWindow.finite_and_one_le_zmult q χ 0 T).1
  rw [zsumR_eq_sum_toFinset χ 0 T _ hT, zsum, finsum_mem_eq_finite_toFinset_sum _ hT, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ρ hρ => ?_)
  have h := hB ρ (by simpa using hρ)
  rw [norm_mul, norm_div, Complex.norm_natCast]
  calc (zmult χ ρ : ℝ) * (‖(u : ℂ) ^ ρ‖ / ‖ρ‖) ≤ (zmult χ ρ : ℝ) * (B / ‖ρ‖) := by gcongr
    _ = _ := by ring

theorem large (h1 : ExplZeta) (h2 : ExplChi) (h3 : LogDerOne) (h4 : ZeroCount) (hZ : Formalism.ZeroFreeDirichlet.ZFRDirichlet)
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) :
    ∃ K c : ℝ, 0 ≤ K ∧ 0 < c ∧ ∀ s : ℝ, 1 ≤ s → Real.log (3 * q) ≤ s →
      ‖GlobalTheoryTheory.psi0 χ (Real.exp (s ^ 2))‖ ≤ K * s ^ 4 * (Real.exp (s ^ 2) * Real.exp (-c * s)) := by
  obtain ⟨c, hc, hc1, hre⟩ := exists_re_le hZ q χ
  obtain ⟨C1, hC1⟩ := GlobalTheory.Mem.An.ExplUsed.explicit_formula_used h1 h2 h3
  obtain ⟨C2, hC2⟩ := zsumR_recip_le h4
  set A := zsumR χ 0 1 (fun ρ => 1 / ‖ρ‖) with hA
  have hA0 : 0 ≤ A := by
    rw [hA, zsumR_eq_sum_toFinset χ 0 1 _ (ZeroWindow.finite_and_one_le_zmult q χ 0 1).1]
    positivity
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  refine ⟨|C1| * (9 + 2 + A) + (A + 4 * |C2|), c, by positivity, hc, fun s hs hs' => ?_⟩
  have hs0 : 0 < s := by linarith
  have hss : s ≤ s ^ 2 := by nlinarith
  have hT2 : 2 ≤ Real.exp s := by linarith [Real.add_one_le_exp s]
  have hTu : Real.exp s ≤ Real.exp (s ^ 2) := Real.exp_le_exp.2 hss
  have hlq : Real.log q ≤ s := (Real.log_le_log (by linarith) (by linarith)).trans hs'
  have hlq0 : 0 ≤ Real.log q := Real.log_nonneg hq
  have e1 := hC1 q χ hχ _ _ hT2 hTu
  have e2 := (hC2 q χ hχ _ hT2).1
  set u := Real.exp (s ^ 2) with hu
  have hu0 : 0 < u := Real.exp_pos _
  set E := u * Real.exp (-c * s) with hE
  have l1 : Real.log (q * u) = Real.log q + s ^ 2 := by
    rw [Real.log_mul (by positivity) hu0.ne', hu, Real.log_exp]
  have l2 : Real.log (q * u * Real.exp s) = Real.log q + s ^ 2 + s := by
    rw [Real.log_mul (by positivity) (by positivity), l1, Real.log_exp]
  have l3 : Real.log (q * Real.exp s) = Real.log q + s := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_exp]
  rw [l1, l2, ← hA] at e1
  rw [l3] at e2
  have hE1 : u / Real.exp s ≤ E := by
    rw [hE, div_eq_mul_inv, ← Real.exp_neg]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by nlinarith)) hu0.le
  have hE2 : 1 ≤ E := le_trans (by rw [le_div_iff₀ (Real.exp_pos _)]; linarith) hE1
  have hB : ∀ ρ ∈ zerosIn χ 0 (Real.exp s), ‖(u : ℂ) ^ ρ‖ ≤ E := by
    intro ρ hρ
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hu0, hE, hu, ← Real.exp_mul, ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    calc s ^ 2 * ρ.re ≤ s ^ 2 * (1 - c / s) := mul_le_mul_of_nonneg_left (hre s hs hs' ρ hρ) (by positivity)
      _ = _ := by field_simp; ring
  have e3 := norm_zsum_le χ _ u E hB
  have e4 := zsumR_recip_split χ (Real.exp s)
  rw [← hA] at e4
  have hs4 : 1 ≤ s ^ 4 := one_le_pow₀ hs
  have hs24 : s ^ 2 ≤ s ^ 4 := pow_le_pow_right₀ hs (by norm_num)
  have e5 : zsumR χ 0 (Real.exp s) (fun ρ => 1 / ‖ρ‖) ≤ (A + 4 * |C2|) * s ^ 4 := by
    have a1 : C2 * (Real.log q + s) ^ 2 ≤ |C2| * (4 * s ^ 4) :=
      (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)).trans
        (mul_le_mul_of_nonneg_left (by nlinarith) (abs_nonneg _))
    have a2 : A ≤ A * s ^ 4 := le_mul_of_one_le_right hA0 hs4
    linarith
  have e6 : u * (Real.log q + s ^ 2 + s) ^ 2 / Real.exp s + (Real.log q + s ^ 2) + A ≤
      (9 + 2 + A) * s ^ 4 * E := by
    have a1 : (Real.log q + s ^ 2 + s) ^ 2 ≤ 9 * s ^ 4 := by
      calc (Real.log q + s ^ 2 + s) ^ 2 ≤ (3 * s ^ 2) ^ 2 :=
            pow_le_pow_left₀ (by positivity) (by linarith) 2
        _ = _ := by ring
    have a2 : u * (Real.log q + s ^ 2 + s) ^ 2 / Real.exp s ≤ 9 * s ^ 4 * E := by
      calc u * (Real.log q + s ^ 2 + s) ^ 2 / Real.exp s
          = (Real.log q + s ^ 2 + s) ^ 2 * (u / Real.exp s) := by ring
        _ ≤ _ := mul_le_mul a1 hE1 (by positivity) (by positivity)
    have a3 : (2 + A) * s ^ 4 ≤ (2 + A) * s ^ 4 * E := le_mul_of_one_le_right (by positivity) hE2
    have a4 : A ≤ A * s ^ 4 := le_mul_of_one_le_right hA0 hs4
    linarith
  have e7 : C1 * (u * (Real.log q + s ^ 2 + s) ^ 2 / Real.exp s + (Real.log q + s ^ 2) + A) ≤
      |C1| * ((9 + 2 + A) * s ^ 4 * E) :=
    (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)).trans
        (mul_le_mul_of_nonneg_left e6 (abs_nonneg _))
  have e8 : E * zsumR χ 0 (Real.exp s) (fun ρ => 1 / ‖ρ‖) ≤ E * ((A + 4 * |C2|) * s ^ 4) :=
    mul_le_mul_of_nonneg_left e5 (by linarith)
  have e9 := norm_sub_le (GlobalTheoryTheory.psi0 χ u + zsum χ 0 (Real.exp s) (fun ρ => (u : ℂ) ^ ρ / ρ))
    (zsum χ 0 (Real.exp s) (fun ρ => (u : ℂ) ^ ρ / ρ))
  rw [add_sub_cancel_right] at e9
  linarith

end GlobalTheory.Mem.An.PsiFix

namespace GlobalTheory.Mem.An

theorem psi0_le_exp_neg_sqrt_log : GlobalTheory.Mem.An.ExplZeta → GlobalTheory.Mem.An.ExplChi → GlobalTheory.Mem.An.LogDerOne →
    GlobalTheory.Mem.An.ZeroCount → Formalism.ZeroFreeDirichlet.ZFRDirichlet →
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → ∃ C c : ℝ, 0 < c ∧ ∀ u : ℝ, 2 ≤ u →
      ‖GlobalTheoryTheory.psi0 χ u‖ ≤ C * u * Real.exp (-c * Real.sqrt (Real.log u)) := by
  intro h1 h2 h3 h4 hZ q _ χ hχ
  obtain ⟨K, c, hK, hc, hl⟩ := PsiFix.large h1 h2 h3 h4 hZ q χ hχ
  set S := max 1 (Real.log (3 * q)) with hS
  refine ⟨K * (24 / (c / 2) ^ 4) + (S ^ 2 + 1) * Real.exp (c / 2 * S), c / 2, by positivity, fun u hu => ?_⟩
  have hu0 : 0 < u := by linarith
  have hlu : 0 ≤ Real.log u := Real.log_nonneg (by linarith)
  set s := Real.sqrt (Real.log u) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hsq : s ^ 2 = Real.log u := Real.sq_sqrt hlu
  have hF : 0 < u * Real.exp (-(c / 2) * s) := by positivity
  have hp1 : 0 ≤ K * (24 / (c / 2) ^ 4) := by positivity
  have hp2 : 0 ≤ (S ^ 2 + 1) * Real.exp (c / 2 * S) := by positivity
  rw [mul_assoc]
  rcases le_total S s with h | h
  · have e := hl s ((le_max_left _ _).trans h) ((le_max_right _ _).trans h)
    rw [hsq, Real.exp_log hu0] at e
    have a := Real.pow_div_factorial_le_exp (c / 2 * s) (by positivity) 4
    have a' : s ^ 4 ≤ 24 / (c / 2) ^ 4 * Real.exp (c / 2 * s) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      have : ((Nat.factorial 4 : ℕ) : ℝ) = 24 := by norm_num [Nat.factorial]
      rw [this, mul_pow] at a
      linarith
    refine e.trans ?_
    calc K * s ^ 4 * (u * Real.exp (-c * s))
        ≤ K * (24 / (c / 2) ^ 4 * Real.exp (c / 2 * s)) * (u * Real.exp (-c * s)) := by gcongr
      _ = K * (24 / (c / 2) ^ 4) * (u * (Real.exp (c / 2 * s) * Real.exp (-c * s))) := by ring
      _ = K * (24 / (c / 2) ^ 4) * (u * Real.exp (-(c / 2) * s)) := by
          rw [← Real.exp_add]; congr 3; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) hF.le
  · refine (PsiFix.norm_psi0_le χ u (by linarith)).trans ?_
    have a1 : 1 ≤ Real.exp (c / 2 * S) * Real.exp (-(c / 2) * s) := by
      rw [← Real.exp_add]
      exact Real.one_le_exp (by nlinarith)
    have a2 : Real.log u + 1 ≤ S ^ 2 + 1 := by
      rw [← hsq]; nlinarith
    calc u * (Real.log u + 1) ≤ u * ((S ^ 2 + 1) * (Real.exp (c / 2 * S) * Real.exp (-(c / 2) * s))) :=
          mul_le_mul_of_nonneg_left (a2.trans (le_mul_of_one_le_right (by positivity) a1)) hu0.le
      _ = (S ^ 2 + 1) * Real.exp (c / 2 * S) * (u * Real.exp (-(c / 2) * s)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) hF.le

end GlobalTheory.Mem.An
