import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuation
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.PartialSum

set_option autoImplicit false

noncomputable section

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

theorem one_le_sizeE_of_nonneg {r : ℕ} (x : Fin r → ℝ) (hx : ∀ i, 0 ≤ x i) : 1 ≤ sizeE x := by
  unfold sizeE
  have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => hx i)
  linarith

theorem linF_comparable_sizeE {ι : Type} {r : ℕ} (a : ι → Fin r → ℝ) (b : ι → ℝ) (j : ι)
    (ha : ∀ i, 0 < a j i) (hb : 0 < b j) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ x : Fin r → ℝ, (∀ i, 0 ≤ x i) →
      c * sizeE x ≤ linF a b j x ∧ linF a b j x ≤ C * sizeE x := by
  let f : Option (Fin r) → ℝ := fun o => o.elim (b j) (a j)
  obtain ⟨p, hp⟩ := Finite.exists_min f
  obtain ⟨q, hq⟩ := Finite.exists_max f
  have hpos : ∀ o, 0 < f o := by
    intro o
    cases o with
    | none => exact hb
    | some i => exact ha i
  refine ⟨f p, f q, hpos p, hpos q, fun x hx => ?_⟩
  unfold linF sizeE
  constructor
  · rw [mul_add, mul_one, Finset.mul_sum]
    exact add_le_add (hp none)
      (Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hp (some i)) (hx i))
  · rw [mul_add, mul_one, Finset.mul_sum]
    exact add_le_add (hq none)
      (Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hq (some i)) (hx i))

theorem rpow_le_of_comparable (c C T : ℝ) (hc : 0 < c) (hC : 0 < C) (hT : 0 ≤ T) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ L E t D : ℝ, 1 ≤ E → c * E ≤ L → L ≤ C * E → |t| ≤ T → t ≤ D →
      L ^ t ≤ K * E ^ D := by
  refine ⟨Real.exp ((|Real.log c| + |Real.log C|) * T), (Real.exp_pos _).le, ?_⟩
  intro L E t D hE h1 h2 ht htD
  have hE0 : 0 < E := by linarith
  have hL : 0 < L := lt_of_lt_of_le (mul_pos hc hE0) h1
  have hu : 0 < L / E := div_pos hL hE0
  have hu1 : c ≤ L / E := (le_div_iff₀ hE0).2 h1
  have hu2 : L / E ≤ C := (div_le_iff₀ hE0).2 h2
  have hlog1 : Real.log c ≤ Real.log (L / E) := Real.log_le_log hc hu1
  have hlog2 : Real.log (L / E) ≤ Real.log C := Real.log_le_log hu hu2
  have habs : |Real.log (L / E)| ≤ |Real.log c| + |Real.log C| := by
    rw [abs_le]
    constructor
    · have := neg_abs_le (Real.log c)
      have := abs_nonneg (Real.log C)
      linarith
    · have := le_abs_self (Real.log C)
      have := abs_nonneg (Real.log c)
      linarith
  have hLE : L = (L / E) * E := by field_simp
  have hfirst : (L / E) ^ t ≤ Real.exp ((|Real.log c| + |Real.log C|) * T) := by
    rw [Real.rpow_def_of_pos hu]
    apply Real.exp_le_exp.2
    calc Real.log (L / E) * t ≤ |Real.log (L / E) * t| := le_abs_self _
      _ = |Real.log (L / E)| * |t| := abs_mul _ _
      _ ≤ (|Real.log c| + |Real.log C|) * T :=
        mul_le_mul habs ht (abs_nonneg _) (by positivity)
  have hsecond : E ^ t ≤ E ^ D := Real.rpow_le_rpow_of_exponent_le hE htD
  calc L ^ t = (L / E) ^ t * E ^ t := by
        rw [← Real.mul_rpow hu.le hE0.le, ← hLE]
    _ ≤ Real.exp ((|Real.log c| + |Real.log C|) * T) * E ^ D :=
        mul_le_mul hfirst hsecond (Real.rpow_nonneg hE0.le _) (Real.exp_pos _).le

theorem prod_zpow_eq_zpow_sum {ι : Type} (E : ℝ) (hE : E ≠ 0) (S : Finset ι) (f : ι → ℤ) :
    ∏ j ∈ S, E ^ f j = E ^ ∑ j ∈ S, f j := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert j S hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj, ih, zpow_add₀ hE]

theorem norm_factor_le {ι : Type} (r : ℕ) (a : ι → Fin r → ℝ) (b : ι → ℝ) (j : ι)
    (ha : ∀ i, 0 < a j i) (hb : 0 < b j) (B R β : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ s : ℂ, ‖s‖ ≤ R → -(B : ℝ) ≤ s.re → ∀ x : Fin r → ℝ, (∀ i, 0 ≤ x i) →
      ‖((linF a b j x : ℝ) : ℂ) ^ (-s - (β : ℂ))‖ ≤ K * sizeE x ^ ((B : ℤ) - (β : ℤ)) := by
  obtain ⟨c, C, hc, hC, hcmp⟩ := linF_comparable_sizeE a b j ha hb
  obtain ⟨K, hK0, hK⟩ := rpow_le_of_comparable c C ((R : ℝ) + β) hc hC (by positivity)
  refine ⟨K, hK0, fun s hs hs' x hx => ?_⟩
  have hE := one_le_sizeE_of_nonneg x hx
  have hE0 : 0 < sizeE x := by linarith
  obtain ⟨h1, h2⟩ := hcmp x hx
  have hL : 0 < linF a b j x := lt_of_lt_of_le (mul_pos hc hE0) h1
  have hre : (-s - (β : ℂ)).re = -s.re - β := by simp
  have hsr : |s.re| ≤ R := (Complex.abs_re_le_norm s).trans hs
  have hβ : (0 : ℝ) ≤ β := by positivity
  have ht : |-s.re - (β : ℝ)| ≤ (R : ℝ) + β := by
    rw [abs_le] at hsr ⊢
    constructor <;> linarith [hsr.1, hsr.2]
  have htD : -s.re - (β : ℝ) ≤ (((B : ℤ) - (β : ℤ) : ℤ) : ℝ) := by
    push_cast
    linarith
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hL, hre, ← Real.rpow_intCast]
  exact hK _ _ _ _ hE h1 h2 ht htD

theorem baseBound : ∀ (ι : Type) [Fintype ι] (r : ℕ) (a : ι → Fin r → ℝ) (b : ι → ℝ), (∀ j i, 0 < a j i) → (∀ j, 0 < b j) → ∀ (B R : ℕ) (β : ι → ℕ), ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, ‖s‖ ≤ R → -(B : ℝ) ≤ s.re →
  ∀ x : Fin r → ℝ, (∀ i, 0 ≤ x i) →
    ‖Fr a b s β x‖ ≤ C * sizeE x ^ ((Fintype.card ι : ℤ) * (B : ℤ) - ∑ j, (β j : ℤ)) := by
  intro ι _ r a b ha hb B R β
  have hj := fun j => norm_factor_le r a b j (ha j) (hb j) B R (β j)
  choose K hK0 hK using hj
  refine ⟨∏ j, K j, Finset.prod_nonneg fun j _ => hK0 j, fun s hs hs' x hx => ?_⟩
  have hE0 : sizeE x ≠ 0 := by
    have := one_le_sizeE_of_nonneg x hx
    intro h
    linarith
  unfold Fr
  rw [norm_prod]
  calc ∏ j, ‖((linF a b j x : ℝ) : ℂ) ^ (-s - (β j : ℂ))‖
      ≤ ∏ j, (K j * sizeE x ^ ((B : ℤ) - (β j : ℤ))) :=
        Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun j _ => hK j s hs hs' x hx)
    _ = (∏ j, K j) * sizeE x ^ ((Fintype.card ι : ℤ) * (B : ℤ) - ∑ j, (β j : ℤ)) := by
        rw [Finset.prod_mul_distrib, prod_zpow_eq_zpow_sum _ hE0, Finset.sum_sub_distrib]
        simp

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
