import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ZerosDisc
import Development.AbelianVarietyTheory.Definitions.Foundations.RayPrimes
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DirichletLZerosInWindowFiniteAndPosOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DirichletLZeroSymmetry
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SumIndicatorLeZsumR
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LogDerivSeriesOfExplicit
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ZeroCountHolds
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExplicitFormulaClosedStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DirichletLZerosEqPrimitiveCharacterZerosStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsDirichletLFunctionZeroGapNearOneStatement

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical

namespace GlobalTheory.ExplicitFormulaRight

open GlobalTheory.Mem.An

theorem zfin {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (t T : ℝ) :
    (zerosIn χ t T).Finite := (ZeroWindow.finite_and_one_le_zmult q χ t T).1

theorem zsumR_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (t T : ℝ) (f : ℂ → ℝ) :
    zsumR χ t T f = ∑ ρ ∈ (zfin χ t T).toFinset, (zmult χ ρ : ℝ) * f ρ :=
  finsum_mem_eq_finite_toFinset_sum _ _

theorem recip_bound : ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
    χ.IsPrimitive → ∀ T : ℝ, 2 ≤ T →
      zsumR χ 0 1 (fun ρ => 1 / ‖ρ‖) ≤ C * ((q : ℝ) ^ 2 * Real.log (3 * q) ^ 2) ∧
      zsumR χ 0 T (fun ρ => 1 / ‖ρ‖) ≤
        C * ((q : ℝ) ^ 2 * Real.log (3 * q) ^ 2) + C * Real.log (q * T) ^ 2 := by
  obtain ⟨C₁, H₁⟩ := zsumR_recip_le zeroCount_holds
  obtain ⟨c, hc, H₂⟩ := GlobalTheory.T.exists_dirichletLFunction_zero_gap_near_one
  refine ⟨|C₁| / c + |C₁| + 1, by positivity, fun q _ χ hχ T hT => ?_⟩
  obtain ⟨h1, h2⟩ := H₁ q χ hχ T hT
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hl : 0 < Real.log (3 * q) := Real.log_pos (by linarith)
  have hK : 0 < (q : ℝ) ^ 2 * Real.log (3 * q) := by positivity
  have hA : zsumR χ 0 1 (fun ρ => 1 / ‖ρ‖) ≤
      (|C₁| / c + |C₁| + 1) * ((q : ℝ) ^ 2 * Real.log (3 * q) ^ 2) := by
    have a1 : zsumR χ 0 1 (fun ρ => 1 / ‖ρ‖) ≤
        ((q : ℝ) ^ 2 * Real.log (3 * q) / c) * zsumR χ 0 1 (fun _ => 1) := by
      rw [zsumR_eq, zsumR_eq, Finset.mul_sum]
      refine Finset.sum_le_sum fun ρ hρ => ?_
      obtain ⟨r0, r1, ri, rz⟩ := (zfin χ 0 1).mem_toFinset.mp hρ
      have hz := ((zeros_symm_one_sub q χ hχ ρ r0 r1).1).mp rz
      have hne : (1 - ρ) ≠ 1 := by
        intro h
        have := congrArg Complex.re h
        simp at this
        linarith
      have hb := H₂ q χ⁻¹ (1 - ρ) (Or.inr hne) hz (by simpa using ri)
      have hre : c / ((q : ℝ) ^ 2 * Real.log (3 * q)) ≤ ‖ρ‖ := by
        have := Complex.re_le_norm ρ
        simp only [Complex.sub_re, Complex.one_re] at hb
        linarith
      have : 1 / ‖ρ‖ ≤ (q : ℝ) ^ 2 * Real.log (3 * q) / c := by
        have := one_div_le_one_div_of_le (div_pos hc hK) hre
        rwa [one_div_div] at this
      calc (zmult χ ρ : ℝ) * (1 / ‖ρ‖) ≤ (zmult χ ρ : ℝ) * ((q : ℝ) ^ 2 * Real.log (3 * q) / c) :=
            mul_le_mul_of_nonneg_left this (by positivity)
        _ = _ := by ring
    have a2 : zsumR χ 0 1 (fun _ => 1) ≤ |C₁| * Real.log (3 * q) :=
      h2.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hl.le)
    calc _ ≤ ((q : ℝ) ^ 2 * Real.log (3 * q) / c) * (|C₁| * Real.log (3 * q)) :=
          a1.trans (mul_le_mul_of_nonneg_left a2 (by positivity))
      _ = (|C₁| / c) * ((q : ℝ) ^ 2 * Real.log (3 * q) ^ 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith [abs_nonneg C₁]) (by positivity)
  refine ⟨hA, ?_⟩
  have hB : zsumR χ 0 T (fun ρ => 1 / ‖ρ‖) ≤ zsumR χ 0 1 (fun ρ => 1 / ‖ρ‖) +
      zsumR χ 0 T (fun ρ => if 1 < |ρ.im| then 1 / ‖ρ‖ else 0) := by
    rw [zsumR_eq, zsumR_eq, zsumR_eq]
    have e : (zfin χ 0 1).toFinset = (zfin χ 0 T).toFinset.filter (fun ρ => ¬ 1 < |ρ.im|) := by
      ext ρ
      simp only [Set.Finite.mem_toFinset, Finset.mem_filter, zerosIn, Set.mem_setOf_eq, sub_zero,
        not_lt]
      constructor
      · rintro ⟨a, b, c, d⟩
        exact ⟨⟨a, b, by linarith, d⟩, c⟩
      · rintro ⟨⟨a, b, _, d⟩, c⟩
        exact ⟨a, b, c, d⟩
    rw [e, Finset.sum_filter, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun ρ _ => ?_
    by_cases h : 1 < |ρ.im| <;> simp [h]
  have hC : C₁ * Real.log (q * T) ^ 2 ≤ (|C₁| / c + |C₁| + 1) * Real.log (q * T) ^ 2 := by
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    have : 0 ≤ |C₁| / c := by positivity
    linarith [le_abs_self C₁]
  linarith

theorem box_subset {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (T : ℝ) :
    zerosBox χ (1 / 2) T ⊆ zerosIn χ 0 T := by
  rintro ρ ⟨a, b, c, d⟩
  exact ⟨by linarith, b, by simpa using c, d⟩

theorem left_zeros {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (u T : ℝ) (hu : 1 ≤ u) :
    ‖zsum χ 0 T (fun ρ => (u : ℂ) ^ ρ / ρ) -
      ∑ᶠ ρ ∈ zerosBox χ (1 / 2) T, (ord χ ρ : ℂ) * ((u : ℂ) ^ ρ / ρ)‖ ≤
      Real.sqrt u * zsumR χ 0 T (fun ρ => 1 / ‖ρ‖) := by
  have hf := (zfin χ 0 T).subset (box_subset χ T)
  have e : hf.toFinset = (zfin χ 0 T).toFinset.filter (fun ρ => 1 / 2 ≤ ρ.re) := by
    ext ρ
    simp only [Set.Finite.mem_toFinset, Finset.mem_filter]
    constructor
    · intro h
      exact ⟨box_subset χ T h, h.1⟩
    · rintro ⟨⟨_, b, c, d⟩, a⟩
      exact ⟨a, b, by simpa using c, d⟩
  rw [zsumR_eq, zsum, finsum_mem_eq_finite_toFinset_sum _ (zfin χ 0 T),
    finsum_mem_eq_finite_toFinset_sum _ hf, e, Finset.sum_filter, ← Finset.sum_sub_distrib,
    Finset.mul_sum]
  refine norm_sum_le_of_le _ fun ρ _ => ?_
  have hu0 : 0 < u := by linarith
  by_cases h : 1 / 2 ≤ ρ.re
  · rw [if_pos h]
    have : (ord χ ρ : ℂ) = zmult χ ρ := rfl
    rw [this, sub_self, norm_zero]
    positivity
  · rw [if_neg h, sub_zero, norm_mul, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hu0,
      Complex.norm_natCast, Real.sqrt_eq_rpow]
    have h1 : u ^ ρ.re ≤ u ^ (1 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hu (not_le.mp h).le
    calc (zmult χ ρ : ℝ) * (u ^ ρ.re / ‖ρ‖) = u ^ ρ.re * ((zmult χ ρ : ℝ) * (1 / ‖ρ‖)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right h1 (by positivity)

theorem logs {N q u T : ℝ} (hN : 1 ≤ N) (hq : N ≤ q) (hT : 2 ≤ T) (hu : T ≤ u) {L : ℝ}
    (hL : L = Real.log (q * u * T)) :
    1 ≤ L ∧ Real.log (N * u * T) ^ 2 ≤ L ^ 2 ∧ Real.log (N * u) ≤ L ^ 2 ∧
      Real.log (3 * N) ^ 2 ≤ L ^ 2 ∧ Real.log (N * T) ^ 2 ≤ L ^ 2 ∧
      (Nat.log 2 ⌊u⌋₊ : ℝ) * Real.log q ≤ 2 * L ^ 2 := by
  have hq1 : 1 ≤ q := hN.trans hq
  have hu2 : 2 ≤ u := hT.trans hu
  have huT : 4 ≤ u * T := by nlinarith
  have hlog : ∀ x : ℝ, 0 < x → x ≤ q * u * T → Real.log x ≤ L := fun x hx h =>
    hL ▸ Real.log_le_log hx h
  have key : ∀ a b : ℝ, 0 ≤ a → a ≤ q → 0 ≤ b → b ≤ u * T → a * b ≤ q * u * T := by
    intro a b ha haq hb hbu
    rw [mul_assoc]
    exact mul_le_mul haq hbu hb (by linarith)
  have h2 := Real.log_two_gt_d9
  have hL1 : 1 ≤ L := by
    have := hlog 4 (by norm_num) (by simpa using key 1 4 (by norm_num) hq1 (by norm_num) huT)
    have h2' : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    linarith
  have sq_le : ∀ x : ℝ, 1 ≤ x → x ≤ q * u * T → Real.log x ^ 2 ≤ L ^ 2 := fun x hx hc =>
    pow_le_pow_left₀ (Real.log_nonneg hx) (hlog x (by linarith) hc) 2
  have huu : u ≤ u * T := by nlinarith
  have hTT : T ≤ u * T := by nlinarith
  refine ⟨hL1, sq_le _ ?_ ?_, ?_, sq_le _ (by linarith) ?_, sq_le _ (by nlinarith) ?_, ?_⟩
  · rw [mul_assoc]; nlinarith
  · rw [mul_assoc]; exact key _ _ (by linarith) hq (by linarith) le_rfl
  · have := hlog (N * u) (by positivity) (key _ _ (by linarith) hq (by linarith) huu)
    nlinarith
  · rw [mul_comm]; exact key _ _ (by linarith) hq (by linarith) (by linarith)
  · exact key _ _ (by linarith) hq (by linarith) hTT
  · have a1 : Real.log q ≤ L :=
      hlog q (by linarith) (by simpa using key q 1 (by linarith) le_rfl (by norm_num) (by linarith))
    have a2 : Real.log u ≤ L :=
      hlog u (by linarith) (by simpa using key 1 u (by linarith) hq1 (by linarith) huu)
    have hfl : ⌊u⌋₊ ≠ 0 := by
      have : 1 ≤ ⌊u⌋₊ := Nat.le_floor (by push_cast; linarith)
      omega
    have a3 : (Nat.log 2 ⌊u⌋₊ : ℝ) * Real.log 2 ≤ Real.log u := by
      rw [← Real.log_pow]
      refine Real.log_le_log (by positivity) (le_trans ?_ (Nat.floor_le (by linarith)))
      exact_mod_cast Nat.pow_log_le_self 2 hfl
    have a4 : (Nat.log 2 ⌊u⌋₊ : ℝ) ≤ 2 * L := by
      have : (0 : ℝ) ≤ Nat.log 2 ⌊u⌋₊ := by positivity
      nlinarith
    calc _ ≤ (2 * L) * L := mul_le_mul a4 a1 (Real.log_nonneg hq1) (by linarith)
      _ = _ := by ring

theorem combine {A B S s x K E P D Z₁ Z t₁ t₂ l₃ l₄ N q : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hs : 1 ≤ s) (hx : 0 ≤ x) (hK : 0 ≤ K) (hN : 1 ≤ N) (hq : N ≤ q)
    (hS : S ≤ P + E + D) (hP : P ≤ 2 * K) (hE : E ≤ A * (t₁ + t₂ + Z₁)) (hD : D ≤ s * Z)
    (h1 : t₁ ≤ x * K) (h2 : t₂ ≤ K) (hl₃ : l₃ ≤ K) (hl₄ : l₄ ≤ K)
    (hZ₁ : Z₁ ≤ B * (N ^ 2 * l₃)) (hZ : Z ≤ B * (N ^ 2 * l₃) + B * l₄) :
    S ≤ (2 + A * (2 + B) + 2 * B) * (x + s * q ^ 3) * K := by
  have hq1 : 1 ≤ q := hN.trans hq
  have hq3 : 1 ≤ q ^ 3 := one_le_pow₀ hq1
  have hN2 : N ^ 2 ≤ q ^ 3 :=
    (pow_le_pow_left₀ (by linarith) hq 2).trans (pow_le_pow_right₀ hq1 (by norm_num))
  obtain ⟨M, hM⟩ : ∃ M, M = (x + s * q ^ 3) * K := ⟨_, rfl⟩
  have m0 : 0 ≤ x * K := by positivity
  have k1 : K ≤ q ^ 3 * K := le_mul_of_one_le_left hK hq3
  have k2 : q ^ 3 * K ≤ s * (q ^ 3 * K) := le_mul_of_one_le_left (by positivity) hs
  have m1 : s * (q ^ 3 * K) ≤ M := by rw [hM]; linarith
  have m2 : x * K ≤ M := by rw [hM]; linarith
  have n1 : N ^ 2 * l₃ ≤ q ^ 3 * K :=
    (mul_le_mul_of_nonneg_left hl₃ (by positivity)).trans (mul_le_mul_of_nonneg_right hN2 hK)
  have z1 : Z₁ ≤ B * M := hZ₁.trans (mul_le_mul_of_nonneg_left (by linarith) hB)
  have z2 : Z ≤ 2 * B * (q ^ 3 * K) := by
    have b1 := mul_le_mul_of_nonneg_left n1 hB
    have b2 := mul_le_mul_of_nonneg_left (hl₄.trans k1) hB
    linarith
  have z3 : D ≤ 2 * B * M := by
    calc D ≤ s * (2 * B * (q ^ 3 * K)) := hD.trans (mul_le_mul_of_nonneg_left z2 (by linarith))
      _ = 2 * B * (s * (q ^ 3 * K)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left m1 (by positivity)
  have z4 : E ≤ A * (M + M + B * M) := hE.trans (mul_le_mul_of_nonneg_left (by linarith) hA)
  rw [mul_assoc, ← hM]
  linarith

theorem explicit_formula_right : ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (u T : ℝ), 2 ≤ T → T ≤ u → (zerosBox χ (1 / 2) T).Finite ∧ ‖(∑ n ∈ Finset.Icc 1 ⌊u⌋₊, ((Λ n : ℝ) : ℂ) * χ (n : ZMod q)) - (if χ = 1 then (u : ℂ) else 0) + ∑ᶠ ρ ∈ zerosBox χ (1 / 2) T, (ord χ ρ : ℂ) * ((u : ℂ) ^ ρ / ρ)‖ ≤ C * (u / T + Real.sqrt u * (q : ℝ) ^ 3) * Real.log (q * u * T) ^ 2 := by
  obtain ⟨A, HA⟩ := GlobalTheory.T.norm_psi0_add_zsum_le
  obtain ⟨B, hB, HB⟩ := recip_bound
  refine ⟨2 + |A| * (2 + B) + 2 * B, by positivity, fun q _ χ u T hT hu => ?_⟩
  refine ⟨(zfin χ 0 T).subset (box_subset χ T), ?_⟩
  haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hprim := χ.primitiveCharacter_isPrimitive
  have hN : (1 : ℝ) ≤ χ.conductor := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr χ.conductor_ne_zero
  have hq : (χ.conductor : ℝ) ≤ q := by
    exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) χ.conductor_dvd_level
  have hone : χ.primitiveCharacter = 1 ↔ χ = 1 := by
    constructor
    · intro h
      rw [← χ.changeLevel_primitiveCharacter, h, map_one]
    · rintro rfl
      exact primitiveCharacter_one
  have hcmp : ∀ ρ : ℂ, 1 / 2 ≤ ρ.re → ρ.re < 1 →
      (LFunction χ ρ = 0 ↔ LFunction χ.primitiveCharacter ρ = 0) ∧
        ord χ ρ = ord χ.primitiveCharacter ρ := fun ρ a b =>
    GlobalTheory.T.dirichletL_zeros_eq_primitiveCharacter_zeros q χ ρ (by linarith) (Or.inr (by rintro rfl; simp at b))
  have hbox : zerosBox χ (1 / 2) T = zerosBox χ.primitiveCharacter (1 / 2) T := by
    ext ρ
    constructor
    · rintro ⟨a, b, c, d⟩
      exact ⟨a, b, c, (hcmp ρ a b).1.mp d⟩
    · rintro ⟨a, b, c, d⟩
      exact ⟨a, b, c, (hcmp ρ a b).1.mpr d⟩
  have hsum : ∑ᶠ ρ ∈ zerosBox χ (1 / 2) T, (ord χ ρ : ℂ) * ((u : ℂ) ^ ρ / ρ) =
      ∑ᶠ ρ ∈ zerosBox χ.primitiveCharacter (1 / 2) T,
        (ord χ.primitiveCharacter ρ : ℂ) * ((u : ℂ) ^ ρ / ρ) :=
    finsum_mem_congr hbox fun ρ hρ => by rw [(hcmp ρ hρ.1 hρ.2.1).2]
  have hE := HA χ.conductor χ.primitiveCharacter hprim u T hT hu
  obtain ⟨hZ₁, hZ⟩ := HB χ.conductor χ.primitiveCharacter hprim T hT
  have hD := left_zeros χ.primitiveCharacter u T (by linarith)
  have hP := GlobalTheory.MangoldtSeries.norm_sub_primitive_le χ ⌊u⌋₊
  obtain ⟨l0, l1, l2, l3, l4, l5⟩ := logs hN hq hT hu rfl
  have hpsi : Formalism.MainNotions.GlobalTheoryTheory.psi0 χ.primitiveCharacter u =
      (∑ n ∈ Finset.Icc 1 ⌊u⌋₊, ((Λ n : ℝ) : ℂ) * χ.primitiveCharacter (n : ZMod χ.conductor)) -
        (if χ = 1 then (u : ℂ) else 0) := by
    unfold Formalism.MainNotions.GlobalTheoryTheory.psi0
    congr 1
    by_cases h : χ = 1
    · rw [if_pos h, if_pos (hone.mpr h)]
    · rw [if_neg h, if_neg (mt hone.mp h)]
  have hu0 : 0 < u := by linarith
  have hT0 : 0 < T := by linarith
  have hZ0 : 0 ≤ zsumR χ.primitiveCharacter 0 1 (fun ρ => 1 / ‖ρ‖) := by
    rw [zsumR_eq]
    exact Finset.sum_nonneg fun ρ _ => by positivity
  have hl0 : 0 ≤ Real.log (χ.conductor * u) := Real.log_nonneg (by nlinarith)
  have hE' := hE.trans (mul_le_mul_of_nonneg_right (le_abs_self A) (by positivity))
  refine combine (abs_nonneg A) hB.le (Real.one_le_sqrt.mpr (by linarith)) (by positivity)
    (by positivity) hN hq ?_ (hP.trans l5) hE' hD ?_ l2 l3 l4 hZ₁ hZ
  · rw [hsum, hpsi]
    refine le_trans (le_of_eq ?_) ((norm_sub_le _ _).trans (add_le_add_left (norm_add_le _ _) _))
    congr 1
    ring
  · rw [mul_div_right_comm]
    exact mul_le_mul_of_nonneg_left l1 (by positivity)

end GlobalTheory.ExplicitFormulaRight
