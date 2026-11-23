import Mathlib
import GroundTheory.LocalFields.LocalZetaChar

noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel MeasureTheory Measure Topology Filter
open scoped WithZero NNReal ENNReal Pointwise

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

section Laurent

variable (K) in

def qpowUnit (s : ℂ) : ℂˣ := Units.mk0 ((residueCard K : ℂ) ^ (-s)) (qpow_ne_zero s)

variable (K) in

def evalQpow (P : LaurentPolynomial ℂ) (s : ℂ) : ℂ :=
  LaurentPolynomial.eval₂ (RingHom.id ℂ) (qpowUnit K s) P

theorem evalQpow_C_mul_T (a : ℂ) (n : ℤ) (s : ℂ) :
    evalQpow K (LaurentPolynomial.C a * LaurentPolynomial.T n) s =
      a * ((residueCard K : ℂ) ^ (-s)) ^ n := by
  rw [evalQpow, LaurentPolynomial.eval₂_C_mul_T, Units.val_zpow_eq_zpow_val]
  rfl

theorem evalQpow_add (P Q : LaurentPolynomial ℂ) (s : ℂ) :
    evalQpow K (P + Q) s = evalQpow K P s + evalQpow K Q s := map_add _ _ _

theorem evalQpow_mul (P Q : LaurentPolynomial ℂ) (s : ℂ) :
    evalQpow K (P * Q) s = evalQpow K P s * evalQpow K Q s := map_mul _ _ _

theorem evalQpow_sub (P Q : LaurentPolynomial ℂ) (s : ℂ) :
    evalQpow K (P - Q) s = evalQpow K P s - evalQpow K Q s := map_sub _ _ _

theorem evalQpow_one (s : ℂ) : evalQpow K 1 s = 1 := map_one _

theorem evalQpow_C (a : ℂ) (s : ℂ) : evalQpow K (LaurentPolynomial.C a) s = a := by
  rw [evalQpow, LaurentPolynomial.eval₂_C]
  rfl

theorem evalQpow_sum {ι : Type*} (t : Finset ι) (P : ι → LaurentPolynomial ℂ) (s : ℂ) :
    evalQpow K (∑ i ∈ t, P i) s = ∑ i ∈ t, evalQpow K (P i) s := map_sum _ _ _

theorem differentiable_qpow : Differentiable ℂ fun s : ℂ => (residueCard K : ℂ) ^ (-s) :=
  differentiable_neg.const_cpow (Or.inl residueCard_ne_zero_complex)

theorem differentiable_evalQpow (P : LaurentPolynomial ℂ) : Differentiable ℂ (evalQpow K P) := by
  induction P using LaurentPolynomial.induction_on' with
  | add p q hp hq =>
    have : evalQpow K (p + q) = fun s => evalQpow K p s + evalQpow K q s :=
      funext fun s => evalQpow_add p q s
    rw [this]
    exact hp.add hq
  | C_mul_T n a =>
    have : evalQpow K (LaurentPolynomial.C a * LaurentPolynomial.T n) =
        fun s => a * ((residueCard K : ℂ) ^ (-s)) ^ n :=
      funext fun s => evalQpow_C_mul_T a n s
    rw [this]
    exact (differentiable_qpow.zpow (Or.inl fun s => qpow_ne_zero s)).const_mul a

end Laurent

section Sums

omit [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in

theorem hasSum_int_of_shift {E : Type*} [AddCommMonoid E] [TopologicalSpace E] {a : ℤ → E}
    (M : ℤ) (h : ∀ k, k < M → a k = 0) {x : E} (hx : HasSum (fun n : ℕ => a (M + n)) x) :
    HasSum a x := by
  have hinj : Function.Injective (fun n : ℕ => M + (n : ℤ)) := fun m n hmn => by
    simpa using hmn
  refine (hinj.hasSum_iff fun k hk => h k ?_).mp hx
  by_contra hle
  push Not at hle
  exact hk ⟨(k - M).toNat, by simp only; omega⟩

end Sums

section LFactor

variable (χ : Kˣ →* ℂˣ)

open Classical in

def localLFactor (s : ℂ) : ℂ :=
  if IsUnramifiedChar χ then (1 - ((χ (unifUnit K) : ℂˣ) : ℂ) * (residueCard K : ℂ) ^ (-s))⁻¹
  else 1

variable {χ}

theorem localLFactor_of_isUnramified (h : IsUnramifiedChar χ) (s : ℂ) :
    localLFactor χ s = (1 - ((χ (unifUnit K) : ℂˣ) : ℂ) * (residueCard K : ℂ) ^ (-s))⁻¹ := by
  simp [localLFactor, h]

theorem localLFactor_of_not_isUnramified (h : ¬ IsUnramifiedChar χ) (s : ℂ) :
    localLFactor χ s = 1 := by
  simp [localLFactor, h]

variable (hχ : Continuous χ)
include hχ

theorem norm_quasiChar_unifUnit :
    ‖((χ (unifUnit K) : ℂˣ) : ℂ)‖ = (residueCard K : ℝ) ^ (-quasiCharExponent χ) := by
  rw [norm_quasiChar_apply hχ, modulus_of_ne_zero (unifUnit K).ne_zero, ord_unifUnit,
    NNReal.coe_zpow, NNReal.coe_natCast, ← Real.rpow_intCast,
    ← Real.rpow_mul residueCard_pos_real.le]
  congr 1
  push_cast
  ring

theorem norm_quasiChar_unifUnit_mul_qpow_lt_one {s : ℂ} (hs : -quasiCharExponent χ < s.re) :
    ‖((χ (unifUnit K) : ℂˣ) : ℂ) * (residueCard K : ℂ) ^ (-s)‖ < 1 := by
  rw [norm_mul, norm_quasiChar_unifUnit hχ, norm_qpow, ← Real.rpow_add residueCard_pos_real]
  exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast one_lt_residueCard) (by linarith)

theorem one_sub_quasiChar_unifUnit_mul_qpow_ne_zero {s : ℂ}
    (hs : -quasiCharExponent χ < s.re) :
    1 - ((χ (unifUnit K) : ℂˣ) : ℂ) * (residueCard K : ℂ) ^ (-s) ≠ 0 := by
  intro h
  have := norm_quasiChar_unifUnit_mul_qpow_lt_one hχ hs
  rw [← sub_eq_zero.mp h, norm_one] at this
  exact lt_irrefl _ this

theorem localLFactor_ne_zero {s : ℂ} (hs : -quasiCharExponent χ < s.re) :
    localLFactor χ s ≠ 0 := by
  by_cases h : IsUnramifiedChar χ
  · rw [localLFactor_of_isUnramified h]
    exact inv_ne_zero (one_sub_quasiChar_unifUnit_mul_qpow_ne_zero hχ hs)
  · rw [localLFactor_of_not_isUnramified h]
    exact one_ne_zero

theorem norm_quasiChar_mul_modulus_cpow (u : Kˣ) (s : ℂ) :
    ‖((χ u : ℂˣ) : ℂ) * ((modulus (u : K) : ℝ) : ℂ) ^ s‖ =
      ‖((χ (unifUnit K) : ℂˣ) : ℂ) * (residueCard K : ℂ) ^ (-s)‖ ^ ord (u : K) := by
  have hχu : ‖((χ u : ℂˣ) : ℂ)‖ = ‖((χ (unifUnit K) : ℂˣ) : ℂ)‖ ^ ord (u : K) := by
    have e := congrArg (fun v => ‖((χ v : ℂˣ) : ℂ)‖) (eq_unifUnit_zpow_mul u)
    rw [e, map_mul, Units.val_mul, norm_mul,
      norm_quasiChar_apply_eq_one hχ (unifUnit_zpow_neg_mul_mem u), mul_one, map_zpow,
      Units.val_zpow_eq_zpow_val, norm_zpow]
  rw [norm_mul, hχu, modulus_cpow_eq_zpow, norm_zpow, ← mul_zpow, ← norm_mul]

end LFactor

section ZetaNonvanishing₂

variable [MeasurableSpace K] [BorelSpace K]

def localZeta (f : K → ℂ) (χ : Kˣ →* ℂˣ) (s : ℂ) : ℂ :=
  ∫ u, f u * ((χ u : ℂˣ) : ℂ) * ((modulus (u : K) : ℝ) : ℂ) ^ s ∂multHaar K

variable {f : K → ℂ} {χ : Kˣ →* ℂˣ}

omit [MeasurableSpace K] [BorelSpace K] in
theorem continuous_localZeta_integrand (hf : f ∈ schwartzBruhat K) (hχ : Continuous χ) (s : ℂ) :
    Continuous fun u : Kˣ => f u * ((χ u : ℂˣ) : ℂ) * ((modulus (u : K) : ℝ) : ℂ) ^ s := by
  refine ((hf.1.continuous.comp Units.continuous_val).mul (Units.continuous_val.comp hχ)).mul ?_
  refine (Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp
    (continuous_modulus.comp Units.continuous_val))).cpow continuous_const fun u => ?_
  exact Complex.ofReal_mem_slitPlane.mpr (by exact_mod_cast modulus_pos u.ne_zero)

theorem integrable_localZeta (hf : f ∈ schwartzBruhat K) (hχ : Continuous χ) {s : ℂ}
    (hs : -quasiCharExponent χ < s.re) :
    Integrable (fun u : Kˣ => f u * ((χ u : ℂˣ) : ℂ) * ((modulus (u : K) : ℝ) : ℂ) ^ s)
      (multHaar K) := by
  obtain ⟨-, M, -, hM⟩ := exists_invariant_of_mem_schwartzBruhat hf
  obtain ⟨C, hC⟩ := hf.1.continuous.bounded_above_of_compact_support hf.2
  set ρ := ‖((χ (unifUnit K) : ℂˣ) : ℂ) * (residueCard K : ℂ) ^ (-s)‖ with hρ
  have hρ1 : ρ < 1 := norm_quasiChar_unifUnit_mul_qpow_lt_one hχ hs
  have hρ0 : 0 < ρ := norm_pos_iff.mpr (mul_ne_zero (χ _).ne_zero (qpow_ne_zero s))
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  refine ⟨(continuous_localZeta_integrand hf hχ s).aestronglyMeasurable, ?_⟩
  let a : ℤ → ℝ := fun k => if M ≤ k then C * ρ ^ k else 0
  have ha0 : ∀ k, 0 ≤ a k := fun k => by
    simp only [a]
    split_ifs
    · exact mul_nonneg hC0 (zpow_nonneg hρ0.le _)
    · exact le_rfl
  have hsum : HasSum a (C * ρ ^ M * (1 - ρ)⁻¹) := by
    refine hasSum_int_of_shift M (fun k hk => by simp [a, not_le.mpr hk]) ?_
    have e : (fun n : ℕ => a (M + n)) = fun n : ℕ => C * ρ ^ M * ρ ^ n := by
      funext n
      simp only [a, le_add_iff_nonneg_right, Nat.cast_nonneg, if_true]
      rw [zpow_add₀ hρ0.ne', zpow_natCast, mul_assoc]
    rw [e]
    exact (hasSum_geometric_of_lt_one hρ0.le hρ1).mul_left _
  have hbound : ∀ u : Kˣ,
      ‖f u * ((χ u : ℂˣ) : ℂ) * ((modulus (u : K) : ℝ) : ℂ) ^ s‖ₑ ≤
        ENNReal.ofReal (a (ord (u : K))) := by
    intro u
    rw [← ofReal_norm]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [mul_assoc, norm_mul, norm_quasiChar_mul_modulus_cpow hχ]
    simp only [a]
    split_ifs with hk
    · exact mul_le_mul_of_nonneg_right (hC _) (zpow_nonneg hρ0.le _)
    · have : f u = 0 := by
        by_contra h0
        exact hk ((mem_valBall_iff_le_ord u.ne_zero).mp (hM _ h0))
      rw [this, norm_zero, zero_mul]
  refine (lintegral_multHaar_le_tsum _ (fun k => ENNReal.ofReal (a k)) hbound).trans_lt ?_
  rw [← ENNReal.ofReal_tsum_of_nonneg ha0 hsum.summable]
  exact ENNReal.ofReal_lt_top

open scoped Classical in

theorem localZeta_eq_sum (hf : f ∈ schwartzBruhat K) (hχ : Continuous χ) {M N : ℤ} (hMN : M ≤ N)
    (hM : ∀ x, f x ≠ 0 → x ∈ valBall K M) (hN : ∀ x ∈ valBall K N, f x = f 0) {s : ℂ}
    (hs : -quasiCharExponent χ < s.re) :
    localZeta f χ s =
      ∑ k ∈ Finset.Ico M N, (∫ u in ordShell K k, f u * ((χ u : ℂˣ) : ℂ) ∂multHaar K) *
          ((residueCard K : ℂ) ^ (-s)) ^ k +
        if IsUnramifiedChar χ then
          f 0 * (((χ (unifUnit K) : ℂˣ) : ℂ) * (residueCard K : ℂ) ^ (-s)) ^ N *
            (1 - ((χ (unifUnit K) : ℂˣ) : ℂ) * (residueCard K : ℂ) ^ (-s))⁻¹
        else 0 := by
  set T := (residueCard K : ℂ) ^ (-s) with hT
  set α := ((χ (unifUnit K) : ℂˣ) : ℂ) with hα
  let Z : ℤ → ℂ := fun k => ∫ u in ordShell K k, f u * ((χ u : ℂˣ) : ℂ) ∂multHaar K
  have hsum := hasSum_setIntegral_ordShell (integrable_localZeta hf hχ hs)
  have hterm : ∀ k, ∫ u in ordShell K k, f u * ((χ u : ℂˣ) : ℂ) *
      ((modulus (u : K) : ℝ) : ℂ) ^ s ∂multHaar K = Z k * T ^ k := by
    intro k
    simp only [Z]
    rw [← integral_mul_const]
    refine setIntegral_congr_fun (measurableSet_ordShell k) fun u hu => ?_
    rw [modulus_cpow_eq_zpow, mem_ordShell.mp hu]
  simp only [hterm] at hsum
  have hlow : ∀ k, k < M → Z k = 0 := by
    intro k hk
    refine setIntegral_eq_zero_of_forall_eq_zero fun u hu => ?_
    have : f u = 0 := by
      by_contra h0
      have := (mem_valBall_iff_le_ord u.ne_zero).mp (hM _ h0)
      rw [mem_ordShell.mp hu] at this
      omega
    rw [this, zero_mul]
  have hhigh : ∀ k, N ≤ k → Z k = f 0 * (if IsUnramifiedChar χ then α ^ k else 0) := by
    intro k hk
    rw [← setIntegral_ordShell_quasiChar hχ k, ← integral_const_mul]
    refine setIntegral_congr_fun (measurableSet_ordShell k) fun u hu => ?_
    rw [hN u ((mem_valBall_iff_le_ord u.ne_zero).mpr (by rw [mem_ordShell.mp hu]; exact hk))]
  have hαT : ‖α * T‖ < 1 := norm_quasiChar_unifUnit_mul_qpow_lt_one hχ hs
  have hαT0 : α * T ≠ 0 := mul_ne_zero (χ _).ne_zero (qpow_ne_zero s)
  have h1 : HasSum (fun k => if k < N then Z k * T ^ k else 0)
      (∑ k ∈ Finset.Ico M N, Z k * T ^ k) := by
    have : HasSum (fun k => if k < N then Z k * T ^ k else 0)
        (∑ k ∈ Finset.Ico M N, if k < N then Z k * T ^ k else 0) :=
      hasSum_sum_of_ne_finset_zero (fun k hk => by
        rw [Finset.mem_Ico, not_and_or, not_le, not_lt] at hk
        rcases hk with hk | hk
        · simp [hlow k hk]
        · simp [not_lt.mpr hk])
    convert this using 1
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [if_pos (Finset.mem_Ico.mp hk).2]
  have h2 : HasSum (fun k => if k < N then 0 else Z k * T ^ k)
      (if IsUnramifiedChar χ then f 0 * (α * T) ^ N * (1 - α * T)⁻¹ else 0) := by
    by_cases hu : IsUnramifiedChar χ
    · rw [if_pos hu]
      refine hasSum_int_of_shift N (fun k hk => by simp [hk]) ?_
      have e : (fun n : ℕ => if N + (n : ℤ) < N then 0 else Z (N + n) * T ^ (N + (n : ℤ))) =
          fun n : ℕ => f 0 * (α * T) ^ N * (α * T) ^ n := by
        funext n
        rw [if_neg (by omega), hhigh _ (by omega), if_pos hu, mul_assoc, ← mul_zpow,
          zpow_add₀ hαT0, zpow_natCast, mul_assoc]
      rw [e]
      exact (hasSum_geometric_of_norm_lt_one hαT).mul_left _
    · rw [if_neg hu]
      convert hasSum_zero with k
      split_ifs with hk
      · rfl
      · rw [hhigh k (not_lt.mp hk), if_neg hu, mul_zero, zero_mul]
  have h12 := h1.add h2
  have e : (fun k => (if k < N then Z k * T ^ k else 0) + (if k < N then 0 else Z k * T ^ k)) =
      fun k => Z k * T ^ k := by
    funext k
    split_ifs <;> simp
  rw [e] at h12
  exact hsum.unique h12

theorem exists_localZeta_eq_mul_evalQpow (hf : f ∈ schwartzBruhat K) (hχ : Continuous χ) :
    ∃ P : LaurentPolynomial ℂ, ∀ s : ℂ, -quasiCharExponent χ < s.re →
      localZeta f χ s = localLFactor χ s * evalQpow K P s := by
  obtain ⟨N₀, M, hN₀, hM⟩ := exists_invariant_of_mem_schwartzBruhat hf
  set N := max N₀ M
  have hMN : M ≤ N := le_max_right _ _
  have hN : ∀ x ∈ valBall K N, f x = f 0 := fun x hx => by
    have := hN₀ 0 x (valBall_antitone (le_max_left _ _) hx)
    rwa [zero_add] at this
  let Z : ℤ → ℂ := fun k => ∫ u in ordShell K k, f u * ((χ u : ℂˣ) : ℂ) ∂multHaar K
  let Q : LaurentPolynomial ℂ :=
    ∑ k ∈ Finset.Ico M N, LaurentPolynomial.C (Z k) * LaurentPolynomial.T k
  have hQ : ∀ s, evalQpow K Q s = ∑ k ∈ Finset.Ico M N, Z k * ((residueCard K : ℂ) ^ (-s)) ^ k :=
    fun s => by simp only [Q, evalQpow_sum, evalQpow_C_mul_T]
  by_cases hu : IsUnramifiedChar χ
  · set α := ((χ (unifUnit K) : ℂˣ) : ℂ)
    refine ⟨(1 - LaurentPolynomial.C α * LaurentPolynomial.T 1) * Q +
      LaurentPolynomial.C (f 0 * α ^ N) * LaurentPolynomial.T N, fun s hs => ?_⟩
    rw [localZeta_eq_sum hf hχ hMN hM hN hs, if_pos hu, localLFactor_of_isUnramified hu,
      evalQpow_add, evalQpow_mul, evalQpow_sub, evalQpow_one, evalQpow_C_mul_T, evalQpow_C_mul_T,
      hQ, zpow_one]
    have hne := one_sub_quasiChar_unifUnit_mul_qpow_ne_zero hχ hs
    rw [mul_add, ← mul_assoc, inv_mul_cancel₀ hne, one_mul, mul_zpow]
    ring
  · refine ⟨Q, fun s hs => ?_⟩
    rw [localZeta_eq_sum hf hχ hMN hM hN hs, if_neg hu, localLFactor_of_not_isUnramified hu, hQ,
      add_zero, one_mul]

open Classical in

def localZetaRatio (f : K → ℂ) (χ : Kˣ →* ℂˣ) (s : ℂ) : ℂ :=
  if h : ∃ P : LaurentPolynomial ℂ, ∀ s : ℂ, -quasiCharExponent χ < s.re →
      localZeta f χ s = localLFactor χ s * evalQpow K P s then
    evalQpow K h.choose s
  else 0

theorem exists_localZetaRatio_eq (hf : f ∈ schwartzBruhat K) (hχ : Continuous χ) :
    ∃ P : LaurentPolynomial ℂ, (∀ s : ℂ, localZetaRatio f χ s = evalQpow K P s) ∧
      ∀ s : ℂ, -quasiCharExponent χ < s.re →
        localZeta f χ s = localLFactor χ s * evalQpow K P s := by
  have h := exists_localZeta_eq_mul_evalQpow hf hχ
  exact ⟨h.choose, fun s => by rw [localZetaRatio, dif_pos h], h.choose_spec⟩

theorem localZeta_eq_localLFactor_mul (hf : f ∈ schwartzBruhat K) (hχ : Continuous χ) {s : ℂ}
    (hs : -quasiCharExponent χ < s.re) :
    localZeta f χ s = localLFactor χ s * localZetaRatio f χ s := by
  obtain ⟨P, hP, hZ⟩ := exists_localZetaRatio_eq hf hχ
  rw [hP, hZ s hs]

theorem localZetaRatio_eq_div (hf : f ∈ schwartzBruhat K) (hχ : Continuous χ) {s : ℂ}
    (hs : -quasiCharExponent χ < s.re) :
    localZetaRatio f χ s = localZeta f χ s / localLFactor χ s := by
  rw [localZeta_eq_localLFactor_mul hf hχ hs, mul_div_cancel_left₀ _ (localLFactor_ne_zero hχ hs)]

theorem differentiable_localZetaRatio (hf : f ∈ schwartzBruhat K) (hχ : Continuous χ) :
    Differentiable ℂ (localZetaRatio f χ) := by
  obtain ⟨P, hP, -⟩ := exists_localZetaRatio_eq hf hχ
  have : localZetaRatio f χ = evalQpow K P := funext hP
  rw [this]
  exact differentiable_evalQpow P

omit [MeasurableSpace K] [BorelSpace K] in
theorem meromorphicOn_localLFactor (χ : Kˣ →* ℂˣ) : MeromorphicOn (localLFactor χ) Set.univ := by
  intro s _
  by_cases h : IsUnramifiedChar χ
  · have e : localLFactor χ = fun s =>
        (1 - ((χ (unifUnit K) : ℂˣ) : ℂ) * (residueCard K : ℂ) ^ (-s))⁻¹ :=
      funext fun s => localLFactor_of_isUnramified h s
    rw [e]
    exact ((((differentiable_qpow (K := K)).const_mul _).const_sub 1).analyticAt s).meromorphicAt.inv
  · have e : localLFactor χ = fun _ => (1 : ℂ) :=
      funext fun s => localLFactor_of_not_isUnramified h s
    rw [e]
    exact analyticAt_const.meromorphicAt

theorem meromorphicOn_localZetaContinuation (hf : f ∈ schwartzBruhat K) (hχ : Continuous χ) :
    MeromorphicOn (fun s => localLFactor χ s * localZetaRatio f χ s) Set.univ ∧
      ∀ s : ℂ, -quasiCharExponent χ < s.re →
        localZeta f χ s = localLFactor χ s * localZetaRatio f χ s := by
  refine ⟨fun s hs => ?_, fun s hs => localZeta_eq_localLFactor_mul hf hχ hs⟩
  exact (meromorphicOn_localLFactor χ s hs).mul
    ((differentiable_localZetaRatio hf hχ).analyticAt s).meromorphicAt

end ZetaNonvanishing₂

end GroundTheory.LocalField
