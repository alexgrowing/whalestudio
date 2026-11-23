import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDHPrimeD

open Finset Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet
open LSeries ArithmeticFunction DirichletCharacter

lemma dhpr_partial {M : ℕ} [NeZero M] (χ₁ : DirichletCharacter ℂ M) (h1 : χ₁ ^ 2 = 1) (k : ℕ)
    {σ CT CH A : ℝ} (hσ : 1 < σ) (hσ2 : σ ≤ 2) (hCT : 0 ≤ CT) (hCH : 0 ≤ CH) (hA0 : 0 ≤ A)
    (hMert : ∀ y : ℝ, 2 ≤ y → ∑ n ∈ Icc 1 ⌊y⌋₊, (Λ n : ℝ) / (n : ℝ) ≤ CT * Real.log y)
    (hHyp : ∀ y x : ℝ, 1 ≤ y → y ≤ x →
      ∑ n ∈ Finset.Ioc ⌊y⌋₊ ⌊x⌋₊, (∑ d ∈ n.divisors, χ₁ (d : ZMod M)).re / (n : ℝ) ≤
        A * Real.log (x / y) + CH * M * (Real.log y + 1) / Real.sqrt y)
    (v0 : ℕ) (hv0pos : 0 < v0) (N : ℕ) :
    ∑ n ∈ range N, dhprF χ₁ k σ n ≤ 2 * CT * (v0 : ℝ) ^ (k + 1) +
      (2 * A * (2 * Real.exp 2 * ((k : ℝ) + 2) * (((k : ℝ) + 1) * k.factorial) / (σ - 1) ^ (k + 2))
      + 2 * CH * M * (Real.exp 1 * (((k : ℝ) + 1) * k.factorial) / (σ - 1) ^ (k + 1) *
          (20 * Real.exp (-((v0 : ℝ) / 4))))) := by
  have hη : 0 < σ - 1 := by linarith
  have hvV : v0 ≤ v0 + N := Nat.le_add_right _ _
  have hNZ : N ≤ ⌊Real.exp ((v0 + N : ℕ) : ℝ)⌋₊ := by
    apply Nat.le_floor
    have := Real.add_one_le_exp ((v0 + N : ℕ) : ℝ)
    push_cast at this ⊢
    have : (0 : ℝ) ≤ v0 := Nat.cast_nonneg _
    linarith
  have hYZ := dhpr_floor_mono hvV
  have hrange : range (⌊Real.exp ((v0 + N : ℕ) : ℝ)⌋₊ + 1) =
      insert 0 (Ioc 0 ⌊Real.exp ((v0 + N : ℕ) : ℝ)⌋₊) := by
    ext n; simp only [mem_range, mem_insert, mem_Ioc]; omega
  have hf0 : dhprF χ₁ k σ 0 = 0 := by simp [dhprF]
  have hHyp' : ∀ v : ℕ, ∑ n ∈ Ioc ⌊Real.exp (v : ℝ)⌋₊ ⌊Real.exp ((v + 1 : ℕ) : ℝ)⌋₊,
      (∑ d ∈ n.divisors, χ₁ (d : ZMod M)).re / (n : ℝ) ≤
        A + CH * M * (((v : ℝ) + 1) * Real.exp (-((v : ℝ) / 2))) := by
    intro v
    have h := hHyp (Real.exp (v : ℝ)) (Real.exp ((v + 1 : ℕ) : ℝ))
      (Real.one_le_exp (Nat.cast_nonneg v)) (Real.exp_le_exp.mpr (by push_cast; linarith))
    rwa [dhpr_hyper_simp] at h
  calc ∑ n ∈ range N, dhprF χ₁ k σ n
      ≤ ∑ n ∈ range (⌊Real.exp ((v0 + N : ℕ) : ℝ)⌋₊ + 1), dhprF χ₁ k σ n :=
        sum_le_sum_of_subset_of_nonneg (range_mono (by omega))
          (fun n _ _ => dhpr_term_nonneg χ₁ h1 k n σ)
    _ = ∑ n ∈ Ioc 0 ⌊Real.exp ((v0 + N : ℕ) : ℝ)⌋₊, dhprF χ₁ k σ n := by
        rw [hrange, sum_insert (by simp), hf0, zero_add]
    _ = ∑ n ∈ Ioc 0 ⌊Real.exp (v0 : ℝ)⌋₊, dhprF χ₁ k σ n +
          ∑ n ∈ Ioc ⌊Real.exp (v0 : ℝ)⌋₊ ⌊Real.exp ((v0 + N : ℕ) : ℝ)⌋₊, dhprF χ₁ k σ n :=
        (sum_Ioc_consecutive _ (Nat.zero_le _) hYZ).symm
    _ ≤ _ := add_le_add (dhpr_small χ₁ h1 k hσ.le v0 hv0pos hCT hMert)
        (dhpr_large χ₁ h1 k hσ.le rfl hη (by linarith) v0 (v0 + N) hvV hA0 hCH hHyp')

lemma dhpr_arith (k : ℕ) {CT CD CH C A ℓ lam η F E M v0 : ℝ}
    (hCT : 0 ≤ CT) (hCD : 0 ≤ CD) (hCH : 0 ≤ CH)
    (hC1 : 30 * CD ≤ C) (hC2 : 18 * CT + 9 ≤ C) (hC3 : 110 * CH ≤ C)
    (hM0 : 0 < M) (hℓ1 : 1 ≤ ℓ) (hv00 : 0 ≤ v0) (hv0ℓ : v0 ≤ 9 * ℓ) (hA0 : 0 ≤ A)
    (hA : A ≤ CD * ℓ ^ 2 * lam) (hlam : 0 < lam) (hη : 0 < η) (hF : 0 < F) (hE0 : 0 ≤ E)
    (hexp : E ≤ 1 / M ^ 2) :
    2 * CT * v0 ^ (k + 1) +
      (2 * A * (2 * Real.exp 2 * ((k : ℝ) + 2) * (((k : ℝ) + 1) * F) / η ^ (k + 2))
      + 2 * CH * M * (Real.exp 1 * (((k : ℝ) + 1) * F) / η ^ (k + 1) * (20 * E))) ≤
    (C * lam * ℓ ^ 2 * ((k : ℝ) + 2) ^ 2 / η ^ (k + 2) + (C * ℓ) ^ (k + 1) / F
      + C * ((k : ℝ) + 2) * ℓ ^ 2 / (M * η ^ (k + 1))) * F := by
  have hd9 := Real.exp_one_lt_d9
  have he1 : Real.exp 1 ≤ 2.72 := by norm_num at hd9 ⊢; linarith
  have he2 : Real.exp 2 ≤ 7.4 := by
    have h : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    rw [h]; nlinarith [Real.exp_pos 1]
  have hC9 : 9 ≤ C := by linarith
  have hk : (k : ℝ) + 1 ≤ (k : ℝ) + 2 := by linarith
  have hi : 2 * CT * v0 ^ (k + 1) ≤ (C * ℓ) ^ (k + 1) := by
    calc 2 * CT * v0 ^ (k + 1) ≤ 2 * CT * (9 * ℓ) ^ (k + 1) := by gcongr
      _ = (18 * CT) * 9 ^ k * ℓ ^ (k + 1) := by ring
      _ ≤ C * C ^ k * ℓ ^ (k + 1) := by gcongr; linarith
      _ = (C * ℓ) ^ (k + 1) := by ring
  have hii : 2 * A * (2 * Real.exp 2 * ((k : ℝ) + 2) * (((k : ℝ) + 1) * F) / η ^ (k + 2)) ≤
      C * lam * ℓ ^ 2 * ((k : ℝ) + 2) ^ 2 / η ^ (k + 2) * F := by
    calc 2 * A * (2 * Real.exp 2 * ((k : ℝ) + 2) * (((k : ℝ) + 1) * F) / η ^ (k + 2))
        = (4 * A * Real.exp 2 * ((k : ℝ) + 2) * ((k : ℝ) + 1)) * (F / η ^ (k + 2)) := by ring
      _ ≤ (4 * (CD * ℓ ^ 2 * lam) * 7.4 * ((k : ℝ) + 2) * ((k : ℝ) + 2)) * (F / η ^ (k + 2)) := by
          gcongr
      _ = (29.6 * CD) * lam * ℓ ^ 2 * ((k : ℝ) + 2) ^ 2 * (F / η ^ (k + 2)) := by ring
      _ ≤ C * lam * ℓ ^ 2 * ((k : ℝ) + 2) ^ 2 * (F / η ^ (k + 2)) := by gcongr; linarith
      _ = _ := by ring
  have hiii : 2 * CH * M * (Real.exp 1 * (((k : ℝ) + 1) * F) / η ^ (k + 1) * (20 * E)) ≤
      C * ((k : ℝ) + 2) * ℓ ^ 2 / (M * η ^ (k + 1)) * F := by
    have hME : M * E ≤ 1 / M := by
      calc M * E ≤ M * (1 / M ^ 2) := by gcongr
        _ = 1 / M := by field_simp
    have hℓ2 : 1 ≤ ℓ ^ 2 := by nlinarith
    have hC' : 108.8 * CH ≤ C * ℓ ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hℓ2 (by linarith : (0 : ℝ) ≤ C)]
    calc 2 * CH * M * (Real.exp 1 * (((k : ℝ) + 1) * F) / η ^ (k + 1) * (20 * E))
        = (40 * CH * Real.exp 1 * ((k : ℝ) + 1)) * (M * E) * (F / η ^ (k + 1)) := by ring
      _ ≤ (40 * CH * 2.72 * ((k : ℝ) + 2)) * (1 / M) * (F / η ^ (k + 1)) := by gcongr
      _ = (108.8 * CH) * ((k : ℝ) + 2) * (F / (M * η ^ (k + 1))) := by field_simp; ring
      _ ≤ (C * ℓ ^ 2) * ((k : ℝ) + 2) * (F / (M * η ^ (k + 1))) := by gcongr
      _ = _ := by ring
  have hexpand : (C * lam * ℓ ^ 2 * ((k : ℝ) + 2) ^ 2 / η ^ (k + 2) + (C * ℓ) ^ (k + 1) / F
      + C * ((k : ℝ) + 2) * ℓ ^ 2 / (M * η ^ (k + 1))) * F =
      C * lam * ℓ ^ 2 * ((k : ℝ) + 2) ^ 2 / η ^ (k + 2) * F + (C * ℓ) ^ (k + 1)
      + C * ((k : ℝ) + 2) * ℓ ^ 2 / (M * η ^ (k + 1)) * F := by
    rw [add_mul, add_mul, div_mul_cancel₀ _ hF.ne']
  rw [hexpand]
  linarith

lemma dhpr_main {M : ℕ} [NeZero M] (χ₁ : DirichletCharacter ℂ M) (k : ℕ) {β₁ σ CH CD CT C : ℝ}
    (hM : 3 ≤ M) (h1 : χ₁ ^ 2 = 1) (hβ1 : β₁ < 1) (hσ : 1 < σ) (hσ2 : σ ≤ 2)
    (hCH : 0 ≤ CH) (hCD : 0 ≤ CD) (hCT : 0 ≤ CT)
    (hC1 : 30 * CD ≤ C) (hC2 : 18 * CT + 9 ≤ C) (hC3 : 110 * CH ≤ C)
    (hA : ‖DirichletCharacter.LFunction χ₁ 1‖ ≤ CD * Real.log (3 * M) ^ 2 * (1 - β₁))
    (hMert : ∀ y : ℝ, 2 ≤ y → ∑ n ∈ Icc 1 ⌊y⌋₊, (Λ n : ℝ) / (n : ℝ) ≤ CT * Real.log y)
    (hHyp : ∀ y x : ℝ, 1 ≤ y → y ≤ x →
      ∑ n ∈ Finset.Ioc ⌊y⌋₊ ⌊x⌋₊, (∑ d ∈ n.divisors, χ₁ (d : ZMod M)).re / (n : ℝ) ≤
        ‖DirichletCharacter.LFunction χ₁ 1‖ * Real.log (x / y)
          + CH * M * (Real.log y + 1) / Real.sqrt y) :
    ((-1 : ℂ) ^ k * (iteratedDeriv k (negLD (1 : DirichletCharacter ℂ M)) (σ : ℂ)
        + iteratedDeriv k (negLD χ₁) (σ : ℂ))).re / (k.factorial : ℝ) ≤
      C * (1 - β₁) * Real.log (3 * M) ^ 2 * (k + 2) ^ 2 / (σ - 1) ^ (k + 2)
        + (C * Real.log (3 * M)) ^ (k + 1) / (k.factorial : ℝ)
        + C * (k + 2) * Real.log (3 * M) ^ 2 / (M * (σ - 1) ^ (k + 1)) := by
  have hM3 : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hM0 : (0 : ℝ) < M := by linarith
  have hlogM : 0 < Real.log M := Real.log_pos (by linarith)
  have hlogM3 : Real.log M ≤ Real.log (3 * M) := Real.log_le_log hM0 (by linarith)
  have hd9 := Real.exp_one_lt_d9
  have hℓ1 : 1 ≤ Real.log (3 * M) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    norm_num at hd9
    linarith
  have hF : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  have hA0 : 0 ≤ ‖DirichletCharacter.LFunction χ₁ 1‖ := norm_nonneg _
  have hS : HasSum (dhprF χ₁ k σ) _ := dhpr_hasSum χ₁ k hσ
  have hv0a : 8 * Real.log M ≤ (⌈8 * Real.log M⌉₊ : ℝ) := Nat.le_ceil _
  have hv0b : (⌈8 * Real.log M⌉₊ : ℝ) < 8 * Real.log M + 1 := Nat.ceil_lt_add_one (by positivity)
  have hv0pos : 0 < ⌈8 * Real.log M⌉₊ := Nat.ceil_pos.mpr (by linarith)
  have hexp : Real.exp (-((⌈8 * Real.log M⌉₊ : ℝ) / 4)) ≤ 1 / (M : ℝ) ^ 2 := by
    have h2 : Real.exp (-(2 * Real.log M)) = 1 / (M : ℝ) ^ 2 := by
      rw [Real.exp_neg, show 2 * Real.log M = Real.log ((M : ℝ) ^ 2) by
        rw [Real.log_pow]; push_cast; ring, Real.exp_log (by positivity), one_div]
    rw [← h2]; exact Real.exp_le_exp.mpr (by linarith)
  have hle := le_of_tendsto' hS.tendsto_sum_nat
    (dhpr_partial χ₁ h1 k hσ hσ2 hCT hCH hA0 hMert hHyp _ hv0pos)
  rw [div_le_iff₀ hF]
  refine hle.trans ?_
  exact dhpr_arith k hCT hCD hCH hC1 hC2 hC3 hM0 hℓ1 (Nat.cast_nonneg _) (by linarith) hA0 hA
    (by linarith) (by linarith) hF (Real.exp_pos _).le hexp

theorem deuring_heilbronn_prime_sum : DHPrimeOf := by
  intro hH
  obtain ⟨CH, hCH, hHyp⟩ := hH
  obtain ⟨CD, hCD, hL1⟩ := lfunction_one_le_of_siegel_zero
  obtain ⟨CT, hCT, hMert⟩ := Formalism.HermitianLattices.Ext.BoxTail.tail_mertens
  refine ⟨max (max (30 * CD) (18 * CT + 9)) (110 * CH),
    lt_of_lt_of_le (by linarith : (0 : ℝ) < 18 * CT + 9) (le_max_of_le_left (le_max_right _ _)), ?_⟩
  intro M _ χ₁ β₁ σ k hM h1 hne hz hβ hβ1 hσ hσ2
  exact dhpr_main χ₁ k hM h1 hβ1 hσ hσ2 hCH.le hCD hCT
    (le_max_of_le_left (le_max_left _ _)) (le_max_of_le_left (le_max_right _ _)) (le_max_right _ _)
    (hL1 M χ₁ β₁ hne hz hβ hβ1) hMert (fun y x hy hyx => hHyp M χ₁ y x hM h1 hne hy hyx)

end Formalism.HermitianLattices.Ext.PrimesInProgressions
