import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AdaptSelf
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PairBdNonneg
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsNormalFormStabilizerMeasure

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt GlobalTheory.DegAsm
open scoped Pointwise ENNReal Classical
namespace GlobalTheory.DegAsm

theorem parith_small (k f g : ℕ) (b e : ℝ) (hb : 2 ≤ b) (hk : 9 ≤ k) (hf : 1 ≤ f) (hfk : f ≤ k)
    (he : 42 * (e * Real.log b) ≤ k) (hg : ((k : ℝ) * b) ^ 8 ≤ g) :
    (32 / (g : ℝ)) ^ (k * f) * ((4 * k * f : ℕ) : ℝ) ^ (4 * f) * (b ^ (e * f)) ^ 42 ≤ 1 / 2 := by
  have hb0 : 0 < b := by linarith
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
  have hk0 : (0 : ℝ) < k := by linarith
  have hfk' : (f : ℝ) ≤ k := by exact_mod_cast hfk
  have h1 : (b ^ (e * f)) ^ 42 = (Real.exp (42 * (e * Real.log b))) ^ f := by
    rw [Real.rpow_def_of_pos hb0, ← Real.exp_nat_mul, ← Real.exp_nat_mul]
    congr 1; push_cast; ring
  rw [h1, pow_mul, pow_mul, ← mul_pow, ← mul_pow]
  have hb8 : (256 : ℝ) ≤ b ^ 8 := by
    calc (256 : ℝ) = 2 ^ 8 := by norm_num
      _ ≤ b ^ 8 := by gcongr
  have hk8 : (1 : ℝ) ≤ (k : ℝ) ^ 8 := one_le_pow₀ hk1
  have hg' : 256 * (k : ℝ) ^ 8 ≤ g := by
    refine le_trans ?_ hg
    rw [mul_pow]; nlinarith
  have hg0 : (0 : ℝ) < g := by linarith
  have h2 : 32 / (g : ℝ) ≤ (1 / 8) * (1 / (k : ℝ) ^ 8) := by
    rw [div_mul_div_comm, div_le_div_iff₀ hg0 (by positivity)]; linarith
  have h3 : (32 / (g : ℝ)) ^ k ≤ (1 / 8) ^ k * (1 / (k : ℝ) ^ 8) := by
    calc (32 / (g : ℝ)) ^ k ≤ ((1 / 8) * (1 / (k : ℝ) ^ 8)) ^ k := by gcongr
      _ = (1 / 8) ^ k * (1 / (k : ℝ) ^ 8) ^ k := mul_pow _ _ _
      _ ≤ _ := by
        gcongr
        exact pow_le_of_le_one (by positivity) (by rw [div_le_one (by positivity)]; exact hk8) (by omega)
  have h4 : ((4 * k * f : ℕ) : ℝ) ^ 4 ≤ 256 * (k : ℝ) ^ 8 := by
    push_cast
    calc (4 * (k : ℝ) * f) ^ 4 ≤ (4 * (k : ℝ) * k) ^ 4 := by gcongr
      _ = _ := by ring
  have h5 : Real.exp (42 * (e * Real.log b)) ≤ 4 ^ k := by
    calc _ ≤ Real.exp (k * 1) := Real.exp_le_exp.2 (by linarith)
      _ = Real.exp 1 ^ k := Real.exp_nat_mul _ _
      _ ≤ 4 ^ k := by
        gcongr
        have := Real.exp_one_lt_d9
        linarith
  have h6 : (32 / (g : ℝ)) ^ k * ((4 * k * f : ℕ) : ℝ) ^ 4 * Real.exp (42 * (e * Real.log b)) ≤ 1 / 2 := by
    calc _ ≤ ((1 / 8) ^ k * (1 / (k : ℝ) ^ 8)) * (256 * (k : ℝ) ^ 8) * 4 ^ k := by gcongr
      _ = 256 * ((1 / 8) * 4) ^ k := by rw [mul_pow]; field_simp
      _ = 256 * (1 / 2) ^ k := by norm_num
      _ ≤ 256 * (1 / 2) ^ 9 := by
        gcongr 256 * ?_
        exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hk
      _ = 1 / 2 := by norm_num
  exact le_trans (pow_le_of_le_one (by positivity) (by linarith) (by omega)) h6

theorem parith_bracket (k : ℕ) (M q q' Z : ℝ) (hM0 : 0 ≤ M) (hq : 0 ≤ q) (hq' : 0 ≤ q') (hqq : q' ≤ q) (hZ : 1 ≤ Z)
    (hqZ : q ≤ 1 / 2 * Z) :
    1 + M * (∑ s ∈ Finset.Ico 1 k, q ^ s) + q' ^ k ≤ (2 + 2 * M) * Z ^ k := by
  have hZk : 1 ≤ Z ^ k := one_le_pow₀ hZ
  have h1 : ∑ s ∈ Finset.Ico 1 k, q ^ s ≤ 2 * Z ^ k := by
    calc ∑ s ∈ Finset.Ico 1 k, q ^ s ≤ ∑ s ∈ Finset.range k, q ^ s := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro s hs; simp at hs ⊢; omega
          · intros; positivity
      _ ≤ ∑ s ∈ Finset.range k, (1 / 2 : ℝ) ^ s * Z ^ k := by
          apply Finset.sum_le_sum
          intro s hs
          have hs' : s ≤ k := (Finset.mem_range.1 hs).le
          calc q ^ s ≤ (1 / 2 * Z) ^ s := by gcongr
            _ = (1 / 2 : ℝ) ^ s * Z ^ s := mul_pow _ _ _
            _ ≤ _ := by gcongr
      _ ≤ 2 * Z ^ k := by
          rw [← Finset.sum_mul]
          gcongr
          exact sum_geometric_two_le k
  have h2 : q' ^ k ≤ Z ^ k := by gcongr; linarith
  have h3 : M * (∑ s ∈ Finset.Ico 1 k, q ^ s) ≤ M * (2 * Z ^ k) := by gcongr
  linarith

theorem parith_rest (r : ℕ) (hr : 1 ≤ r) (c f Del Db NT U : ℝ) (hc : c ≤ 4 * r) (hU : 1 ≤ U) (h8 : 8 ^ (r + 1) ≤ U)
    (hf : f ^ 2 ≤ U) (hD : 1 ≤ Del) (hDU : Del ≤ U) (hN : 0 ≤ NT) (hNU : NT ≤ U) (hDb : 0 ≤ Db) (hDbU : Db ≤ U ^ r) :
    8 ^ (r + 1) * f ^ 2 * Del ^ (3 * c + 6) * NT ^ 2 * (Db * Del * NT) ^ (10000 * (r + 1) ^ 3) ≤ U ^ (250000 * r ^ 4) := by
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have h1 : Del ^ (3 * c + 6) ≤ U ^ (18 * r) := by
    calc Del ^ (3 * c + 6) ≤ Del ^ ((18 * r : ℕ) : ℝ) := by
          apply Real.rpow_le_rpow_of_exponent_le hD; push_cast; linarith
      _ = Del ^ (18 * r) := Real.rpow_natCast _ _
      _ ≤ _ := by gcongr
  calc _ ≤ U * U * U ^ (18 * r) * U ^ 2 * (U ^ r * U * U) ^ (10000 * (r + 1) ^ 3) := by gcongr
    _ = U ^ (4 + 18 * r + (r + 2) * (10000 * (r + 1) ^ 3)) := by
        rw [show U ^ r * U * U = U ^ (r + 2) by ring, ← pow_mul, pow_add, pow_add]; ring
    _ ≤ _ := by
        apply pow_le_pow_right₀ hU
        have a1 : (r + 1) ^ 3 ≤ (2 * r) ^ 3 := by gcongr; omega
        have a2 : (r + 2) * (10000 * (r + 1) ^ 3) ≤ (3 * r) * (10000 * (2 * r) ^ 3) := by gcongr; omega
        have a3 : r ≤ r ^ 4 := Nat.le_self_pow (by norm_num) r
        have a4 : (3 * r) * (10000 * (2 * r) ^ 3) = 240000 * r ^ 4 := by ring
        omega

theorem parith_const (r f : ℕ) (hr : 1 ≤ r) (hf : 1 ≤ f) (b w c : ℝ) (hb : 2 ≤ b) (hw : 1 ≤ w) (hwb : w ≤ b)
    (hc : c ≤ 4 * r) (hfb : (f : ℝ) ≤ b ^ (2 * r)) :
    2 + 2 * ((20 * (f : ℝ) * w ^ 2) ^ (2 * (f : ℝ) * (6 + c)) * w ^ f) ≤ (b ^ (r ^ 2 * f)) ^ 183 := by
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hf' : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hb1 : 1 ≤ b := by linarith
  have h20 : (20 : ℝ) ≤ b ^ 5 := by
    calc (20 : ℝ) ≤ 2 ^ 5 := by norm_num
      _ ≤ b ^ 5 := by gcongr
  have hw2 : 1 ≤ w ^ 2 := one_le_pow₀ hw
  have h1 : (20 * (f : ℝ) * w ^ 2) ^ (2 * (f : ℝ) * (6 + c)) ≤ b ^ ((9 * r) * (20 * r * f)) := by
    calc _ ≤ (20 * (f : ℝ) * w ^ 2) ^ ((20 * r * f : ℕ) : ℝ) := by
          apply Real.rpow_le_rpow_of_exponent_le (by nlinarith); push_cast; nlinarith
      _ = (20 * (f : ℝ) * w ^ 2) ^ (20 * r * f) := Real.rpow_natCast _ _
      _ ≤ (b ^ 5 * b ^ (2 * r) * b ^ 2) ^ (20 * r * f) := by gcongr
      _ ≤ (b ^ (9 * r)) ^ (20 * r * f) := by
          gcongr
          rw [← pow_add, ← pow_add]
          exact pow_le_pow_right₀ hb1 (by omega)
      _ = _ := by rw [← pow_mul]
  have hn : f ≤ r ^ 2 * f := Nat.le_mul_of_pos_left _ (by positivity)
  set X := b ^ (r ^ 2 * f) with hX
  have hX2 : b ^ f ≤ X := pow_le_pow_right₀ hb1 hn
  have hX3 : 2 ≤ X := le_trans (le_trans hb (le_self_pow₀ hb1 (by omega))) hX2
  have h2 : b ^ ((9 * r) * (20 * r * f)) = X ^ 180 := by rw [hX, ← pow_mul]; congr 1; ring
  have h3 : w ^ f ≤ X := le_trans (by gcongr) hX2
  have h4 : (20 * (f : ℝ) * w ^ 2) ^ (2 * (f : ℝ) * (6 + c)) * w ^ f ≤ X ^ 181 := by
    calc _ ≤ X ^ 180 * X := by rw [← h2]; gcongr
      _ = _ := by ring
  have h5 : 1 ≤ X ^ 181 := one_le_pow₀ (by linarith)
  have h6 : X ^ 183 = X ^ 181 * X ^ 2 := by ring
  have h7 : 4 ≤ X ^ 2 := by nlinarith
  rw [h6]
  nlinarith

theorem parith_pair (K : Type) [Field K] [NumberField K] (k g r T x x' : ℕ) (hr : 1 ≤ r) (A S S' : ℝ) (hA : 1 ≤ A)
    (hS : 1 ≤ S) (hS' : 1 ≤ S') (hx : 1 ≤ x) (hx' : 1 ≤ x') (hxA : (x : ℝ) ≤ A * S ^ 2) (hxA' : (x' : ℝ) ≤ A * S' ^ 2)
    (hT : 1 ≤ T) (hTA : (T : ℝ) ^ Formalism.HermitianLatticesTheory.fDeg K ≤ A) (hc : cf K ≤ 4 * r) (hv : 1 ≤ Formalism.HermitianLatticesTheory.vInv K)
    (hsm : (32 / (g : ℝ)) ^ (k * Formalism.HermitianLatticesTheory.fDeg K) * ((4 * k * Formalism.HermitianLatticesTheory.fDeg K : ℕ) : ℝ) ^ (4 * Formalism.HermitianLatticesTheory.fDeg K) * A ^ 42 ≤ 1 / 2)
    (hco : 2 + 2 * ((20 * (Formalism.HermitianLatticesTheory.fDeg K : ℝ) * (2 * Formalism.HermitianLatticesTheory.vInv K) ^ 2) ^ (2 * (Formalism.HermitianLatticesTheory.fDeg K : ℝ) * (6 + cf K)) *
      (2 * Formalism.HermitianLatticesTheory.vInv K) ^ Formalism.HermitianLatticesTheory.fDeg K) ≤ A ^ 183) :
    pairBd K k g r T x x' ≤ ((x : ℝ) * x') ^ ((k : ℝ) / 2) *
      (((A * S ^ 2) * (A * S' ^ 2)) ^ (96 * r + 183) * (S * S') ^ (14 * k)) := by
  unfold pairBd
  simp only []
  generalize Formalism.HermitianLatticesTheory.fDeg K = f at *
  generalize cf K = c at *
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hx1' : (1 : ℝ) ≤ x' := by exact_mod_cast hx'
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hD1 : (1 : ℝ) ≤ (T : ℝ) ^ (2 * f) := one_le_pow₀ hT1
  have hDA : (T : ℝ) ^ (2 * f) ≤ A ^ 2 := by rw [mul_comm, pow_mul]; gcongr
  generalize (T : ℝ) ^ (2 * f) = D at *
  have hD0 : 0 ≤ D := by linarith
  have hxx : (1 : ℝ) ≤ (x : ℝ) * x' := one_le_mul_of_one_le_of_one_le hx1 hx1'
  have hY1 : (1 : ℝ) ≤ (x : ℝ) * x' * D ^ 2 := one_le_mul_of_one_le_of_one_le hxx (one_le_pow₀ hD1)
  have hYA : (x : ℝ) * x' * D ^ 2 ≤ A ^ 6 * (S * S') ^ 2 := by
    calc _ ≤ (A * S ^ 2) * (A * S' ^ 2) * (A ^ 2) ^ 2 := by gcongr
      _ = _ := by ring
  have hDY : D * x * x' ≤ ((x : ℝ) * x' * D ^ 2) ^ 7 := by
    refine le_trans ?_ (le_self_pow₀ hY1 (by norm_num))
    have : D ≤ D ^ 2 := le_self_pow₀ hD1 (by norm_num)
    calc D * x * x' = x * x' * D := by ring
      _ ≤ _ := by gcongr
  generalize (x : ℝ) * x' * D ^ 2 = Y at *
  have hY0 : 0 ≤ Y := by linarith
  have hv0 : 0 ≤ Formalism.HermitianLatticesTheory.vInv K := by linarith
  have hSS : 1 ≤ S * S' := one_le_mul_of_one_le_of_one_le hS hS'
  have hS2 : 1 ≤ S ^ 2 := one_le_pow₀ hS
  have hS2' : 1 ≤ S' ^ 2 := one_le_pow₀ hS'
  have hZ : 1 ≤ (S * S') ^ 14 := one_le_pow₀ hSS
  set V := (A * S ^ 2) * (A * S' ^ 2) with hV
  have hVe : V = A ^ 2 * (S * S') ^ 2 := by rw [hV]; ring
  have hSS2 : 1 ≤ (S * S') ^ 2 := one_le_pow₀ hSS
  have hAV : A ≤ V := by
    rw [hVe]
    calc A = A * 1 := by ring
      _ ≤ _ := by gcongr; exact le_self_pow₀ hA (by norm_num)
  have hYV : Y ≤ V ^ 3 := by
    refine le_trans hYA ?_
    rw [hVe, mul_pow (A ^ 2), ← pow_mul]
    gcongr
    exact le_self_pow₀ hSS2 (by norm_num)
  have h1 : Y ^ (6 * (r : ℝ) + 10 + 4 * c) ≤ V ^ (96 * r) := by
    calc _ ≤ Y ^ ((32 * r : ℕ) : ℝ) := by
          apply Real.rpow_le_rpow_of_exponent_le hY1; push_cast; linarith
      _ = Y ^ (32 * r) := Real.rpow_natCast _ _
      _ ≤ (V ^ 3) ^ (32 * r) := by gcongr
      _ = _ := by rw [← pow_mul]; congr 1; ring
  have hB := parith_bracket k
    ((20 * (f : ℝ) * (2 * Formalism.HermitianLatticesTheory.vInv K) ^ 2) ^ (2 * (f : ℝ) * (6 + c)) * (2 * Formalism.HermitianLatticesTheory.vInv K) ^ f)
    ((32 / (g : ℝ)) ^ (k * f) * ((4 * k * f : ℕ) : ℝ) ^ (4 * f) * Y ^ 7)
    ((2 / (g : ℝ)) ^ (k * f) * ((4 * k * f : ℕ) : ℝ) ^ (4 * f) * D * x * x') ((S * S') ^ 14)
    (by positivity) (by positivity) (by positivity)
    (by
      rw [mul_assoc _ D, mul_assoc _ (D * x)]
      gcongr
      norm_num)
    hZ
    (by
      calc _ ≤ (32 / (g : ℝ)) ^ (k * f) * ((4 * k * f : ℕ) : ℝ) ^ (4 * f) * (A ^ 6 * (S * S') ^ 2) ^ 7 := by gcongr
        _ = ((32 / (g : ℝ)) ^ (k * f) * ((4 * k * f : ℕ) : ℝ) ^ (4 * f) * A ^ 42) * (S * S') ^ 14 := by ring
        _ ≤ _ := by gcongr)
  have hB' := le_trans hB (mul_le_mul_of_nonneg_right (le_trans hco (pow_le_pow_left₀ (by linarith) hAV 183))
    (by positivity))
  have hV0 : 0 ≤ V := by linarith
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  calc _ ≤ V ^ (96 * r) * (V ^ 183 * ((S * S') ^ 14) ^ k) := mul_le_mul h1 hB' (by positivity) (by positivity)
    _ = _ := by rw [← pow_mul, pow_add V, ← mul_assoc]

theorem parith_cancel (x x' Del Del' e : ℝ) (hx : 0 < x) (hx' : 0 < x') (hD : 0 ≤ Del) (hD' : 0 ≤ Del') :
    (x * x') ^ e * ((Del / x) ^ e * (Del' / x') ^ e) = Del ^ e * Del' ^ e := by
  rw [Real.mul_rpow hx.le hx'.le, Real.div_rpow hD hx.le, Real.div_rpow hD' hx'.le]
  have := Real.rpow_pos_of_pos hx e
  have := Real.rpow_pos_of_pos hx' e
  field_simp

theorem parith_sum (K : Type) [Field K] [NumberField K] [StarRing K] (k g r T : ℕ) (hr : 1 ≤ r) (A S S' Del Del' Db Db' : ℝ)
    (hA : 1 ≤ A) (hS : 1 ≤ S) (hS' : 1 ≤ S') (hD : 1 ≤ Del) (hD' : 1 ≤ Del') (hDb : 1 ≤ Db) (hDb' : 1 ≤ Db')
    (hDA : Del ≤ A * S ^ 2) (hDA' : Del' ≤ A * S' ^ 2) (hDbA : Db ≤ (A * S ^ 2) ^ r) (hDbA' : Db' ≤ (A * S' ^ 2) ^ r)
    (hT : 1 ≤ T) (hTA : (T : ℝ) ^ Formalism.HermitianLatticesTheory.fDeg K ≤ A) (hc : cf K ≤ 4 * r) (hv : 1 ≤ Formalism.HermitianLatticesTheory.vInv K)
    (h8 : 8 ^ (r + 1) ≤ A) (hf : (Formalism.HermitianLatticesTheory.fDeg K : ℝ) ^ 2 ≤ A)
    (hsm : (32 / (g : ℝ)) ^ (k * Formalism.HermitianLatticesTheory.fDeg K) * ((4 * k * Formalism.HermitianLatticesTheory.fDeg K : ℕ) : ℝ) ^ (4 * Formalism.HermitianLatticesTheory.fDeg K) * A ^ 42 ≤ 1 / 2)
    (hco : 2 + 2 * ((20 * (Formalism.HermitianLatticesTheory.fDeg K : ℝ) * (2 * Formalism.HermitianLatticesTheory.vInv K) ^ 2) ^ (2 * (Formalism.HermitianLatticesTheory.fDeg K : ℝ) * (6 + cf K)) *
      (2 * Formalism.HermitianLatticesTheory.vInv K) ^ Formalism.HermitianLatticesTheory.fDeg K) ≤ A ^ 183) :
    ∑ x ∈ Finset.Icc 1 ⌊Del⌋₊, ∑ x' ∈ Finset.Icc 1 ⌊Del'⌋₊, pairBd K k g r T x x' *
      (datBd K k r Del Db ((T : ℝ) ^ Formalism.HermitianLatticesTheory.fDeg K) x * datBd K k r Del' Db' ((T : ℝ) ^ Formalism.HermitianLatticesTheory.fDeg K) x') ≤
      (Del ^ ((k : ℝ) / 2) * (A * S ^ 2) ^ (300000 * r ^ 4) * S ^ (14 * k)) *
        (Del' ^ ((k : ℝ) / 2) * (A * S' ^ 2) ^ (300000 * r ^ 4) * S' ^ (14 * k)) := by
  have hS2 : 1 ≤ S ^ 2 := one_le_pow₀ hS
  have hS2' : 1 ≤ S' ^ 2 := one_le_pow₀ hS'
  have hAU : A ≤ A * S ^ 2 := le_mul_of_one_le_right (by linarith) hS2
  have hAU' : A ≤ A * S' ^ 2 := le_mul_of_one_le_right (by linarith) hS2'
  have hR := parith_rest r hr (cf K) (Formalism.HermitianLatticesTheory.fDeg K) Del Db ((T : ℝ) ^ Formalism.HermitianLatticesTheory.fDeg K) (A * S ^ 2) hc (by linarith)
    (by linarith) (by linarith) hD hDA (by positivity) (by linarith) (by linarith) hDbA
  have hR' := parith_rest r hr (cf K) (Formalism.HermitianLatticesTheory.fDeg K) Del' Db' ((T : ℝ) ^ Formalism.HermitianLatticesTheory.fDeg K) (A * S' ^ 2) hc (by linarith)
    (by linarith) (by linarith) hD' hDA' (by positivity) (by linarith) (by linarith) hDbA'
  have hfl : (⌊Del⌋₊ : ℝ) ≤ A * S ^ 2 := le_trans (Nat.floor_le (by linarith)) hDA
  have hfl' : (⌊Del'⌋₊ : ℝ) ≤ A * S' ^ 2 := le_trans (Nat.floor_le (by linarith)) hDA'
  set U := A * S ^ 2 with hU
  set U' := A * S' ^ 2 with hU'
  have hU1 : 1 ≤ U := by linarith
  have hU1' : 1 ≤ U' := by linarith
  have hD0 : 0 ≤ Del := by linarith
  have hD0' : 0 ≤ Del' := by linarith
  set C := (Del ^ ((k : ℝ) / 2) * Del' ^ ((k : ℝ) / 2)) *
    ((U * U') ^ (96 * r + 183) * (S * S') ^ (14 * k) * (U ^ (250000 * r ^ 4) * U' ^ (250000 * r ^ 4))) with hC
  have hC0 : 0 ≤ C := by positivity
  have hterm : ∀ x ∈ Finset.Icc 1 ⌊Del⌋₊, ∀ x' ∈ Finset.Icc 1 ⌊Del'⌋₊, pairBd K k g r T x x' *
      (datBd K k r Del Db ((T : ℝ) ^ Formalism.HermitianLatticesTheory.fDeg K) x * datBd K k r Del' Db' ((T : ℝ) ^ Formalism.HermitianLatticesTheory.fDeg K) x') ≤ C := by
    intro x hx x' hx'
    obtain ⟨hx1, hx2⟩ := Finset.mem_Icc.1 hx
    obtain ⟨hx1', hx2'⟩ := Finset.mem_Icc.1 hx'
    have hxU : (x : ℝ) ≤ U := le_trans (by exact_mod_cast hx2) hfl
    have hxU' : (x' : ℝ) ≤ U' := le_trans (by exact_mod_cast hx2') hfl'
    have hP := parith_pair K k g r T x x' hr A S S' hA hS hS' hx1 hx1' hxU hxU' hT hTA hc hv hsm hco
    have hx0 : (0 : ℝ) < x := by exact_mod_cast hx1
    have hx0' : (0 : ℝ) < x' := by exact_mod_cast hx1'
    rw [hC, ← parith_cancel x x' Del Del' _ hx0 hx0' hD0 hD0']
    unfold datBd
    calc _ ≤ (((x : ℝ) * x') ^ ((k : ℝ) / 2) * ((U * U') ^ (96 * r + 183) * (S * S') ^ (14 * k))) *
          (((Del / x) ^ ((k : ℝ) / 2) * U ^ (250000 * r ^ 4)) * ((Del' / x') ^ ((k : ℝ) / 2) * U' ^ (250000 * r ^ 4))) := by
          gcongr
      _ = _ := by ring
  calc _ ≤ ∑ x ∈ Finset.Icc 1 ⌊Del⌋₊, ∑ x' ∈ Finset.Icc 1 ⌊Del'⌋₊, C :=
        Finset.sum_le_sum fun x hx => Finset.sum_le_sum fun x' hx' => hterm x hx x' hx'
    _ = (⌊Del⌋₊ : ℝ) * (⌊Del'⌋₊ * C) := by simp
    _ ≤ U * (U' * C) := by gcongr
    _ = (Del ^ ((k : ℝ) / 2) * U ^ (1 + (96 * r + 183) + 250000 * r ^ 4) * S ^ (14 * k)) *
        (Del' ^ ((k : ℝ) / 2) * U' ^ (1 + (96 * r + 183) + 250000 * r ^ 4) * S' ^ (14 * k)) := by
        rw [hC, pow_add U, pow_add U, pow_add U', pow_add U', mul_pow U, mul_pow S, pow_one, pow_one]
        generalize U ^ (96 * r + 183) = a1
        generalize U' ^ (96 * r + 183) = a2
        generalize U ^ (250000 * r ^ 4) = a3
        generalize U' ^ (250000 * r ^ 4) = a4
        generalize S ^ (14 * k) = a5
        generalize S' ^ (14 * k) = a6
        ring
    _ ≤ _ := by
        have a3 : r ≤ r ^ 4 := Nat.le_self_pow (by norm_num) r
        have : 1 + (96 * r + 183) + 250000 * r ^ 4 ≤ 300000 * r ^ 4 := by omega
        gcongr

theorem parith_abs (k r : ℕ) (A B S Ch : ℝ) (hA : 1 ≤ A) (hAB : A ≤ B) (hS : 1 ≤ S) (hCh : 300000 ≤ Ch)
    (hk : 300000 * r ^ 4 ≤ k) (E : ℝ) (hE : 0 ≤ E) :
    E * (A * S ^ 2) ^ (300000 * r ^ 4) * S ^ (14 * k) ≤ E * B ^ (Ch * (r : ℝ) ^ 4) * S ^ (16 * (k : ℝ)) := by
  have h1 : A ^ (300000 * r ^ 4) ≤ B ^ (Ch * (r : ℝ) ^ 4) := by
    calc _ ≤ B ^ (300000 * r ^ 4) := by gcongr
      _ = B ^ ((300000 * r ^ 4 : ℕ) : ℝ) := (Real.rpow_natCast _ _).symm
      _ ≤ _ := by
        apply Real.rpow_le_rpow_of_exponent_le (by linarith); push_cast; gcongr
  have h2 : (S ^ 2) ^ (300000 * r ^ 4) * S ^ (14 * k) ≤ S ^ (16 * (k : ℝ)) := by
    rw [← pow_mul, ← pow_add, show (16 * (k : ℝ)) = ((16 * k : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
    exact pow_le_pow_right₀ hS (by omega)
  have hB : 0 ≤ B := by linarith
  rw [mul_pow, mul_assoc, mul_assoc, mul_assoc]
  gcongr

set_option maxHeartbeats 1600000 in

theorem sum_pairBd_mul_datBd_le : ∀ Ca : ℝ, 1 ≤ Ca → ∃ Ch Cl : ℝ, 0 ≤ Ch ∧ ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (k r m g T : ℕ) (b Del Del' Db Db' S S' : ℝ), Module.finrank ℚ K = 2 * Formalism.HermitianLatticesTheory.fDeg K → m = 2 * r + 2 → Cl ≤ m → m ^ 4 ≤ Formalism.HermitianLatticesTheory.fDeg K → m ^ 5 * Formalism.HermitianLatticesTheory.fDeg K ≤ k → Cl * ((m : ℝ) ^ 2 * Real.log b) ≤ k → Real.log (Formalism.HermitianLatticesTheory.fDeg K) ≤ Real.sqrt r → 2 ≤ b → 1 ≤ Formalism.HermitianLatticesTheory.vInv K → 2 * Formalism.HermitianLatticesTheory.vInv K ≤ b → ((k : ℝ) * b) ^ 8 ≤ g → 1 ≤ T → (T : ℝ) ≤ b ^ (Ca * m) → 1 ≤ S → 1 ≤ S' → 1 ≤ Del → 1 ≤ Del' → 1 ≤ Db → 1 ≤ Db' → Del ≤ b ^ (Ca * (m : ℝ) ^ 2 * Formalism.HermitianLatticesTheory.fDeg K) * S ^ 2 → Del' ≤ b ^ (Ca * (m : ℝ) ^ 2 * Formalism.HermitianLatticesTheory.fDeg K) * S' ^ 2 → Db ≤ (b ^ (Ca * (m : ℝ) ^ 2 * Formalism.HermitianLatticesTheory.fDeg K) * S ^ 2) ^ r → Db' ≤ (b ^ (Ca * (m : ℝ) ^ 2 * Formalism.HermitianLatticesTheory.fDeg K) * S' ^ 2) ^ r → ∑ x ∈ Finset.Icc 1 ⌊Del⌋₊, ∑ x' ∈ Finset.Icc 1 ⌊Del'⌋₊, pairBd K k g r T x x' * (datBd K k r Del Db ((T : ℝ) ^ Formalism.HermitianLatticesTheory.fDeg K) x * datBd K k r Del' Db' ((T : ℝ) ^ Formalism.HermitianLatticesTheory.fDeg K) x') ≤ (Del ^ ((k : ℝ) / 2) * (b ^ (Ch * (m : ℝ) ^ 2 * Formalism.HermitianLatticesTheory.fDeg K)) ^ (Ch * (r : ℝ) ^ 4) * S ^ (16 * (k : ℝ))) * (Del' ^ ((k : ℝ) / 2) * (b ^ (Ch * (m : ℝ) ^ 2 * Formalism.HermitianLatticesTheory.fDeg K)) ^ (Ch * (r : ℝ) ^ 4) * S' ^ (16 * (k : ℝ))) := by
  intro Ca hCa
  refine ⟨300000 * Ca, 42 * Ca, by linarith, ?_⟩
  intro K _ _ _ k r m g T b Del Del' Db Db' S S' hfin hm hCm hmf hmk hCk hlog hb hv hvb hg hT hTb hS hS' hD hD' hDb hDb'
    hDA hDA' hDbA hDbA'
  have hm42 : 42 ≤ m := by
    have : (42 : ℝ) ≤ m := by linarith
    exact_mod_cast this
  have hr : 1 ≤ r := by omega
  have hrm : r ≤ m := by omega
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hm5 : 42 ^ 5 ≤ m ^ 5 := by gcongr
  have hm4 : 42 ^ 4 ≤ m ^ 4 := by gcongr
  have hr4 : r ^ 4 ≤ m ^ 4 := by gcongr
  have hc : cf K ≤ 4 * r := by
    have hf0 : (0 : ℝ) < Formalism.HermitianLatticesTheory.fDeg K := by exact_mod_cast (by omega : 0 < Formalism.HermitianLatticesTheory.fDeg K)
    unfold cf
    rw [hfin]
    push_cast
    rw [Real.logb_mul (by norm_num) hf0.ne', Real.logb_self_eq_one (by norm_num), Real.logb]
    have h2 := Real.log_two_gt_d9
    have hs : Real.sqrt r ≤ r := by rw [Real.sqrt_le_left (by linarith)]; nlinarith
    have : Real.log (Formalism.HermitianLatticesTheory.fDeg K) / Real.log 2 ≤ 2 * r := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    linarith
  obtain ⟨f, hfdef⟩ : ∃ f, f = Formalism.HermitianLatticesTheory.fDeg K := ⟨_, rfl⟩
  rw [← hfdef] at hmf hmk hlog hDA hDA' hDbA hDbA'
  have hf1 : 1 ≤ f := by omega
  have hf1' : (1 : ℝ) ≤ f := by exact_mod_cast hf1
  have hm1' : (1 : ℝ) ≤ m := by linarith
  have hb1 : 1 ≤ b := by linarith
  have hk1 : 42 ^ 5 * f ≤ k := le_trans (by gcongr) hmk
  have hfb : (f : ℝ) ≤ b ^ (2 * r) := by
    have hs : Real.sqrt r ≤ r := by rw [Real.sqrt_le_left (by linarith)]; nlinarith
    calc (f : ℝ) = Real.exp (Real.log f) := (Real.exp_log (by linarith)).symm
      _ ≤ Real.exp (r * 1) := Real.exp_le_exp.2 (by linarith)
      _ = Real.exp 1 ^ r := Real.exp_nat_mul _ _
      _ ≤ (b ^ 2) ^ r := by
        gcongr
        have := Real.exp_one_lt_d9
        nlinarith
      _ = _ := by rw [← pow_mul]
  have hpow : ∀ n : ℕ, n ≤ m ^ 2 * f → b ^ n ≤ b ^ (Ca * (m : ℝ) ^ 2 * f) := by
    intro n hn
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le hb1
    have h1 : (n : ℝ) ≤ (m : ℝ) ^ 2 * f := by exact_mod_cast hn
    have h2 : (0 : ℝ) ≤ (m : ℝ) ^ 2 * f := by positivity
    nlinarith
  have hmf2 : m ^ 2 ≤ m ^ 2 * f := Nat.le_mul_of_pos_right _ hf1
  have hmm : 42 * m ≤ m ^ 2 := by rw [pow_two]; exact Nat.mul_le_mul_right m hm42
  have hA : 1 ≤ b ^ (Ca * (m : ℝ) ^ 2 * f) := by simpa using hpow 0 (by omega)
  have hTA : (T : ℝ) ^ f ≤ b ^ (Ca * (m : ℝ) ^ 2 * f) := by
    calc (T : ℝ) ^ f ≤ (b ^ (Ca * m)) ^ f := by gcongr
      _ = b ^ (Ca * m * f) := by rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
      _ ≤ _ := by
        apply Real.rpow_le_rpow_of_exponent_le hb1
        gcongr
        exact le_self_pow₀ hm1' (by norm_num)
  have h8 : (8 : ℝ) ^ (r + 1) ≤ b ^ (Ca * (m : ℝ) ^ 2 * f) := by
    refine le_trans ?_ (hpow (3 * (r + 1)) (by omega))
    rw [pow_mul]
    gcongr
    calc (8 : ℝ) = 2 ^ 3 := by norm_num
      _ ≤ b ^ 3 := by gcongr
  have hf2 : (f : ℝ) ^ 2 ≤ b ^ (Ca * (m : ℝ) ^ 2 * f) := by
    refine le_trans ?_ (hpow (2 * r * 2) (by omega))
    rw [pow_mul]
    gcongr
  have hsm := parith_small k f g b (Ca * (m : ℝ) ^ 2) hb (by omega) hf1 (by omega) (by linarith) hg
  have hco := le_trans (parith_const r f hr hf1 b (2 * Formalism.HermitianLatticesTheory.vInv K) (cf K) hb (by linarith) hvb hc hfb)
    (pow_le_pow_left₀ (by positivity) (hpow (r ^ 2 * f) (by gcongr)) 183)
  subst hfdef
  refine le_trans (parith_sum K k g r T hr _ S S' Del Del' Db Db' hA hS hS' hD hD' hDb hDb' hDA hDA' hDbA hDbA' hT hTA hc hv
    h8 hf2 hsm hco) ?_
  have hAB : b ^ (Ca * (m : ℝ) ^ 2 * Formalism.HermitianLatticesTheory.fDeg K) ≤ b ^ (300000 * Ca * (m : ℝ) ^ 2 * Formalism.HermitianLatticesTheory.fDeg K) := by
    apply Real.rpow_le_rpow_of_exponent_le hb1
    gcongr
    linarith
  have hkr : 300000 * r ^ 4 ≤ k := by omega
  have hD0 : 0 ≤ Del := by linarith
  have hD0' : 0 ≤ Del' := by linarith
  exact mul_le_mul
    (parith_abs k r _ _ S _ hA hAB hS (by linarith) hkr _ (by positivity))
    (parith_abs k r _ _ S' _ hA hAB hS' (by linarith) hkr _ (by positivity)) (by positivity) (by positivity)

end GlobalTheory.DegAsm
