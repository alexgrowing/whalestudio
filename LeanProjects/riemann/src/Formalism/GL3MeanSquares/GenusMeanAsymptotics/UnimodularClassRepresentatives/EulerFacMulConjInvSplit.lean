import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsSqAbsNormOfInert
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.CardFilterResCharLe

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

variable {K : Type} [Field K] [NumberField K] [StarRing K]

namespace IdealNormInequalities

theorem zpow_neg_lt_one {x : ℝ} (hx : 1 < x) {M : ℕ} (hM : 1 ≤ M) : x ^ (-(M : ℤ)) < 1 := by
  rw [zpow_neg, zpow_natCast]
  exact inv_lt_one_of_one_lt₀ (one_lt_pow₀ hx (by omega))

theorem zpow_neg_le {x p : ℝ} (hp : 1 ≤ p) (hx : p ≤ x) {M : ℕ} (hM : 2 ≤ M) :
    x ^ (-(M : ℤ)) ≤ (p ^ 2)⁻¹ := by
  rw [zpow_neg, zpow_natCast]
  refine inv_anti₀ (by positivity) ?_
  calc p ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ (by linarith) hx 2
    _ ≤ x ^ M := pow_le_pow_right₀ (by linarith) hM

theorem two_le_absNorm {P : Ideal (𝓞 K)} (hP : P.IsMaximal) : 2 ≤ Ideal.absNorm P :=
  (resChar_prime hP).two_le.trans (resChar_le_absNorm hP)

theorem one_lt_absNorm {P : Ideal (𝓞 K)} (hP : P.IsMaximal) : (1 : ℝ) < (Ideal.absNorm P : ℝ) := by
  exact_mod_cast (two_le_absNorm hP)

theorem one_lt_sqrt_absNorm {P : Ideal (𝓞 K)} (hP : P.IsMaximal) :
    (1 : ℝ) < Real.sqrt (Ideal.absNorm P : ℝ) := by
  rw [Real.lt_sqrt (by norm_num)]
  simpa using one_lt_absNorm hP

def smallTerm (M : ℕ) (P : Ideal (𝓞 K)) : ℝ :=
  if Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P then
    -((-1 : ℝ) ^ M * Real.sqrt (Ideal.absNorm P : ℝ) ^ (-(M : ℤ)))
  else -((Ideal.absNorm P : ℝ) ^ (-(M : ℤ)))

theorem abs_smallTerm_lt_one {P : Ideal (𝓞 K)} (hP : P.IsMaximal) {M : ℕ} (hM : 1 ≤ M) :
    |smallTerm M P| < 1 := by
  unfold smallTerm
  split_ifs with hc
  · rw [abs_neg, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_of_nonneg (zpow_nonneg (Real.sqrt_nonneg _) _)]
    exact zpow_neg_lt_one (one_lt_sqrt_absNorm hP) hM
  · rw [abs_neg, abs_of_nonneg (zpow_nonneg (Nat.cast_nonneg _) _)]
    exact zpow_neg_lt_one (one_lt_absNorm hP) hM

theorem one_add_smallTerm_pos {P : Ideal (𝓞 K)} (hP : P.IsMaximal) {M : ℕ} (hM : 1 ≤ M) :
    0 < 1 + smallTerm M P := by
  have := (abs_lt.mp (abs_smallTerm_lt_one hP hM)).1
  linarith

theorem abs_smallTerm_le (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {P : Ideal (𝓞 K)} (hP : P.IsMaximal) {M : ℕ}
    (hM : 2 ≤ M) : |smallTerm M P| ≤ ((resChar P : ℝ) ^ 2)⁻¹ := by
  have hp1 : (1 : ℝ) ≤ (resChar P : ℝ) := by exact_mod_cast (resChar_prime hP).one_lt.le
  unfold smallTerm
  split_ifs with hc
  · rw [abs_neg, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_of_nonneg (zpow_nonneg (Real.sqrt_nonneg _) _)]
    obtain ⟨q, hq⟩ := exists_sq_absNorm_of_inert hK hP hc
    have hs : Real.sqrt (Ideal.absNorm P : ℝ) = q := by
      rw [hq]; push_cast; exact Real.sqrt_sq (Nat.cast_nonneg q)
    rw [hs]
    exact zpow_neg_le hp1 (by exact_mod_cast resChar_le_of_sq hP hq) hM
  · rw [abs_neg, abs_of_nonneg (zpow_nonneg (Nat.cast_nonneg _) _)]
    exact zpow_neg_le hp1 (by exact_mod_cast resChar_le_absNorm hP) hM

theorem eulerFac_eq (M : ℕ) (P : Ideal (𝓞 K)) :
    Formalism.HermitianLatticesTheory.eulerFac K M P = if Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P then (1 + smallTerm M P)⁻¹
      else (1 + smallTerm M P) ^ (-(1 : ℝ) / 2) := by
  unfold Formalism.HermitianLatticesTheory.eulerFac smallTerm
  split_ifs with hc <;> simp only [← sub_eq_add_neg]

theorem abs_log_eulerFac_le {P : Ideal (𝓞 K)} (hP : P.IsMaximal) {M : ℕ} (hM : 1 ≤ M) :
    |Real.log (Formalism.HermitianLatticesTheory.eulerFac K M P)| ≤ |Real.log (1 + smallTerm M P)| := by
  rw [eulerFac_eq]
  split_ifs with hc
  · rw [Real.log_inv, abs_neg]
  · rw [Real.log_rpow (one_add_smallTerm_pos hP hM), abs_mul]
    have : |(-(1 : ℝ) / 2)| = 1 / 2 := by rw [abs_of_nonpos (by norm_num)]; norm_num
    rw [this]
    nlinarith [abs_nonneg (Real.log (1 + smallTerm M P))]

theorem summable_log_eulerFac (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {M : ℕ} (hM : 2 ≤ M) :
    Summable (fun P : {P : Ideal (𝓞 K) // P.IsMaximal} =>
      Real.log (Formalism.HermitianLatticesTheory.eulerFac K M P.1)) := by
  have h1 : Summable (fun P : {P : Ideal (𝓞 K) // P.IsMaximal} => smallTerm M P.1) :=
    Summable.of_norm_bounded summable_resChar_sq (fun P => abs_smallTerm_le hK P.2 hM)
  have h2 := (Real.summable_log_one_add_of_summable h1).abs
  exact Summable.of_norm_bounded h2 (fun P => abs_log_eulerFac_le P.2 (by omega))

end IdealNormInequalities

open IdealNormInequalities

theorem eulerFac_pos (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {P : Ideal (𝓞 K)} (hP : P.IsMaximal) (M : ℕ)
    (hM : 1 ≤ M) : 0 < Formalism.HermitianLatticesTheory.eulerFac K M P := by
  rw [eulerFac_eq]
  split_ifs with hc
  · exact inv_pos.mpr (one_add_smallTerm_pos hP hM)
  · exact Real.rpow_pos_of_pos (one_add_smallTerm_pos hP hM) _

theorem eulerFac_inv_inert (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {P : Ideal (𝓞 K)} (hP : P.IsMaximal)
    (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P) (M : ℕ) :
    (Formalism.HermitianLatticesTheory.eulerFac K M P)⁻¹ =
      1 - (-1 : ℝ) ^ M * Real.sqrt (Ideal.absNorm P : ℝ) ^ (-(M : ℤ)) := by
  unfold Formalism.HermitianLatticesTheory.eulerFac
  rw [if_pos hc, inv_inv]

theorem eulerFac_mul_conj_inv_split (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {P : Ideal (𝓞 K)}
    (hP : P.IsMaximal) (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P ≠ P) (M : ℕ) (hM : 1 ≤ M) :
    (Formalism.HermitianLatticesTheory.eulerFac K M P * Formalism.HermitianLatticesTheory.eulerFac K M (Formalism.HermitianLatticesTheory.conjIdeal (K := K) P))⁻¹ =
      1 - (Ideal.absNorm P : ℝ) ^ (-(M : ℤ)) := by
  have hc' : Formalism.HermitianLatticesTheory.conjIdeal (K := K) (Formalism.HermitianLatticesTheory.conjIdeal (K := K) P) ≠
      Formalism.HermitianLatticesTheory.conjIdeal (K := K) P := by
    rw [conjIdeal_conjIdeal hK]; exact hc.symm
  have hx : 0 < 1 - (Ideal.absNorm P : ℝ) ^ (-(M : ℤ)) :=
    sub_pos.mpr (zpow_neg_lt_one (one_lt_absNorm hP) hM)
  unfold Formalism.HermitianLatticesTheory.eulerFac
  rw [if_neg hc, if_neg hc', absNorm_conjIdeal hK, ← Real.rpow_add hx]
  norm_num [Real.rpow_neg_one]

theorem multipliable_eulerFac (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (M : ℕ) (hM : 2 ≤ M) :
    Multipliable (fun P : {P : Ideal (𝓞 K) // P.IsMaximal} => Formalism.HermitianLatticesTheory.eulerFac K M P.1) :=
  Real.multipliable_of_summable_log (fun P => eulerFac_pos hK P.2 M (by omega))
    (summable_log_eulerFac hK hM)

theorem lValEta_pos (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (M : ℕ) (hM : 2 ≤ M) :
    0 < Formalism.HermitianLatticesTheory.lValEta K M := by
  unfold Formalism.HermitianLatticesTheory.lValEta
  rw [← Real.rexp_tsum_eq_tprod (fun P => eulerFac_pos hK P.2 M (by omega))
    (summable_log_eulerFac hK hM)]
  exact Real.exp_pos _

end Formalism.HermitianLattices.Ext.L3
