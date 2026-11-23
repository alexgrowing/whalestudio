import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.BlockAnti
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ContinuousOnMajorantFlagLengths

noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.Cheb

theorem isClosed_GG (k r : ℕ) : IsClosed (GG k r) := by
  unfold GG UH
  exact isClosed_eq (by fun_prop) continuous_const

theorem measurableSet_len_gt (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (a : Fin (r + 1)) (T : ℝ) :
    MeasurableSet {x : Mt k r | Matrix.of x ∈ GG k r ∧ T < lA k r z (Matrix.of x) a} := by
  obtain ⟨u, hu, h⟩ := continuousOn_iff'.1 ((LenCont.lA_Sg_continuousOn k r z).1 a) (Set.Ioi T) isOpen_Ioi
  have h1 : MeasurableSet (α := Mt k r) u := IsOpen.measurableSet (α := Mt k r) hu
  have h2 : MeasurableSet (α := Mt k r) (GG k r) := IsClosed.measurableSet (α := Mt k r) (isClosed_GG k r)
  have h3 : {x : Mt k r | Matrix.of x ∈ GG k r ∧ T < lA k r z (Matrix.of x) a} = u ∩ GG k r := by
    rw [← h]
    ext x
    exact ⟨fun hx => ⟨hx.2, hx.1⟩, fun hx => ⟨hx.2, hx.1⟩⟩
  rw [h3]
  exact h1.inter h2

theorem cheb_one {X : Type*} [MeasurableSpace X] (ν : Measure X) (l : X → ℝ) (f : X → ℝ≥0∞) (E : Set X)
    (hE : MeasurableSet E) (T : ℝ) (hT : 0 < T) (hl : ∀ x ∈ E, T < l x) (n : ℕ) :
    ∫⁻ x in E, f x ∂ν ≤ ENNReal.ofReal ((T ^ n)⁻¹) * ∫⁻ x, ENNReal.ofReal (l x ^ n) * f x ∂ν := by
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine le_trans (setLIntegral_mono' hE fun x hx => ?_) (setLIntegral_le_lintegral E _)
  have hTn : 0 < T ^ n := pow_pos hT n
  rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 hTn.le)]
  refine le_mul_of_one_le_left' ?_
  rw [ENNReal.one_le_ofReal, inv_mul_eq_div, one_le_div hTn]
  exact pow_le_pow_left₀ hT.le (hl x hx).le n

theorem tail_mass_le : ∀ (k r : ℕ) {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] (z : (Fin (2 * r + k + 1) → ℂ)) (νS : Measure (Mt k r)) (Φ : Mat k r → Wp) (q : ℕ) (H₁ : ℝ), 1 ≤ H₁ → νS {x | Matrix.of x ∉ GG k r} = 0 → ContinuousOn Φ (GG k r) → MomBd z νS Φ q H₁ → ∀ i : ℕ, ∫⁻ x in {x : Mt k r | Matrix.of x ∈ GG k r ∧ (i = 0 ∨ 2 ^ i * H₁ / 2 < Sg k r z (Matrix.of x))}, (‖Φ (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2 ∂νS ≤ ENNReal.ofReal ((r + 1) * 4 ^ q * ((2 ^ i : ℝ) ^ (2 * q))⁻¹) * l2SG νS Φ := by
  intro k r Wp _ _ _ z νS Φ q H₁ hH _ _ hM i
  rcases i with _ | j
  · refine (setLIntegral_le_lintegral _ _).trans ?_
    refine le_mul_of_one_le_left' ?_
    rw [ENNReal.one_le_ofReal]
    have h1 : (1 : ℝ) ≤ 4 ^ q := one_le_pow₀ (by norm_num)
    have h2 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    simp only [pow_zero, one_pow, inv_one, mul_one]
    nlinarith
  · set T : ℝ := 2 ^ (j + 1) * H₁ / 2 with hTdef
    have hT' : T = 2 ^ j * H₁ := by rw [hTdef]; ring
    have h2j : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
    have hT1 : 1 ≤ T := by rw [hT']; nlinarith
    have hsub : {x : Mt k r | Matrix.of x ∈ GG k r ∧ (j + 1 = 0 ∨ T < Sg k r z (Matrix.of x))} ⊆
        ⋃ a : Fin (r + 1), {x : Mt k r | Matrix.of x ∈ GG k r ∧ T < lA k r z (Matrix.of x) a} := by
      rintro x ⟨hx, h | h⟩
      · omega
      · unfold Sg at h
        rw [Finset.lt_fold_max] at h
        rcases h with h | ⟨a, -, h⟩
        · linarith
        · exact Set.mem_iUnion.2 ⟨a, hx, h⟩
    refine (lintegral_mono_set hsub).trans ((lintegral_iUnion_le _ _).trans ?_)
    rw [tsum_fintype]
    have hone : ∀ a : Fin (r + 1),
        ∫⁻ x in {x : Mt k r | Matrix.of x ∈ GG k r ∧ T < lA k r z (Matrix.of x) a},
          (‖Φ (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2 ∂νS ≤
          ENNReal.ofReal (4 ^ q * ((2 ^ (j + 1) : ℝ) ^ (2 * q))⁻¹) * l2SG νS Φ := by
      intro a
      refine (cheb_one νS (fun x => lA k r z (Matrix.of x) a) _ _ (measurableSet_len_gt k r z a T) T
        (by linarith) (fun x hx => hx.2) (2 * q)).trans ?_
      refine (mul_le_mul_right (hM a) _).trans (le_of_eq ?_)
      rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
      congr 2
      have hH0 : H₁ ≠ 0 := by linarith
      have h4 : (4 : ℝ) ^ q = 2 ^ (2 * q) := by rw [pow_mul]; norm_num
      rw [hT', h4, pow_succ, mul_pow, mul_pow]
      field_simp
    refine (Finset.sum_le_sum fun a _ => hone a).trans (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc, mul_assoc ((r : ℝ) + 1),
      ENNReal.ofReal_mul (p := (r : ℝ) + 1) (by positivity)]
    congr 2
    rw [← ENNReal.ofReal_natCast]
    push_cast
    rfl

end GlobalTheory.Amp.Cheb
