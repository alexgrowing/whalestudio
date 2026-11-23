import Mathlib
import Formalism.GL3MeanSquares.PrimeCountAsymptoticInProgressions
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Formalism.CyclotomicNorms.StatementI
import Development.AbelianVarietyTheory.Definitions.Foundations.RayPrimes
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsExcRat
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.PageThm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsJacobiSymEqNegOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CardPrimesResidueGeRpow
open Finset ArithmeticFunction NumberField IsDedekindDomain Filter Topology GlobalTheory.Mem.An Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab
open scoped nonZeroDivisors

namespace GlobalTheory.Mem.An.JacobiMean

open Formalism.HermitianLattices.GL2PrimeSums (Li Emain PP)

theorem inv_log_integrable {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun t : ℝ => 1 / Real.log t) MeasureTheory.volume a b := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le hab]
  intro t ht
  have h1 : 1 < t := lt_of_lt_of_le ha ht.1
  exact (continuousAt_const.div (Real.continuousAt_log (by linarith)) (Real.log_pos h1).ne').continuousWithinAt

theorem integral_inv_log_le {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    ∫ t in a..b, 1 / Real.log t ≤ (b - a) / Real.log a := by
  have h := intervalIntegral.integral_mono_on hab (inv_log_integrable ha hab)
    (intervalIntegrable_const (c := 1 / Real.log a)) (fun t ht =>
      one_div_le_one_div_of_le (Real.log_pos ha) (Real.log_le_log (by linarith) ht.1))
  simpa [div_eq_mul_inv] using h

theorem le_integral_inv_log {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    (b - a) / Real.log b ≤ ∫ t in a..b, 1 / Real.log t := by
  have h := intervalIntegral.integral_mono_on hab
    (intervalIntegrable_const (c := 1 / Real.log b)) (inv_log_integrable ha hab) (fun t ht =>
      one_div_le_one_div_of_le (Real.log_pos (lt_of_lt_of_le ha ht.1))
        (Real.log_le_log (by linarith [ht.1]) ht.2))
  simpa [div_eq_mul_inv] using h

theorem li_le {Y : ℝ} (hY : 4 ≤ Y) : Li Y ≤ 6 * Y / Real.log Y := by
  set s := Real.sqrt Y with hs
  have hs2 : 2 ≤ s := by
    rw [hs]; apply Real.le_sqrt_of_sq_le; norm_num; linarith
  have hss : s * s = Y := Real.mul_self_sqrt (by linarith)
  have hsY : s ≤ Y := by nlinarith
  have hs0 : 0 < s := by linarith
  have hlogY : Real.log Y = 2 * Real.log s := by
    rw [← hss, Real.log_mul hs0.ne' hs0.ne']; ring
  have hls : 0 < Real.log s := Real.log_pos (by linarith)
  have b1 := integral_inv_log_le (a := 2) (b := s) (by norm_num) hs2
  have b2 := integral_inv_log_le (a := s) (b := Y) (by linarith) hsY
  have b3 := intervalIntegral.integral_add_adjacent_intervals
    (inv_log_integrable (a := 2) (b := s) (by norm_num) hs2)
    (inv_log_integrable (a := s) (b := Y) (by linarith) hsY)
  have hr : Real.log s ≤ s - 1 := Real.log_le_sub_one_of_pos hs0
  have h2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have c1 : (s - 2) / Real.log 2 ≤ 2 * s := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have c2 : (Y - s) / Real.log s ≤ Y / Real.log s :=
    div_le_div_of_nonneg_right (by linarith) hls.le
  have c3 : 2 * s ≤ 2 * (Y / Real.log s) := by
    have : s ≤ Y / Real.log s := by rw [le_div_iff₀ hls]; nlinarith
    linarith
  have e : 6 * Y / Real.log Y = 3 * (Y / Real.log s) := by
    rw [hlogY]; field_simp; ring
  unfold Formalism.HermitianLattices.GL2PrimeSums.Li
  rw [e]; linarith

theorem li_rpow_le {X β : ℝ} (hX : 16 ≤ X) (hβ : 1 / 2 ≤ β) :
    0 ≤ Li (X ^ β) ∧ 0 ≤ Li X ∧ Li (X ^ β) ≤ 24 * X ^ (β - 1) * Li X := by
  have hX0 : 0 < X := by linarith
  have hl : 0 < Real.log X := Real.log_pos (by linarith)
  have h4 : 4 ≤ X ^ β := by
    have h3 : X ^ (1 / 2 : ℝ) ≤ X ^ β := Real.rpow_le_rpow_of_exponent_le (by linarith) hβ
    have e : (4 : ℝ) ≤ X ^ (1 / 2 : ℝ) := by
      rw [← Real.sqrt_eq_rpow]; apply Real.le_sqrt_of_sq_le; linarith
    linarith
  have a1 := le_integral_inv_log (a := 2) (b := X ^ β) (by norm_num) (by linarith)
  have a2 := le_integral_inv_log (a := 2) (b := X) (by norm_num) (by linarith)
  have hl' : 0 < Real.log (X ^ β) := Real.log_pos (by linarith)
  have a3 : X / Real.log X ≤ 2 * Li X := by
    have : X / Real.log X ≤ 2 * ((X - 2) / Real.log X) := by
      rw [← mul_div_assoc]; exact div_le_div_of_nonneg_right (by linarith) hl.le
    unfold Formalism.HermitianLattices.GL2PrimeSums.Li; linarith
  have a4 : 0 ≤ X / Real.log X := by positivity
  refine ⟨le_trans (div_nonneg (by linarith) hl'.le) a1, by linarith, (li_le h4).trans ?_⟩
  have hp : 0 < X ^ (β - 1) := Real.rpow_pos_of_pos hX0 _
  have e : X ^ β = X ^ (β - 1) * X := by rw [Real.rpow_sub_one hX0.ne']; field_simp
  calc 6 * X ^ β / Real.log (X ^ β) ≤ 6 * X ^ β / (Real.log X / 2) := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        rw [Real.log_rpow hX0]; nlinarith
    _ = 12 * X ^ (β - 1) * (X / Real.log X) := by rw [e]; field_simp; ring
    _ ≤ 12 * X ^ (β - 1) * (2 * Li X) := by gcongr
    _ = _ := by ring

theorem finite_core (F : Finset ℕ) (lam N θ : ℕ → ℝ) (φ L L' ρ δ : ℝ) (hφ : 0 < φ) (hρ0 : 0 < ρ) (hρ : ρ ≤ 1 / 2)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 2) (hL : 0 ≤ L) (hL' : 0 ≤ L') (hl : ∀ b ∈ F, |lam b| ≤ 1) (hθ : ∀ b ∈ F, |θ b| ≤ 1)
    (hs : ∑ b ∈ F, lam b = 0) (hN : ∀ b ∈ F, |φ * N b - (L - θ b * L')| ≤ ρ * (L - θ b * L'))
    (hc : ∑ b ∈ F, lam b * θ b = 0 ∨ L' ≤ δ * L) :
    |∑ b ∈ F, lam b * N b| ≤ (2 * ρ + 4 * δ) * ∑ b ∈ F, N b := by
  have hE : ∀ b ∈ F, 0 ≤ L - θ b * L' := fun b hb =>
    (mul_nonneg_iff_of_pos_left hρ0).1 (le_trans (abs_nonneg _) (hN b hb))
  have hE2 : ∀ b ∈ F, L - θ b * L' ≤ 2 * (φ * N b) := fun b hb => by
    have h1 := (abs_le.1 (hN b hb)).1
    have h2 := hE b hb
    nlinarith
  have hS : ∑ b ∈ F, (L - θ b * L') ≤ 2 * (φ * ∑ b ∈ F, N b) := by
    rw [Finset.mul_sum, Finset.mul_sum]; exact Finset.sum_le_sum hE2
  have hS0 : 0 ≤ ∑ b ∈ F, (L - θ b * L') := Finset.sum_nonneg hE
  have e1 : φ * ∑ b ∈ F, lam b * N b = ∑ b ∈ F, lam b * (φ * N b - (L - θ b * L')) - L' * ∑ b ∈ F, lam b * θ b := by
    have : ∑ b ∈ F, lam b * L = 0 := by rw [← Finset.sum_mul, hs, zero_mul]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← add_zero (∑ b ∈ F, (_ - _)), ← this,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun b _ => by ring
  have h1 : |∑ b ∈ F, lam b * (φ * N b - (L - θ b * L'))| ≤ ρ * ∑ b ∈ F, (L - θ b * L') := by
    rw [Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b hb => ?_)
    rw [abs_mul]
    exact (mul_le_of_le_one_left (abs_nonneg _) (hl b hb)).trans (hN b hb)
  have h2 : |L' * ∑ b ∈ F, lam b * θ b| ≤ 2 * δ * ∑ b ∈ F, (L - θ b * L') := by
    rcases hc with hc | hc
    · rw [hc]; simp only [mul_zero, abs_zero]; positivity
    · rw [Finset.mul_sum, Finset.mul_sum]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b hb => ?_)
      rw [abs_mul, abs_mul, abs_of_nonneg hL']
      have k1 : |lam b| * |θ b| ≤ 1 := mul_le_one₀ (hl b hb) (abs_nonneg _) (hθ b hb)
      have k2 : θ b * L' ≤ L' := mul_le_of_le_one_left hL' (abs_le.1 (hθ b hb)).2
      have k3 : L / 2 ≤ L - θ b * L' := by nlinarith
      calc L' * (|lam b| * |θ b|) ≤ L' := mul_le_of_le_one_right hL' k1
        _ ≤ 2 * δ * (L / 2) := by linarith
        _ ≤ _ := by gcongr
  have h3 : φ * |∑ b ∈ F, lam b * N b| ≤ φ * ((2 * ρ + 4 * δ) * ∑ b ∈ F, N b) := by
    rw [← abs_of_pos hφ, ← abs_mul, abs_of_pos hφ, e1]
    refine (abs_sub _ _).trans ?_
    have : (ρ + 2 * δ) * ∑ b ∈ F, (L - θ b * L') ≤ (ρ + 2 * δ) * (2 * (φ * ∑ b ∈ F, N b)) := by gcongr
    nlinarith
  exact le_of_mul_le_mul_left h3 hφ

def cls (m₀ s a₀ : ℕ) : Finset ℕ := (range (m₀ * s)).filter (fun b => b ≡ a₀ [MOD m₀] ∧ Nat.Coprime b s)

theorem jacobi_mod (m₀ s b : ℕ) : jacobiSym ((b % (m₀ * s) : ℕ) : ℤ) s = jacobiSym (b : ℤ) s := by
  apply jacobiSym.mod_left'
  exact Int.natCast_modEq_iff.mpr ((Nat.mod_modEq b (m₀ * s)).of_mul_left m₀)

theorem mod_mem_cls {m₀ s a₀ p : ℕ} (hM : 0 < m₀ * s) (h1 : p ≡ a₀ [MOD m₀]) (h2 : Nat.Coprime p s) :
    p % (m₀ * s) ∈ cls m₀ s a₀ := by
  unfold cls
  rw [Finset.mem_filter, Finset.mem_range]
  refine ⟨Nat.mod_lt _ hM, ((Nat.mod_modEq p (m₀ * s)).of_mul_right s).trans h1, ?_⟩
  have := ((Nat.mod_modEq p (m₀ * s)).of_mul_left m₀).gcd_eq
  unfold Nat.Coprime at h2 ⊢
  rw [this, h2]

theorem jacobi_eq_zero {s b : ℕ} (hs : 0 < s) (h : ¬ Nat.Coprime b s) : jacobiSym (b : ℤ) s = 0 := by
  haveI : NeZero s := ⟨hs.ne'⟩
  exact jacobiSym.eq_zero_iff_not_coprime.mpr (by simpa [Int.gcd_natCast_natCast] using h)

theorem abs_jacobi_le (b : ℤ) (s : ℕ) : |(jacobiSym b s : ℝ)| ≤ 1 := by
  rcases jacobiSym.trichotomy b s with h | h | h <;> simp [h]

theorem sum_primes_fiber (m₀ s a₀ n : ℕ) (hm : 0 < m₀) (hs : 0 < s) :
    ∑ p ∈ (Icc 1 n).filter (fun p => p.Prime ∧ p ≡ a₀ [MOD m₀]), (jacobiSym (p : ℤ) s : ℝ) =
      ∑ b ∈ cls m₀ s a₀, (jacobiSym (b : ℤ) s : ℝ) *
        (((Icc 1 n).filter (fun p => p.Prime ∧ p ≡ b [MOD m₀ * s])).card : ℝ) ∧
    ∑ b ∈ cls m₀ s a₀, (((Icc 1 n).filter (fun p => p.Prime ∧ p ≡ b [MOD m₀ * s])).card : ℝ) ≤
      (((Icc 1 n).filter (fun p => p.Prime ∧ p ≡ a₀ [MOD m₀])).card : ℝ) := by
  have hM : 0 < m₀ * s := Nat.mul_pos hm hs
  set A := (Icc 1 n).filter (fun p => p.Prime ∧ p ≡ a₀ [MOD m₀]) with hA
  have hmap : ∀ p ∈ A.filter (fun p => Nat.Coprime p s), p % (m₀ * s) ∈ cls m₀ s a₀ := by
    intro p hp
    rw [Finset.mem_filter, hA, Finset.mem_filter] at hp
    exact mod_mem_cls hM hp.1.2.2 hp.2
  have hfib : ∀ b ∈ cls m₀ s a₀, (A.filter (fun p => Nat.Coprime p s)).filter (fun p => p % (m₀ * s) = b) =
      (Icc 1 n).filter (fun p => p.Prime ∧ p ≡ b [MOD m₀ * s]) := by
    intro b hb
    unfold cls at hb
    rw [Finset.mem_filter, Finset.mem_range] at hb
    ext p
    simp only [hA, Finset.mem_filter]
    constructor
    · rintro ⟨⟨⟨h1, h2, -⟩, -⟩, h3⟩
      exact ⟨h1, h2, h3 ▸ (Nat.mod_modEq p _).symm⟩
    · rintro ⟨h1, h2, h3⟩
      refine ⟨⟨⟨h1, h2, (h3.of_mul_right s).trans hb.2.1⟩, ?_⟩, ?_⟩
      · have := (h3.of_mul_left m₀).gcd_eq
        unfold Nat.Coprime
        rw [this]; exact hb.2.2
      · unfold Nat.ModEq at h3
        rw [h3, Nat.mod_eq_of_lt hb.1]
  constructor
  · have e : ∑ p ∈ A, (jacobiSym (p : ℤ) s : ℝ) =
        ∑ p ∈ A.filter (fun p => Nat.Coprime p s), (jacobiSym (p : ℤ) s : ℝ) := by
      rw [Finset.sum_filter (fun p => Nat.Coprime p s)]
      refine Finset.sum_congr rfl fun p _ => ?_
      split_ifs with h
      · rfl
      · rw [jacobi_eq_zero hs h]; simp
    rw [e, ← Finset.sum_fiberwise_of_maps_to hmap]
    refine Finset.sum_congr rfl fun b hb => ?_
    rw [← hfib b hb, mul_comm (jacobiSym (b : ℤ) s : ℝ), ← nsmul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [← (Finset.mem_filter.1 hp).2, jacobi_mod]
  · have h := Finset.card_eq_sum_card_fiberwise (f := fun p => p % (m₀ * s)) hmap
    rw [Finset.sum_congr rfl (fun b hb => congrArg Finset.card (hfib b hb))] at h
    rw [← Nat.cast_sum, ← h]
    exact_mod_cast Finset.card_filter_le _ _

theorem sum_cls_jacobi {m₀ s a₀ : ℕ} (hm : 0 < m₀) (h1 : 1 < s) (ho : Odd s) (hsq : Squarefree s)
    (hc : Nat.Coprime s m₀) : ∑ b ∈ cls m₀ s a₀, (jacobiSym (b : ℤ) s : ℝ) = 0 := by
  have h := GlobalTheory.JacobiClassSum.lamSumZero m₀ s a₀ hm h1 ho hsq hc
  unfold cls
  have h' := congrArg (Int.cast : ℤ → ℝ) h
  rw [Int.cast_sum, Int.cast_zero] at h'
  refine Eq.trans ?_ h'
  rw [← Finset.filter_filter, Finset.sum_filter (fun p => Nat.Coprime p s)]
  refine Finset.sum_congr rfl fun p _ => ?_
  split_ifs with h
  · rfl
  · rw [jacobi_eq_zero (by omega) h]; simp

theorem jacobi_mul_char_eq_one {m₀ s a₀ : ℕ} (hM : 0 < m₀ * s) (χ : DirichletCharacter ℂ (m₀ * s))
    (h : ∑ b ∈ cls m₀ s a₀, (jacobiSym (b : ℤ) s : ℂ) * χ (b : ZMod (m₀ * s)) ≠ 0)
    {u : ℕ} (hu1 : u ≡ 1 [MOD m₀]) (hu2 : Nat.Coprime u s) :
    (jacobiSym (u : ℤ) s : ℂ) * χ (u : ZMod (m₀ * s)) = 1 := by
  have hum : Nat.Coprime u (m₀ * s) := by
    refine Nat.Coprime.mul_right ?_ hu2
    unfold Nat.Coprime
    rw [hu1.gcd_eq]; simp
  have hinj : Set.InjOn (fun b => (u * b) % (m₀ * s)) (cls m₀ s a₀ : Set ℕ) := by
    intro b hb b' hb' e
    have hb1 := Finset.mem_range.1 (Finset.mem_filter.1 (Finset.mem_coe.1 hb)).1
    have hb2 := Finset.mem_range.1 (Finset.mem_filter.1 (Finset.mem_coe.1 hb')).1
    exact Nat.ModEq.eq_of_lt_of_lt (Nat.ModEq.cancel_left_of_coprime hum.symm e) hb1 hb2
  have himg : (cls m₀ s a₀).image (fun b => (u * b) % (m₀ * s)) = cls m₀ s a₀ := by
    apply Finset.eq_of_subset_of_card_le
    · intro c hc
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hc
      have hb' := (Finset.mem_filter.1 hb).2
      exact mod_mem_cls hM (by simpa using hu1.mul hb'.1) (Nat.Coprime.mul_left hu2 hb'.2)
    · rw [Finset.card_image_of_injOn hinj]
  have e : ∑ b ∈ cls m₀ s a₀, (jacobiSym (b : ℤ) s : ℂ) * χ (b : ZMod (m₀ * s)) =
      ((jacobiSym (u : ℤ) s : ℂ) * χ (u : ZMod (m₀ * s))) *
        ∑ b ∈ cls m₀ s a₀, (jacobiSym (b : ℤ) s : ℂ) * χ (b : ZMod (m₀ * s)) := by
    conv_lhs => rw [← himg, Finset.sum_image hinj]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [jacobi_mod, ZMod.natCast_mod, Nat.cast_mul, Nat.cast_mul, jacobiSym.mul_left, map_mul]
    push_cast; ring
  exact mul_right_cancel₀ h (by rw [one_mul]; exact e.symm)

theorem exists_sep_of_prime {m₀ s s' p : ℕ} (hp : p.Prime) (hps : p ∣ s) (hps' : ¬ p ∣ s') (ho : Odd s)
    (hsq : Squarefree s) (hc : Nat.Coprime s m₀) :
    ∃ u : ℕ, u ≡ 1 [MOD m₀] ∧ Nat.Coprime u s ∧ Nat.Coprime u s' ∧ jacobiSym (u : ℤ) s = -1 ∧ jacobiSym (u : ℤ) s' = 1 := by
  obtain ⟨t, rfl⟩ := hps
  have hpt : Nat.Coprime p t := Nat.coprime_of_squarefree_mul hsq
  obtain ⟨c, hc1⟩ := GlobalTheory.JacobiClassSum.exists_jacobiSym_eq_neg_one hp.one_lt (Nat.odd_mul.1 ho).1 hp.squarefree
  have hcop : Nat.Coprime p (m₀ * t * s') :=
    Nat.Coprime.mul_right (Nat.Coprime.mul_right (Nat.Coprime.coprime_mul_right hc) hpt)
      ((Nat.Prime.coprime_iff_not_dvd hp).2 hps')
  obtain ⟨u, hu1, hu2⟩ := Nat.chineseRemainder hcop c 1
  have one : ∀ d, d ∣ m₀ * t * s' → jacobiSym (u : ℤ) d = 1 := fun d hd => by
    rw [jacobiSym.mod_left' (a₂ := 1) (by exact_mod_cast (Int.natCast_modEq_iff.mpr (hu2.of_dvd hd))),
      jacobiSym.one_left]
  have hup : jacobiSym (u : ℤ) p = -1 := by
    rw [jacobiSym.mod_left' (a₂ := c) (Int.natCast_modEq_iff.mpr hu1), hc1]
  have ht : t ≠ 0 := by rintro rfl; simp at ho
  have e : jacobiSym (u : ℤ) (p * t) = -1 := by
    rw [jacobiSym.mul_right' _ hp.ne_zero ht, hup, one t ⟨m₀ * s', by ring⟩]; norm_num
  refine ⟨u, hu2.of_dvd ⟨t * s', by ring⟩, ?_, ?_, e, one s' (Dvd.intro_left _ rfl)⟩
  · by_contra h
    rw [jacobi_eq_zero (Nat.mul_pos hp.pos (Nat.pos_of_ne_zero ht)) h] at e
    norm_num at e
  · unfold Nat.Coprime
    rw [(hu2.of_dvd (Dvd.intro_left _ rfl)).gcd_eq]; simp

theorem exists_sep {m₀ s s' : ℕ} (ho : Odd s) (hsq : Squarefree s) (hc : Nat.Coprime s m₀)
    (ho' : Odd s') (hsq' : Squarefree s') (hc' : Nat.Coprime s' m₀) (hne : s ≠ s') :
    ∃ u : ℕ, u ≡ 1 [MOD m₀] ∧ Nat.Coprime u s ∧ Nat.Coprime u s' ∧
      jacobiSym (u : ℤ) s * jacobiSym (u : ℤ) s' = -1 := by
  by_cases h : ∀ p : ℕ, p.Prime → (p ∣ s ↔ p ∣ s')
  · exact absurd ((Nat.Squarefree.ext_iff hsq hsq').2 h) hne
  · push Not at h
    obtain ⟨p, hp, h | h⟩ := h
    · obtain ⟨u, a, b, c, d, e⟩ := exists_sep_of_prime hp h.1 h.2 ho hsq hc
      exact ⟨u, a, b, c, by rw [d, e]; norm_num⟩
    · obtain ⟨u, a, b, c, d, e⟩ := exists_sep_of_prime hp h.2 h.1 ho' hsq' hc'
      exact ⟨u, a, c, b, by rw [d, e]; norm_num⟩

theorem primitive_sq {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M) (h : χ ^ 2 = 1) :
    χ.primitiveCharacter ^ 2 = 1 := by
  apply DirichletCharacter.changeLevel_injective χ.conductor_dvd_level
  rw [map_pow, DirichletCharacter.changeLevel_primitiveCharacter, h, map_one]

theorem primitive_apply {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M) {u : ℕ} (h : Nat.Coprime u M) :
    χ.primitiveCharacter (u : ZMod χ.conductor) = χ (u : ZMod M) := by
  have := χ.primitiveCharacter_apply_of_isCoprime (a := (u : ℤ)) (Nat.isCoprime_iff_coprime.2 h)
  simpa using this

theorem sq_apply {M : ℕ} (χ : DirichletCharacter ℂ M) (h : χ ^ 2 = 1) {u : ℕ} (hu : Nat.Coprime u M) :
    χ (u : ZMod M) ^ 2 = 1 := by
  have h1 : (χ ^ 2) (u : ZMod M) = 1 := by
    rw [h]; exact MulChar.one_apply ((ZMod.isUnit_iff_coprime u M).2 hu)
  rwa [MulChar.pow_apply' χ (by norm_num)] at h1

def Exc (m₀ a₀ : ℕ) (lo : ℝ) (s : ℕ) : Prop :=
  ∃ (_ : NeZero (m₀ * s)) (χ : DirichletCharacter ℂ (m₀ * s)) (β : ℝ), IsExcRat χ β ∧ lo < β ∧
    ∑ b ∈ cls m₀ s a₀, (jacobiSym (b : ℤ) s : ℂ) * χ (b : ZMod (m₀ * s)) ≠ 0

theorem exc_unique {m₀ a₀ s s' : ℕ} {lo Q : ℝ}
    (hP : ∀ (q₁ q₂ : ℕ) [NeZero q₁] [NeZero q₂]
      (χ₁ : DirichletCharacter ℂ q₁) (χ₂ : DirichletCharacter ℂ q₂) (β₁ β₂ : ℝ),
      χ₁.IsPrimitive → χ₂.IsPrimitive → χ₁ ^ 2 = 1 → χ₂ ^ 2 = 1 → (q₁ : ℝ) ≤ Q → (q₂ : ℝ) ≤ Q →
      lo < β₁ → β₁ < 1 → lo < β₂ → β₂ < 1 →
      DirichletCharacter.LFunction χ₁ β₁ = 0 → DirichletCharacter.LFunction χ₂ β₂ = 0 →
      q₁ = q₂ ∧ ∀ n : ℕ, χ₁ (n : ZMod q₁) = χ₂ (n : ZMod q₂))
    (ho : Odd s) (hsq : Squarefree s) (hc : Nat.Coprime s m₀) (hQ : ((m₀ * s : ℕ) : ℝ) ≤ Q)
    (ho' : Odd s') (hsq' : Squarefree s') (hc' : Nat.Coprime s' m₀) (hQ' : ((m₀ * s' : ℕ) : ℝ) ≤ Q)
    (h : Exc m₀ a₀ lo s) (h' : Exc m₀ a₀ lo s') : s = s' := by
  by_contra hne
  obtain ⟨u, hu, hus, hus', hJ⟩ := exists_sep ho hsq hc ho' hsq' hc' hne
  obtain ⟨i, χ, β, hχ, hlo, hsum⟩ := h
  obtain ⟨i', χ', β', hχ', hlo', hsum'⟩ := h'
  have hM := NeZero.pos (m₀ * s)
  have hM' := NeZero.pos (m₀ * s')
  haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  haveI : NeZero χ'.conductor := ⟨χ'.conductor_ne_zero⟩
  have key := (hP χ.conductor χ'.conductor χ.primitiveCharacter χ'.primitiveCharacter β β'
    χ.primitiveCharacter_isPrimitive χ'.primitiveCharacter_isPrimitive (primitive_sq χ hχ.1) (primitive_sq χ' hχ'.1)
    (le_trans (by exact_mod_cast Nat.le_of_dvd hM χ.conductor_dvd_level) hQ)
    (le_trans (by exact_mod_cast Nat.le_of_dvd hM' χ'.conductor_dvd_level) hQ')
    hlo hχ.2.2.1 hlo' hχ'.2.2.1 hχ.2.2.2 hχ'.2.2.2).2 u
  have hum : Nat.Coprime u m₀ := by
    unfold Nat.Coprime
    rw [hu.gcd_eq]; simp
  rw [primitive_apply χ (hum.mul_right hus), primitive_apply χ' (hum.mul_right hus')] at key
  have e1 := jacobi_mul_char_eq_one hM χ hsum hu hus
  have e2 := jacobi_mul_char_eq_one hM' χ' hsum' hu hus'
  have e3 := sq_apply χ hχ.1 (hum.mul_right hus)
  have e4 : (jacobiSym (u : ℤ) s : ℂ) * (jacobiSym (u : ℤ) s' : ℂ) = -1 := by exact_mod_cast hJ
  rw [← key] at e2
  have : (2 : ℂ) = 0 := by
    linear_combination (-(jacobiSym (u : ℤ) s' : ℂ) * χ (u : ZMod (m₀ * s))) * e1 - e2 +
      χ (u : ZMod (m₀ * s)) ^ 2 * e4 - e3
  norm_num at this

theorem twisted_sum_le {m₀ a₀ s : ℕ} [NeZero (m₀ * s)] {lo X ρ δ : ℝ} (hm : 8 ≤ m₀) (ha : Nat.Coprime a₀ m₀)
    (h1 : 1 < s) (ho : Odd s) (hsq : Squarefree s) (hc : Nat.Coprime s m₀)
    (hρ0 : 0 < ρ) (hρ : ρ ≤ 1 / 2) (hδ : δ ≤ 1 / 2) (hX : 16 ≤ X) (hlo : 24 * X ^ (lo - 1) ≤ δ)
    (hT : ∀ (b : ℕ) (θ : ℤ) (β : ℝ), Nat.Coprime b (m₀ * s) →
      ((θ = 0 ∧ ∀ (χ : DirichletCharacter ℂ (m₀ * s)) (β' : ℝ), ¬ IsExcRat χ β') ∨
        ∃ χ : DirichletCharacter ℂ (m₀ * s), IsExcRat χ β ∧ χ (b : ZMod (m₀ * s)) = (θ : ℂ)) →
      |((m₀ * s).totient : ℝ) * (((Icc 1 ⌊X⌋₊).filter (fun p => p.Prime ∧ p ≡ b [MOD m₀ * s])).card : ℝ) - Emain θ β X| ≤
        ρ * Emain θ β X)
    (hE : ¬ Exc m₀ a₀ lo s) :
    |∑ p ∈ (Icc 1 ⌊X⌋₊).filter (fun p => p.Prime ∧ p ≡ a₀ [MOD m₀]), (jacobiSym (p : ℤ) s : ℝ)| ≤
      (2 * ρ + 4 * δ) * (((Icc 1 ⌊X⌋₊).filter (fun p => p.Prime ∧ p ≡ a₀ [MOD m₀])).card : ℝ) := by
  classical
  have hM := NeZero.pos (m₀ * s)
  obtain ⟨k1, k2⟩ := sum_primes_fiber m₀ s a₀ ⌊X⌋₊ (by omega) (by omega)
  have hδ0 : 0 ≤ δ := le_trans (by positivity) hlo
  have hφ : (0 : ℝ) < (m₀ * s).totient := by exact_mod_cast Nat.totient_pos.2 hM
  have hcop : ∀ b ∈ cls m₀ s a₀, Nat.Coprime b (m₀ * s) := fun b hb => by
    have hb' := (Finset.mem_filter.1 hb).2
    refine Nat.Coprime.mul_right ?_ hb'.2
    unfold Nat.Coprime
    rw [hb'.1.gcd_eq]; exact ha
  have hs0 := sum_cls_jacobi (a₀ := a₀) (by omega : 0 < m₀) h1 ho hsq hc
  rw [k1]
  refine le_trans ?_ (mul_le_mul_of_nonneg_left k2 (by positivity))
  by_cases hex : ∃ (χ : DirichletCharacter ℂ (m₀ * s)) (β : ℝ), IsExcRat χ β
  · obtain ⟨χ, β, hχ⟩ := hex
    have hβ : 1 / 2 ≤ β := by
      have h2 : (2 : ℝ) ≤ ((m₀ * s : ℕ) : ℝ) := by
        have : 2 ≤ m₀ * s := by nlinarith
        exact_mod_cast this
      have h3 : Real.log 2 ≤ Real.log ((m₀ * s : ℕ) : ℝ) := Real.log_le_log (by norm_num) h2
      have h4 := Real.log_two_gt_d9
      have h5 : 1 / (8 * Real.log ((m₀ * s : ℕ) : ℝ)) ≤ 1 / 2 :=
        one_div_le_one_div_of_le (by norm_num) (by linarith)
      linarith [hχ.2.1]
    obtain ⟨l1, l2, l3⟩ := li_rpow_le hX hβ
    set θ : ℕ → ℤ := fun b => if χ (b : ZMod (m₀ * s)) = 1 then 1 else -1 with hθ
    have hθχ : ∀ b ∈ cls m₀ s a₀, χ (b : ZMod (m₀ * s)) = (θ b : ℂ) := fun b hb => by
      simp only [hθ]
      split_ifs with h
      · simpa using h
      · simpa using (sq_eq_one_iff.1 (sq_apply χ hχ.1 (hcop b hb))).resolve_left h
    refine finite_core _ _ _ (fun b => (θ b : ℝ)) _ (Li X) (Li (X ^ β)) ρ δ hφ hρ0 hρ hδ0 hδ l2 l1
      (fun b _ => abs_jacobi_le _ _) (fun b _ => ?_) hs0
      (fun b hb => hT b (θ b) β (hcop b hb) (Or.inr ⟨χ, hχ, hθχ b hb⟩)) ?_
    · simp only [hθ]
      split_ifs <;> simp
    · rcases lt_or_ge lo β with hb | hb
      · left
        have h0 : ∑ b ∈ cls m₀ s a₀, (jacobiSym (b : ℤ) s : ℂ) * χ (b : ZMod (m₀ * s)) = 0 := by
          by_contra h
          exact hE ⟨inferInstance, χ, β, hχ, hb, h⟩
        rw [Finset.sum_congr rfl (fun b hb => by rw [hθχ b hb])] at h0
        exact_mod_cast h0
      · right
        refine l3.trans (mul_le_mul_of_nonneg_right (le_trans ?_ hlo) l2)
        have : X ^ (β - 1) ≤ X ^ (lo - 1) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
        linarith
  · push Not at hex
    obtain ⟨l1, l2, -⟩ := li_rpow_le (β := 1) hX (by norm_num)
    refine finite_core _ _ _ (fun _ => ((0 : ℤ) : ℝ)) _ (Li X) (Li (X ^ (1 : ℝ))) ρ δ hφ hρ0 hρ hδ0 hδ l2 l1
      (fun b _ => abs_jacobi_le _ _) (fun b _ => by simp) hs0
      (fun b hb => hT b 0 1 (hcop b hb) (Or.inl ⟨rfl, hex⟩)) (Or.inl (by simp))

theorem mean_PP_le {m₀ a₀ : ℕ} {X η : ℝ} (f : ℕ → ℝ) (hf : ∀ p, |f p| ≤ 1) (hX : 1 ≤ X) (hη0 : 0 ≤ η) (hη : η ≤ 3)
    (hcard : X ^ ((9 : ℝ) / 10) ≤ ((PP m₀ a₀ X).card : ℝ))
    (h : |∑ p ∈ (Icc 1 ⌊X⌋₊).filter (fun p => p.Prime ∧ p ≡ a₀ [MOD m₀]), f p| ≤
      η * (((Icc 1 ⌊X⌋₊).filter (fun p => p.Prime ∧ p ≡ a₀ [MOD m₀])).card : ℝ)) :
    |(∑ p ∈ PP m₀ a₀ X, f p) / (PP m₀ a₀ X).card| ≤ η + 4 * X ^ (-(2 : ℝ) / 5) := by
  set A := (Icc 1 ⌊X⌋₊).filter (fun p => p.Prime ∧ p ≡ a₀ [MOD m₀]) with hA
  have hX0 : 0 < X := by linarith
  have hsub : PP m₀ a₀ X ⊆ A := by
    intro p hp
    unfold Formalism.HermitianLattices.GL2PrimeSums.PP at hp
    rw [Finset.mem_filter, Finset.mem_Ioc] at hp
    rw [hA, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨by omega, hp.1.2⟩, hp.2⟩
  have hd : ((A \ PP m₀ a₀ X).card : ℝ) ≤ X ^ ((1 : ℝ) / 2) := by
    have : A \ PP m₀ a₀ X ⊆ Icc 1 ⌊Real.sqrt X⌋₊ := by
      intro p hp
      rw [Finset.mem_sdiff, hA, Finset.mem_filter, Finset.mem_Icc] at hp
      unfold Formalism.HermitianLattices.GL2PrimeSums.PP at hp
      rw [Finset.mem_filter, Finset.mem_Ioc] at hp
      rw [Finset.mem_Icc]
      refine ⟨hp.1.1.1, ?_⟩
      by_contra h
      exact hp.2 ⟨⟨by omega, hp.1.1.2⟩, hp.1.2⟩
    have h2 := Finset.card_le_card this
    rw [Nat.card_Icc, Nat.add_sub_cancel] at h2
    rw [← Real.sqrt_eq_rpow]
    exact le_trans (by exact_mod_cast h2) (Nat.floor_le (Real.sqrt_nonneg X))
  have hD : |∑ p ∈ A \ PP m₀ a₀ X, f p| ≤ ((A \ PP m₀ a₀ X).card : ℝ) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun p _ => hf p).trans (by simp))
  have hc : (A.card : ℝ) = ((A \ PP m₀ a₀ X).card : ℝ) + ((PP m₀ a₀ X).card : ℝ) := by
    exact_mod_cast (Finset.card_sdiff_add_card_eq_card hsub).symm
  have hs : ∑ p ∈ A \ PP m₀ a₀ X, f p + ∑ p ∈ PP m₀ a₀ X, f p = ∑ p ∈ A, f p := Finset.sum_sdiff hsub
  have h9 : 0 < X ^ ((9 : ℝ) / 10) := Real.rpow_pos_of_pos hX0 _
  have hP : 0 < ((PP m₀ a₀ X).card : ℝ) := lt_of_lt_of_le h9 hcard
  have e : X ^ ((1 : ℝ) / 2) = X ^ (-(2 : ℝ) / 5) * X ^ ((9 : ℝ) / 10) := by
    rw [← Real.rpow_add hX0]; norm_num
  have h25 : 0 < X ^ (-(2 : ℝ) / 5) := Real.rpow_pos_of_pos hX0 _
  have hd2 : ((A \ PP m₀ a₀ X).card : ℝ) ≤ X ^ (-(2 : ℝ) / 5) * ((PP m₀ a₀ X).card : ℝ) :=
    hd.trans (e ▸ mul_le_mul_of_nonneg_left hcard h25.le)
  rw [abs_div, abs_of_pos hP, div_le_iff₀ hP]
  have hd0 : (0 : ℝ) ≤ ((A \ PP m₀ a₀ X).card : ℝ) := Nat.cast_nonneg _
  have : |∑ p ∈ PP m₀ a₀ X, f p| ≤ |∑ p ∈ A, f p| + |∑ p ∈ A \ PP m₀ a₀ X, f p| := by
    rw [← hs]
    have := abs_sub (∑ p ∈ A \ PP m₀ a₀ X, f p + ∑ p ∈ PP m₀ a₀ X, f p) (∑ p ∈ A \ PP m₀ a₀ X, f p)
    simpa using this
  rw [hc] at h
  nlinarith

theorem eventually_sizes {a K c κ B : ℝ} (ha : 0 < a) (hK : 0 < K) (hc : 0 < c) (hκ : 0 < κ) :
    ∀ᶠ x : ℝ in atTop, 1 ≤ x ∧ 1 ≤ Real.log x ∧ B ≤ Real.log x ∧ K * Real.log x ^ 4 ≤ x ^ a ∧
      Real.exp (-c * Real.log x ^ 2) ≤ κ := by
  have h1 := (isLittleO_log_rpow_rpow_atTop (4 : ℝ) ha).bound (inv_pos.2 hK)
  have h2 : Tendsto (fun x : ℝ => Real.exp (-c * Real.log x ^ 2)) atTop (𝓝 0) := by
    apply Real.tendsto_exp_atBot.comp
    exact ((tendsto_pow_atTop (by norm_num)).comp Real.tendsto_log_atTop).const_mul_atTop_of_neg (by linarith)
  filter_upwards [h1, h2.eventually (eventually_le_nhds hκ), eventually_ge_atTop 1,
    Real.tendsto_log_atTop.eventually_ge_atTop 1, Real.tendsto_log_atTop.eventually_ge_atTop B] with x k1 k2 k3 k4 k5
  refine ⟨k3, k4, k5, ?_, k2⟩
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity),
    show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at k1
  rwa [← le_inv_mul_iff₀ hK]

end GlobalTheory.Mem.An.JacobiMean

namespace GlobalTheory.Mem.An

open JacobiMean

theorem jacobi_mean_small :
    GlobalTheory.Mem.An.TZRat → GlobalTheory.Mem.An.PageThm → Formalism.ZeroFreeDirichlet.ZFRDirichlet → ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ x₀ C' c' : ℝ, 0 < C' ∧ 0 < c' ∧ ∀ x : ℝ, x₀ ≤ x → ∀ m₀ a₀ : ℕ, 8 ∣ m₀ → 0 < m₀ → Nat.Coprime a₀ m₀ → ∀ X : ℝ, 0 < X → (1 / 4) * Real.log x ^ 2 * Real.log m₀ ≤ Real.log X → x ^ (eps / 6) ≤ Real.log X → ∃ nStar : ℕ, ∀ s : ℕ, 1 < s → Squarefree s → Nat.Coprime s m₀ → (s : ℝ) ≤ x ^ (800 : ℝ) → s ≠ nStar → |(∑ p ∈ Formalism.HermitianLattices.GL2PrimeSums.PP m₀ a₀ X, (jacobiSym (p : ℤ) s : ℝ)) / (Formalism.HermitianLattices.GL2PrimeSums.PP m₀ a₀ X).card| ≤ C' * Real.exp (-c' * Real.log x ^ 2) := by
  intro hTZ hPage _ eps h0 h1
  classical
  obtain ⟨x₁, hcount⟩ := card_primes_residue_ge_rpow hTZ eps h0 h1
  obtain ⟨c₂, c₃, CA, cS, h2, h3, hA, -, H⟩ := hTZ
  obtain ⟨cP, hcP, HP⟩ := hPage
  set c' : ℝ := min 1 (min (c₃ / 8) (cP / 8)) with hc'
  have hc'0 : 0 < c' := lt_min one_pos (lt_min (by positivity) (by positivity))
  have hc'1 : c' ≤ 1 := min_le_left _ _
  have hc'2 : c' ≤ c₃ / 8 := (min_le_right _ _).trans (min_le_left _ _)
  have hc'3 : c' ≤ cP / 8 := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨x₂, hx₂⟩ := eventually_atTop.1 (eventually_sizes (a := eps / 6) (K := 200 + 1 / c₃) (c := c')
    (κ := 1 / (4 * CA + 48)) (B := 8 * c₂) (by positivity) (by positivity) hc'0 (by positivity))
  refine ⟨max x₁ x₂, 4 * CA + 100, c', by positivity, hc'0, ?_⟩
  intro x hx m₀ a₀ h8 hm0 ha X hX0 hH1 hH2
  obtain ⟨k1, k2, k3, k4, k5⟩ := hx₂ x (le_trans (le_max_right _ _) hx)
  have hm8 : 8 ≤ m₀ := Nat.le_of_dvd hm0 h8
  have hm8' : (8 : ℝ) ≤ m₀ := by exact_mod_cast hm8
  have hcard := hcount x (le_trans (le_max_left _ _) hx) m₀ a₀ (by omega) ha X hX0 hH1 hH2
  set l := Real.log x with hl
  set e := Real.exp (-c' * l ^ 2) with he
  have he0 : 0 < e := Real.exp_pos _
  set Z : ℝ := m₀ * x ^ (800 : ℝ) with hZ
  have hx800 : 1 ≤ x ^ (800 : ℝ) := Real.one_le_rpow k1 (by norm_num)
  have hZ8 : 8 ≤ Z := by rw [hZ]; exact le_trans hm8' (le_mul_of_one_le_right (by positivity) hx800)
  have hlZ : Real.log Z = Real.log m₀ + 800 * l := by
    rw [hZ, Real.log_mul (by positivity) (by positivity), Real.log_rpow (by linarith)]
  have hlZ0 : 0 < Real.log Z := Real.log_pos (by linarith)
  have hl2 : 1 ≤ l ^ 2 := one_le_pow₀ k2
  have hl4 : l ^ 2 ≤ l ^ 4 := pow_le_pow_right₀ k2 (by norm_num)
  have hl3 : l ^ 3 ≤ l ^ 4 := pow_le_pow_right₀ k2 (by norm_num)
  have hl1 : l ≤ l ^ 2 := le_self_pow₀ k2 (by norm_num)
  have hK : 200 * l ^ 4 + l ^ 4 / c₃ ≤ Real.log X := by
    refine le_trans (le_of_eq ?_) (k4.trans hH2); ring
  have hK0 : 0 ≤ l ^ 4 / c₃ := by positivity
  have hK1 : l ^ 4 ≤ c₃ * Real.log X := by
    have : l ^ 4 / c₃ ≤ Real.log X := by linarith
    rwa [div_le_iff₀' h3] at this
  have hmain : l ^ 2 * Real.log Z ≤ 8 * Real.log X := by
    have : l ^ 2 * (Real.log m₀ + 800 * l) = l ^ 2 * Real.log m₀ + 800 * l ^ 3 := by ring
    rw [hlZ, this]; linarith
  have hX16 : 16 ≤ X := by
    have := Real.log_le_sub_one_of_pos hX0
    linarith
  have hlX0 : 0 < Real.log X := Real.log_pos (by linarith)
  rw [le_div_iff₀ (by positivity)] at k5
  have hcl : c' * l ^ 2 ≤ l ^ 2 := mul_le_of_le_one_left (by positivity) hc'1
  have k6 : 4 * (CA * e) + 48 * e ≤ 1 := by linarith
  have hAe : 0 < CA * e := by positivity

  have hexp : ∀ c L : ℝ, c' ≤ c / 8 → 0 < L → L ≤ Real.log Z → Real.exp (-c * Real.log X / L) ≤ e := by
    intro c L hc hL hLZ
    apply Real.exp_le_exp.2
    rw [div_le_iff₀ hL]
    have a1 : l ^ 2 * L ≤ 8 * Real.log X := le_trans (by gcongr) hmain
    have a2 : c' * (l ^ 2 * L) ≤ c / 8 * (8 * Real.log X) :=
      mul_le_mul hc a1 (by positivity) (by linarith)
    linarith
  set lo := 1 - cP / Real.log Z with hlo
  have hδ : 24 * X ^ (lo - 1) ≤ 24 * e := by
    have := hexp cP (Real.log Z) hc'3 hlZ0 le_rfl
    have e2 : X ^ (lo - 1) = Real.exp (-cP * Real.log X / Real.log Z) := by
      rw [Real.rpow_def_of_pos hX0, hlo]; congr 1; ring
    rw [e2]; linarith
  have h25 : X ^ (-(2 : ℝ) / 5) ≤ e := by
    rw [Real.rpow_def_of_pos hX0]
    apply Real.exp_le_exp.2
    linarith
  have hodd : ∀ s : ℕ, Nat.Coprime s m₀ → Odd s := fun s hs =>
    Nat.coprime_two_right.1 (Nat.Coprime.coprime_dvd_right (Dvd.dvd.trans (by norm_num) h8) hs)
  have hMZ : ∀ s : ℕ, (s : ℝ) ≤ x ^ (800 : ℝ) → ((m₀ * s : ℕ) : ℝ) ≤ Z := fun s hs => by
    rw [hZ, Nat.cast_mul]; gcongr

  have hgood : ∀ s : ℕ, 1 < s → Squarefree s → Nat.Coprime s m₀ → (s : ℝ) ≤ x ^ (800 : ℝ) → ¬ Exc m₀ a₀ lo s →
      |(∑ p ∈ Formalism.HermitianLattices.GL2PrimeSums.PP m₀ a₀ X, (jacobiSym (p : ℤ) s : ℝ)) / (Formalism.HermitianLattices.GL2PrimeSums.PP m₀ a₀ X).card| ≤
        (4 * CA + 100) * e := by
    intro s hs1 hsq hc hsx hE
    have hM8 : 8 ≤ m₀ * s := le_trans hm8 (Nat.le_mul_of_pos_right _ (by omega))
    haveI : NeZero (m₀ * s) := ⟨by omega⟩
    have hM4 : (m₀ * s) % 4 ≠ 2 := by
      have : 8 ∣ m₀ * s := h8.mul_right s
      omega
    obtain ⟨-, -, HC⟩ := H (m₀ * s) (by omega) hM4
    have hM8' : (8 : ℝ) ≤ ((m₀ * s : ℕ) : ℝ) := by exact_mod_cast hM8
    have hlM0 : 0 < Real.log ((m₀ * s : ℕ) : ℝ) := Real.log_pos (by linarith)
    have hlM : Real.log ((m₀ * s : ℕ) : ℝ) ≤ Real.log Z := Real.log_le_log (by linarith) (hMZ s hsx)
    have hrange : ((m₀ * s : ℕ) : ℝ) ^ c₂ ≤ X := by
      rw [← Real.log_le_log_iff (by positivity) hX0, Real.log_rpow (by linarith)]
      have a1 : 8 * c₂ * Real.log ((m₀ * s : ℕ) : ℝ) ≤ l ^ 2 * Real.log Z :=
        mul_le_mul (by linarith) hlM hlM0.le (by linarith)
      linarith
    have hsq3 : Real.exp (-Real.sqrt (c₃ * Real.log X)) ≤ e := by
      apply Real.exp_le_exp.2
      have : l ^ 2 ≤ Real.sqrt (c₃ * Real.log X) := Real.le_sqrt_of_sq_le (by linarith)
      linarith
    have hb := twisted_sum_le (lo := lo) (X := X) (ρ := 2 * (CA * e)) (δ := 24 * e) hm8 ha hs1 (hodd s hc) hsq hc
      (by positivity) (by linarith) (by linarith) hX16 hδ (fun b θ β hb hθ => by
        have hq := HC b θ β hb hθ X hrange
        have hE0 : 0 ≤ Formalism.HermitianLattices.GL2PrimeSums.Emain θ β X :=
          (mul_nonneg_iff_of_pos_left (by positivity)).1 (le_trans (abs_nonneg _) hq)
        refine hq.trans (mul_le_mul_of_nonneg_right ?_ hE0)
        have := mul_le_mul_of_nonneg_left (add_le_add (hexp c₃ _ hc'2 hlM0 hlM) hsq3) hA.le
        linarith) hE
    have := mean_PP_le (fun p => (jacobiSym (p : ℤ) s : ℝ)) (fun p => abs_jacobi_le _ _) (by linarith)
      (by positivity) (by linarith) hcard hb
    linarith
  by_cases hex : ∃ s : ℕ, Squarefree s ∧ Nat.Coprime s m₀ ∧ (s : ℝ) ≤ x ^ (800 : ℝ) ∧ Exc m₀ a₀ lo s
  · obtain ⟨n, n1, n2, n3, n4⟩ := hex
    refine ⟨n, fun s hs1 hsq hc hsx hne => hgood s hs1 hsq hc hsx fun hE => hne ?_⟩
    exact exc_unique (HP Z (by linarith)) (hodd s hc) hsq hc (hMZ s hsx) (hodd n n2) n1 n2 (hMZ n n3) hE n4
  · exact ⟨0, fun s hs1 hsq hc hsx _ => hgood s hs1 hsq hc hsx fun hE => hex ⟨s, hsq, hc, hsx, hE⟩⟩

end GlobalTheory.Mem.An
