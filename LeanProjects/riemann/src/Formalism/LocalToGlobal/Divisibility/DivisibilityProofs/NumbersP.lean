import Formalism.LocalToGlobal.Divisibility.NumbersLemmas
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.PlaceSumSquares

noncomputable section

namespace Formalism.L2.DIV

open Formalism.BasicNotions Formalism.FrobeniusOrbits NumberField IsDedekindDomain
open scoped BigOperators

section LP

variable (l d : ℕ) [NeZero d] (Ds : ZMod d → ℝ)

theorem sum_zmod_sub_const (x : ZMod d → ℝ) (c : ZMod d) : ∑ s, x (s - c) = ∑ s, x s :=
  Fintype.sum_equiv (Equiv.subRight c) _ _ (fun _ => rfl)

theorem lpFeasible_le (hl : 2 ≤ l) : ∀ y ∈ lpFeasible l d Ds, y ≤ (∑ s, Ds s) / ((l : ℝ) + 1) := by
  have hl' : (2 : ℝ) ≤ l := by exact_mod_cast hl
  rintro y ⟨xs, hx0, hodd, hcon, rfl⟩
  have hsum := Finset.sum_le_sum fun s (_ : s ∈ Finset.univ) => hcon s
  rw [Finset.sum_add_distrib] at hsum
  have hshift : ∑ s, ∑ i ∈ Finset.range d, xs (s - (i : ZMod d)) i =
      ∑ s, ∑ i ∈ Finset.range d, xs s i := by
    rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact Fintype.sum_equiv (Equiv.subRight (i : ZMod d)) _ _ (fun s => rfl)
  have hfirst : (l : ℝ) * ∑ s, ∑ i ∈ Finset.range d, xs s i ≤
      ∑ s, ∑ i ∈ Finset.range d, (l : ℝ) ^ i * xs s i := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun s _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    by_cases ho : Odd i
    · have hli : (l : ℝ) ≤ (l : ℝ) ^ i := by
        obtain ⟨k, rfl⟩ := ho
        calc (l : ℝ) = (l : ℝ) ^ 1 := (pow_one _).symm
          _ ≤ (l : ℝ) ^ (2 * k + 1) := pow_le_pow_right₀ (by linarith) (by omega)
      exact mul_le_mul_of_nonneg_right hli (hx0 s i)
    · rw [hodd s i (Or.inl ho)]
      simp
  rw [hshift] at hsum
  rw [le_div_iff₀ (by linarith)]
  linarith

theorem zero_mem_lpFeasible (hD : ∀ s, 0 ≤ Ds s) : (0 : ℝ) ∈ lpFeasible l d Ds :=
  ⟨fun _ _ => 0, fun _ _ => le_rfl, fun _ _ _ => rfl, fun s => by simp [hD s], by simp⟩

theorem gamma_sub (hl : 2 ≤ l) (S : ℝ) :
    (l : ℝ) / ((l : ℝ) ^ 2 - 1) * S - S / ((l : ℝ) + 1) = S / ((l : ℝ) ^ 2 - 1) := by
  have hl' : (2 : ℝ) ≤ l := by exact_mod_cast hl
  have h1 : (l : ℝ) + 1 ≠ 0 := by linarith
  have h2 : (l : ℝ) - 1 ≠ 0 := by linarith
  have h3 : (l : ℝ) ^ 2 - 1 = ((l : ℝ) - 1) * ((l : ℝ) + 1) := by ring
  rw [h3]
  field_simp
  ring

theorem lpF_ge (hl : 2 ≤ l) (hD : ∀ s, 0 ≤ Ds s) : (∑ s, Ds s) / ((l : ℝ) ^ 2 - 1) ≤ lpF l d Ds := by
  have h := csSup_le ⟨0, zero_mem_lpFeasible l d Ds hD⟩ (lpFeasible_le l d Ds hl)
  unfold lpF
  rw [← gamma_sub l hl]
  linarith

theorem alt_sum_bounds : ∀ (n : ℕ) (c : ℕ → ℝ), (∀ k, 0 ≤ c k) → (∀ k, c (k + 1) ≤ c k) →
    0 ≤ ∑ k ∈ Finset.range n, (-1 : ℝ) ^ k * c k ∧ ∑ k ∈ Finset.range n, (-1 : ℝ) ^ k * c k ≤ c 0
  | 0, c, h0, _ => by simp [h0 0]
  | n + 1, c, h0, h1 => by
    obtain ⟨a, b⟩ := alt_sum_bounds n (fun k => c (k + 1)) (fun k => h0 _) (fun k => h1 _)
    rw [Finset.sum_range_succ']
    have h : ∑ k ∈ Finset.range n, (-1 : ℝ) ^ (k + 1) * c (k + 1) =
        -∑ k ∈ Finset.range n, (-1 : ℝ) ^ k * c (k + 1) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [h]
    simp only [pow_zero, one_mul]
    have := h1 0
    constructor <;> linarith

def cycSum (n : ℕ) (s : ZMod d) : ℝ :=
  ∑ k ∈ Finset.range n, (-1 : ℝ) ^ k * (((l : ℝ)⁻¹) ^ (k + 1) * Ds (s - (k : ZMod d)))

theorem cycSum_rec (hl : 2 ≤ l) (n : ℕ) (s : ZMod d) :
    (l : ℝ) * cycSum l d Ds n s + cycSum l d Ds n (s - 1) =
      Ds s - (-1 : ℝ) ^ n * ((l : ℝ)⁻¹) ^ n * Ds (s - (n : ZMod d)) := by
  have hl0 : (l : ℝ) ≠ 0 := by
    have : (2 : ℝ) ≤ l := by exact_mod_cast hl
    linarith
  induction n with
  | zero => simp [cycSum]
  | succ n ih =>
    have e1 : cycSum l d Ds (n + 1) s = cycSum l d Ds n s +
        (-1 : ℝ) ^ n * (((l : ℝ)⁻¹) ^ (n + 1) * Ds (s - (n : ZMod d))) := Finset.sum_range_succ _ _
    have e2 : cycSum l d Ds (n + 1) (s - 1) = cycSum l d Ds n (s - 1) +
        (-1 : ℝ) ^ n * (((l : ℝ)⁻¹) ^ (n + 1) * Ds (s - 1 - (n : ZMod d))) := Finset.sum_range_succ _ _
    have e3 : s - 1 - (n : ZMod d) = s - ((n + 1 : ℕ) : ZMod d) := by
      push_cast
      ring
    have e4 : (l : ℝ) * ((l : ℝ)⁻¹) ^ (n + 1) = ((l : ℝ)⁻¹) ^ n := by
      rw [pow_succ, mul_comm, mul_assoc, inv_mul_cancel₀ hl0, mul_one]
    rw [e1, e2, e3]
    have e5 : (l : ℝ) * (cycSum l d Ds n s + (-1 : ℝ) ^ n * (((l : ℝ)⁻¹) ^ (n + 1) * Ds (s - (n : ZMod d)))) =
        (l : ℝ) * cycSum l d Ds n s + (-1 : ℝ) ^ n * (((l : ℝ) * ((l : ℝ)⁻¹) ^ (n + 1)) * Ds (s - (n : ZMod d))) := by
      ring
    rw [e5, e4]
    have e6 : (-1 : ℝ) ^ (n + 1) = -(-1 : ℝ) ^ n := by ring
    rw [e6]
    linear_combination ih

theorem cyc_den_pos (hl : 2 ≤ l) : 0 < 1 - (-1 : ℝ) ^ d * ((l : ℝ)⁻¹) ^ d := by
  have hl' : (2 : ℝ) ≤ l := by exact_mod_cast hl
  have hi0 : 0 ≤ (l : ℝ)⁻¹ := by positivity
  have hi1 : (l : ℝ)⁻¹ ≤ 1 / 2 := by
    rw [inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) hl'
  have hd : 1 ≤ d := Nat.one_le_iff_ne_zero.2 (NeZero.ne d)
  have hp : ((l : ℝ)⁻¹) ^ d ≤ ((l : ℝ)⁻¹) ^ 1 := pow_le_pow_of_le_one hi0 (by linarith) hd
  have hp0 : 0 ≤ ((l : ℝ)⁻¹) ^ d := pow_nonneg hi0 _
  rcases neg_one_pow_eq_or ℝ d with h | h <;> rw [h] <;> linarith

theorem flat_mem_lpFeasible (hl : 2 ≤ l) (hd : 2 ≤ d) (hD : ∀ s, 0 ≤ Ds s) (hflat : ∀ a b, Ds a ≤ (l : ℝ) * Ds b) :
    (∑ s, Ds s) / ((l : ℝ) + 1) ∈ lpFeasible l d Ds := by
  have hl' : (2 : ℝ) ≤ l := by exact_mod_cast hl
  have hl0 : (0 : ℝ) < l := by linarith
  have hi0 : 0 ≤ (l : ℝ)⁻¹ := by positivity
  set ρ : ℝ := 1 - (-1 : ℝ) ^ d * ((l : ℝ)⁻¹) ^ d with hρ
  have hρ0 : 0 < ρ := cyc_den_pos l d hl
  set x : ZMod d → ℝ := fun s => cycSum l d Ds d s / ρ with hx
  have hx0 : ∀ s, 0 ≤ x s := by
    intro s
    refine div_nonneg ?_ hρ0.le
    refine (alt_sum_bounds d (fun k => ((l : ℝ)⁻¹) ^ (k + 1) * Ds (s - (k : ZMod d)))
      (fun k => mul_nonneg (pow_nonneg hi0 _) (hD _)) (fun k => ?_)).1
    have h1 : (l : ℝ)⁻¹ * Ds (s - ((k + 1 : ℕ) : ZMod d)) ≤ Ds (s - (k : ZMod d)) := by
      rw [inv_mul_le_iff₀ hl0]
      exact hflat _ _
    calc ((l : ℝ)⁻¹) ^ (k + 1 + 1) * Ds (s - ((k + 1 : ℕ) : ZMod d))
        = ((l : ℝ)⁻¹) ^ (k + 1) * ((l : ℝ)⁻¹ * Ds (s - ((k + 1 : ℕ) : ZMod d))) := by ring
      _ ≤ ((l : ℝ)⁻¹) ^ (k + 1) * Ds (s - (k : ZMod d)) :=
        mul_le_mul_of_nonneg_left h1 (pow_nonneg hi0 _)
  have hrec : ∀ s, (l : ℝ) * x s + x (s - 1) = Ds s := by
    intro s
    have h := cycSum_rec l d Ds hl d s
    rw [ZMod.natCast_self, sub_zero] at h
    simp only [hx]
    rw [mul_div_assoc', ← add_div, h, div_eq_iff hρ0.ne', hρ]
    ring
  have htot : (∑ s, Ds s) / ((l : ℝ) + 1) = ∑ s, x s := by
    rw [div_eq_iff (by linarith)]
    have h1 : ∑ s, Ds s = ∑ s, ((l : ℝ) * x s + x (s - 1)) := Finset.sum_congr rfl fun s _ => (hrec s).symm
    rw [h1, Finset.sum_add_distrib, sum_zmod_sub_const d x 1, ← Finset.mul_sum]
    ring
  have hmem : 1 ∈ Finset.range d := Finset.mem_range.2 (by omega)
  refine ⟨fun s i => if i = 1 then x s else 0, ?_, ?_, ?_, ?_⟩
  · intro s i
    dsimp only
    split_ifs
    · exact hx0 s
    · exact le_rfl
  · rintro s i h
    dsimp only
    rw [if_neg]
    rintro rfl
    rcases h with h | h
    · exact h odd_one
    · omega
  · intro s
    have h1 : ∑ i ∈ Finset.range d, (l : ℝ) ^ i * (if i = 1 then x s else 0) = (l : ℝ) * x s := by
      rw [Finset.sum_eq_single 1 (fun i _ hi => by rw [if_neg hi, mul_zero]) (fun h => absurd hmem h)]
      simp
    have h2 : ∑ i ∈ Finset.range d, (if i = 1 then x (s - (i : ZMod d)) else 0) = x (s - 1) := by
      rw [Finset.sum_eq_single 1 (fun i _ hi => by rw [if_neg hi]) (fun h => absurd hmem h)]
      simp
    rw [h1, h2, hrec s]
  · rw [htot]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.sum_eq_single 1 (fun i _ hi => if_neg hi) (fun h => absurd hmem h)]
    simp

theorem lpF_flat (hl : 2 ≤ l) (hd : 2 ≤ d) (hD : ∀ s, 0 ≤ Ds s) (hflat : ∀ a b, Ds a ≤ (l : ℝ) * Ds b) :
    lpF l d Ds = (∑ s, Ds s) / ((l : ℝ) ^ 2 - 1) := by
  have hS : sSup (lpFeasible l d Ds) = (∑ s, Ds s) / ((l : ℝ) + 1) :=
    le_antisymm (csSup_le ⟨0, zero_mem_lpFeasible l d Ds hD⟩ (lpFeasible_le l d Ds hl))
      (le_csSup ⟨_, lpFeasible_le l d Ds hl⟩ (flat_mem_lpFeasible l d Ds hl hd hD hflat))
  unfold lpF
  rw [hS, gamma_sub l hl]

end LP

namespace NumDatum

variable (N : NumDatum)

theorem pos_injective (p n : ℕ) : Function.Injective fun z : RPl N.R => N.pos p z n := by
  intro z z' h
  have h1 : xor z.1 (decide (N.cls p = PrimeClass.signal ∧ Odd n)) =
      xor z'.1 (decide (N.cls p = PrimeClass.signal ∧ Odd n)) := congrArg Prod.fst h
  have h2 : z.2 + n • N.hP p = z'.2 + n • N.hP p := congrArg Prod.snd h
  refine Prod.ext ?_ (add_right_cancel h2)
  revert h1
  cases z.1 <;> cases z'.1 <;> cases decide (N.cls p = PrimeClass.signal ∧ Odd n) <;> simp

theorem sum_pos (p n : ℕ) (g : RPl N.R → ℝ) : ∑ z, g (N.pos p z n) = ∑ z, g z :=
  Fintype.sum_bijective (fun z : RPl N.R => N.pos p z n)
    (Finite.injective_iff_bijective.1 (N.pos_injective p n)) _ _ (fun _ => rfl)

theorem sum_orbit_total (p : ℕ) (g : RPl N.R → ℝ) :
    ∑ z, ∑ s : ZMod (N.ordP p), g (N.pos p z s.val) = (N.ordP p : ℝ) * ∑ z, g z := by
  rw [Finset.sum_comm]
  simp only [sum_pos]
  rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]

theorem k_sub_one_nonneg : 0 ≤ (N.R.k : ℝ) - 1 := by
  have h := N.R.m_add_three_le_k
  have h1 : (1 : ℝ) ≤ (N.R.k : ℝ) := by exact_mod_cast (by omega : 1 ≤ N.R.k)
  linarith

theorem two_le_ordP {p : ℕ} (hc : N.cls p = PrimeClass.inertClass ∨ N.cls p = PrimeClass.signal)
    (h : ¬ (N.cls p = PrimeClass.inertClass ∧ N.hP p = 0)) : 2 ≤ N.ordP p := by
  unfold ordP
  rcases hc with hc | hc
  · rw [if_neg (by rw [hc]; decide)]
    have h0 : N.hP p ≠ 0 := fun e => h ⟨hc, e⟩
    have h1 : addOrderOf (N.hP p) ≠ 1 := fun e => h0 (AddMonoid.addOrderOf_eq_one_iff.1 e)
    have h2 := addOrderOf_pos (N.hP p)
    omega
  · rw [if_pos hc]
    have h2 := addOrderOf_pos (2 • N.hP p)
    omega

end NumDatum

theorem numDatum_fInertGe : NumDatum.FInertGe := by
  intro N j p hp _ hw
  have hk := N.k_sub_one_nonneg
  unfold NumDatum.FInert
  split_ifs with h
  · exact le_rfl
  · have hn : (0 : ℝ) < (N.ordP p : ℝ) := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne _))
    rw [le_div_iff₀ hn]
    have h1 : ∀ z : RPl N.R, (∑ s : ZMod (N.ordP p), ((N.R.k : ℝ) - 1) * N.w j (N.pos p z s.val)) / ((p : ℝ) ^ 2 - 1) ≤
        N.FOrb j p z := fun z =>
      lpF_ge p (N.ordP p) _ hp.two_le (fun s => mul_nonneg hk (hw _))
    refine le_trans (le_of_eq ?_) (Finset.sum_le_sum fun z _ => h1 z)
    rw [← Finset.sum_div, ← Finset.sum_div, N.sum_orbit_total p (fun z => ((N.R.k : ℝ) - 1) * N.w j z)]
    ring

theorem inert_flat : NumDatum.FInertFlat := by
  intro N j p hp hc hw hflat
  have hk := N.k_sub_one_nonneg
  unfold NumDatum.FInert
  split_ifs with h
  · rfl
  · have hn : (N.ordP p : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne _)
    have h1 : ∀ z : RPl N.R, N.FOrb j p z =
        (∑ s : ZMod (N.ordP p), ((N.R.k : ℝ) - 1) * N.w j (N.pos p z s.val)) / ((p : ℝ) ^ 2 - 1) := fun z =>
      lpF_flat p (N.ordP p) _ hp.two_le (N.two_le_ordP hc h) (fun s => mul_nonneg hk (hw _))
        (fun a b => by
          have := mul_le_mul_of_nonneg_left (hflat (N.pos p z b.val) (N.pos p z a.val)) hk
          linarith)
    rw [Finset.sum_congr rfl fun z _ => h1 z, ← Finset.sum_div, ← Finset.sum_div,
      N.sum_orbit_total p (fun z => ((N.R.k : ℝ) - 1) * N.w j z)]
    field_simp

section Places

variable {K : Type} [Field K] [NumberField K]

theorem plc_prime' (w : HeightOneSpectrum (𝓞 K)) : (Formalism.EigenvalueLevelCeiling.plc w).Prime := by
  have : Finite (𝓞 K ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot w.asIdeal w.ne_bot
  have : w.asIdeal.IsPrime := w.isPrime
  exact CharP.char_is_prime (𝓞 K ⧸ w.asIdeal) (ringChar (𝓞 K ⧸ w.asIdeal))

theorem vw_prime_eq_zero (w : HeightOneSpectrum (𝓞 K)) {p : ℕ} (hp : p.Prime) (hne : p ≠ Formalism.EigenvalueLevelCeiling.plc w) :
    Formalism.DivisionValues.vw w (p : K) = 0 := by
  classical
  have hnot : (p : 𝓞 K) ∉ w.asIdeal := by
    intro hmem
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast] at hmem
    have hdvd : Formalism.EigenvalueLevelCeiling.plc w ∣ p := (ringChar.spec (𝓞 K ⧸ w.asIdeal) p).1 hmem
    exact hne ((Nat.prime_dvd_prime_iff_eq (plc_prime' w) hp).1 hdvd).symm
  have h : ((p : 𝓞 K) : K) = (p : K) := map_natCast _ p
  have hx : (p : 𝓞 K) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hJ : (Ideal.span {(p : 𝓞 K)} : Ideal (𝓞 K)) ≠ 0 := by
    rw [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact hx
  rw [← h, Formalism.DivisionValues.W5.vw_int, FractionalIdeal.count_coe K w hJ]
  have hm : Associates.mk (Ideal.span {(p : 𝓞 K)} : Ideal (𝓞 K)) ≠ 0 := by
    rwa [ne_eq, Associates.mk_eq_zero]
  have h0 : (Associates.mk w.asIdeal).count
      (Associates.mk (Ideal.span {(p : 𝓞 K)} : Ideal (𝓞 K))).factors = 0 := by
    by_contra hc
    have h1 : 1 ≤ (Associates.mk w.asIdeal).count
        (Associates.mk (Ideal.span {(p : 𝓞 K)} : Ideal (𝓞 K))).factors := Nat.one_le_iff_ne_zero.2 hc
    rw [← Associates.prime_pow_dvd_iff_le hm w.associates_irreducible, pow_one,
      Associates.mk_le_mk_iff_dvd, Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem] at h1
    exact hnot h1
  rw [h0]
  rfl

end Places

theorem NumDatum.prime_of_mem_primeSupport (N : NumDatum) {p : ℕ} (h : p ∈ N.suppP) : p.Prime := by
  unfold NumDatum.suppP at h
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with ⟨_, h⟩ | h | h | h
  · exact h
  · rw [h]; exact N.g_prime 0
  · rw [h]; exact N.g_prime 1
  · rw [h]; exact N.hyp.2.1

theorem split_places : NumDatum.FoPlaces := by
  intro N K _ _
  have hfun : ∀ j, (fun w : HeightOneSpectrum (𝓞 K) => Formalism.DivisionValues.lw w * ((Formalism.EigenvalueLevelCeiling.ramw w : ℝ) * N.Fj j w)) =
      fun w => ∑ p ∈ N.suppP, (Formalism.DivisionValues.lw w * (Formalism.DivisionValues.vw w (p : K) : ℝ)) * N.FjP j p := by
    intro j
    funext w
    rw [Finset.sum_eq_single (Formalism.EigenvalueLevelCeiling.plc w)]
    · unfold NumDatum.Fj Formalism.EigenvalueLevelCeiling.ramw
      ring
    · intro p hp hne
      rw [vw_prime_eq_zero w (N.prime_of_mem_primeSupport hp) hne]
      simp
    · intro hs
      rw [N.FjP_off_supp j (plc_prime' w) hs, mul_zero]
  have hfin : ∀ j, ∀ p ∈ N.suppP, (Function.support fun w : HeightOneSpectrum (𝓞 K) =>
      (Formalism.DivisionValues.lw w * (Formalism.DivisionValues.vw w (p : K) : ℝ)) * N.FjP j p).Finite := by
    intro j p hp
    exact ((Formalism.DivisionValues.place_sum_natural K p (N.prime_of_mem_primeSupport hp).pos).1).subset
      (Function.support_mul_subset_left _ _)
  refine ⟨fun j => ?_, ?_⟩
  · rw [hfun j]
    exact (Set.Finite.biUnion N.suppP.finite_toSet (fun p hp => hfin j p hp)).subset
      (Finset.support_sum _ _)
  · unfold NumDatum.Fo
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hfun j, finsum_sum_comm _ _ (hfin j)]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hP := Formalism.DivisionValues.place_sum_natural K p (N.prime_of_mem_primeSupport hp).pos
    rw [← finsum_mul, hP.2.1]

end Formalism.L2.DIV
