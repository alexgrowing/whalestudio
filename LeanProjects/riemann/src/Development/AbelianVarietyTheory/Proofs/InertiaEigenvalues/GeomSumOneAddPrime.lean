import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemEurOfTeichmullerSeries
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicPowerSeriesAlgHomActionLaws

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Cyc

namespace GlobalTheory.Cyc

open PowerSeries in

theorem algHom_sub_dvd {O : Type} [CommRing O] (f : O⟦X⟧ →ₐ[O] O⟦X⟧) (hf : (X : O⟦X⟧) ∣ f X)
    (a : O⟦X⟧) : f X - X ∣ f a - a := by
  set y := f X with hy
  let g : ℕ → O⟦X⟧ := fun n => ∑ i ∈ Finset.range n, y ^ i * X ^ (n - 1 - i)
  have hg : ∀ n, g n * (y - X) = y ^ n - X ^ n := fun n => geom_sum₂_mul y X n
  have hgd : ∀ n, (X : O⟦X⟧) ^ (n - 1) ∣ g n := by
    intro n
    refine Finset.dvd_sum fun i hi => ?_
    have hi' := Finset.mem_range.mp hi
    have e : n - 1 = i + (n - 1 - i) := by omega
    conv_lhs => rw [e, pow_add]
    exact mul_dvd_mul (pow_dvd_pow_of_dvd hf i) dvd_rfl
  let P : ℕ → O⟦X⟧ := fun N => ∑ n ∈ Finset.range N, C (coeff n a) * g n
  have hP : ∀ m k, (X : O⟦X⟧) ^ m ∣ P (m + 1 + k) - P (m + 1) := by
    intro m k
    induction k with
    | zero => simp
    | succ k ih =>
      have e : P (m + 1 + (k + 1)) - P (m + 1)
          = (P (m + 1 + k) - P (m + 1)) + C (coeff (m + 1 + k) a) * g (m + 1 + k) := by
        simp only [P, ← add_assoc, Finset.sum_range_succ _ (m + 1 + k)]; ring
      rw [e]
      exact dvd_add ih (Dvd.dvd.mul_left ((pow_dvd_pow _ (by omega)).trans (hgd _)) _)
  let b : O⟦X⟧ := PowerSeries.mk fun m => coeff m (P (m + 2))
  have hb : ∀ N, (X : O⟦X⟧) ^ N ∣ P (N + 1) - b := by
    intro N
    rw [X_pow_dvd_iff]
    intro m hm
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hm
    have := X_pow_dvd_iff.mp (hP (m + 1) k) m (by omega)
    rw [map_sub] at this ⊢
    rw [coeff_mk, show m + k + 1 + 1 = m + 1 + 1 + k by omega]
    exact this
  have hr : ∀ N, ∃ r : O⟦X⟧, a = ∑ n ∈ Finset.range N, C (coeff n a) * X ^ n + X ^ N * r := by
    intro N
    have : (X : O⟦X⟧) ^ N ∣ a - ∑ n ∈ Finset.range N, C (coeff n a) * X ^ n := by
      rw [X_pow_dvd_iff]
      intro m hm
      simp [coeff_X_pow, hm]
    obtain ⟨r, hr⟩ := this
    exact ⟨r, by rw [← hr]; ring⟩
  have hN : ∀ N, (X : O⟦X⟧) ^ N ∣ f a - a - (y - X) * P N := by
    intro N
    obtain ⟨r, hr⟩ := hr N
    have h1 : f a = ∑ n ∈ Finset.range N, C (coeff n a) * y ^ n + y ^ N * f r := by
      conv_lhs => rw [hr]
      simp only [map_add, map_sum, map_mul, map_pow, ← hy]
      congr 1
      refine Finset.sum_congr rfl fun n _ => ?_
      congr 1
      exact f.commutes _
    have h2 : (y - X) * P N = ∑ n ∈ Finset.range N, C (coeff n a) * y ^ n
        - ∑ n ∈ Finset.range N, C (coeff n a) * X ^ n := by
      simp only [P, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [← mul_sub, ← hg]; ring
    have h3 : f a - a - (y - X) * P N = y ^ N * f r - X ^ N * r := by
      rw [h2, h1]; linear_combination -hr
    rw [h3]
    exact dvd_sub (Dvd.dvd.mul_right (pow_dvd_pow_of_dvd hf N) _) (dvd_mul_right _ _)
  refine ⟨b, ?_⟩
  ext m
  have : (X : O⟦X⟧) ^ (m + 1) ∣ f a - a - (y - X) * b := by
    have e : f a - a - (y - X) * b
        = (f a - a - (y - X) * P (m + 1 + 1)) + (y - X) * (P (m + 1 + 1) - b) := by ring
    rw [e]
    exact dvd_add ((pow_dvd_pow _ (by omega)).trans (hN _)) (Dvd.dvd.mul_left (hb _) _)
  have := X_pow_dvd_iff.mp this m (by omega)
  rw [map_sub] at this
  exact sub_eq_zero.mp this

theorem geom_sum_one_add_prime {R : Type} [CommRing R] {p : ℕ} (hp : p.Prime) (x : R) :
    ∃ r, ∑ k ∈ Finset.range p, (1 + x) ^ k = x ^ (p - 1) + (p : R) * r := by
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp (Polynomial.X : Polynomial ℤ) 1
  have h1 : (∑ k ∈ Finset.range p, (1 + Polynomial.X : Polynomial ℤ) ^ k)
      = Polynomial.X ^ (p - 1) + (p : Polynomial ℤ) * r := by
    apply mul_right_cancel₀ (Polynomial.X_ne_zero (R := ℤ))
    have h := geom_sum_mul (1 + Polynomial.X : Polynomial ℤ) p
    have e : (Polynomial.X : Polynomial ℤ) ^ p = Polynomial.X ^ (p - 1) * Polynomial.X := by
      rw [← pow_succ, Nat.sub_add_cancel hp.one_le]
    rw [add_comm Polynomial.X, one_pow, e] at hr
    rw [hr] at h
    linear_combination h
  refine ⟨Polynomial.aeval x r, ?_⟩
  have := congrArg (Polynomial.aeval x) h1
  simpa [map_sum] using this

variable (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O]

theorem act_X_eq (c : ℤ_[l]) : act l O c PowerSeries.X = cyc l O c := (GlobalTheory.Cyc.act_laws l O).1 c

theorem act_comm' (c c' : ℤ_[l]) (a) : act l O c (act l O c' a) = act l O c' (act l O c a) := by
  rw [(GlobalTheory.Cyc.act_laws l O).2.1, (GlobalTheory.Cyc.act_laws l O).2.1, mul_comm]

theorem act_nat_X (k : ℕ) : act l O (k : ℤ_[l]) PowerSeries.X = (1 + PowerSeries.X) ^ k - 1 := by
  rw [act_X_eq, (GlobalTheory.Cyc.act_laws l O).2.2.2.1]

theorem cyc_eq_X_mul (c : ℤ_[l]) :
    ∃ b, cyc l O c = PowerSeries.X * (PowerSeries.C (algebraMap ℤ_[l] O c) + PowerSeries.X * b) := by
  have : (PowerSeries.X : PowerSeries O) ^ 2 ∣
      cyc l O c - PowerSeries.C (algebraMap ℤ_[l] O c) * PowerSeries.X := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro m hm
    interval_cases m
    · simp [cyc_const]
    · simp [(GlobalTheory.Cyc.act_laws l O).2.2.2.2.1]
  obtain ⟨b, hb⟩ := this
  exact ⟨b, by linear_combination hb⟩

theorem XX_mul_QQ (s : ℕ) : XX l O s * QQ l O s = (1 + XX l O s) ^ l - 1 := by
  have h := geom_sum_mul (1 + XX l O s) l
  unfold QQ
  linear_combination h

theorem XX_mul_QQ' (s : ℕ) (hs : 1 ≤ s) :
    XX l O s * QQ l O s = (1 + PowerSeries.X) ^ l ^ s - 1 := by
  rw [XX_mul_QQ, XX, add_sub_cancel, ← pow_mul, ← pow_succ, Nat.sub_add_cancel hs]

theorem phi_pow_X (n : ℕ) :
    (phi l O ^ n) PowerSeries.X = (1 + PowerSeries.X) ^ l ^ n - 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', AlgHom.mul_apply, ih]
    simp only [map_sub, map_pow, map_add, map_one, phi, act_nat_X]
    rw [add_sub_cancel, ← pow_mul, ← pow_succ']

theorem act_C (c : ℤ_[l]) (x : O) : act l O c (PowerSeries.C x) = PowerSeries.C x :=
  (act l O c).commutes x

theorem act_QQ_one (c : ℤ_[l]ˣ) :
    ∃ b, act l O c (QQ l O 1) = QQ l O 1 * (1 + PowerSeries.X * b) := by
  obtain ⟨b, hb⟩ := cyc_eq_X_mul l O c
  have h1 : PowerSeries.X * QQ l O 1 = act l O (l : ℤ_[l]) PowerSeries.X := by
    have := XX_mul_QQ' l O 1 le_rfl
    rw [act_nat_X]
    simpa [XX] using this
  have h2 := act_comm' l O c l PowerSeries.X
  rw [← h1, map_mul, act_X_eq, hb] at h2
  simp only [map_mul, map_add, act_C, ← h1] at h2
  have hU : IsUnit (PowerSeries.C (algebraMap ℤ_[l] O c) + PowerSeries.X * b) := by
    rw [PowerSeries.isUnit_iff_constantCoeff]
    simpa using c.isUnit.map (algebraMap ℤ_[l] O)
  obtain ⟨v, hv⟩ := hU.exists_right_inv
  have h3 : (PowerSeries.C (algebraMap ℤ_[l] O c) + PowerSeries.X * b) * act l O c (QQ l O 1)
      = QQ l O 1 * (PowerSeries.C (algebraMap ℤ_[l] O c)
        + PowerSeries.X * QQ l O 1 * act l O (l : ℤ_[l]) b) := by
    apply PowerSeries.X_mul_cancel
    linear_combination h2
  refine ⟨v * (QQ l O 1 * act l O (l : ℤ_[l]) b - b), ?_⟩
  linear_combination v * h3 + (QQ l O 1 - act l O c (QQ l O 1)) * hv

theorem XX_QQ_properties : ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O], ∀ s : ℕ, 1 ≤ s → phi l O (XX l O s) = XX l O s * QQ l O s ∧ (phi l O ^ (s - 1)) PowerSeries.X = XX l O s ∧ PowerSeries.constantCoeff (QQ l O s) = (l : O) ∧ (∃ b, QQ l O s = PowerSeries.X ^ (l ^ (s - 1) * (l - 1)) + (l : PowerSeries O) * b) ∧ (∃ b, QQ l O s = (l : PowerSeries O) + XX l O s * b) ∧ (∀ c : ℤ_[l]ˣ, (∃ b, act l O c (XX l O s) = XX l O s * (PowerSeries.C (algebraMap ℤ_[l] O c) + XX l O s * b)) ∧ ∃ b, act l O c (QQ l O s) = QQ l O s * (1 + XX l O s * b)) ∧ ∀ (u w : ℤ_[l]), u = 1 + (l : ℤ_[l]) ^ s * w → ∀ a, ∃ b, act l O u a - a = XX l O s * QQ l O s * b := by
  intro l _ O _ _ s hs
  have hp : l.Prime := Fact.out
  have hψ : act l O ((l ^ (s - 1) : ℕ) : ℤ_[l]) PowerSeries.X = XX l O s := act_nat_X l O _
  have hψQ : act l O ((l ^ (s - 1) : ℕ) : ℤ_[l]) (QQ l O 1) = QQ l O s := by
    have : XX l O 1 = PowerSeries.X := by simp [XX]
    simp only [QQ, this, map_sum, map_pow, map_add, map_one, hψ]
  have h0 : PowerSeries.constantCoeff (XX l O s) = 0 := by simp [XX]
  refine ⟨?_, phi_pow_X l O _, ?_, ?_, ?_, fun c => ⟨?_, ?_⟩, ?_⟩
  · rw [XX_mul_QQ' l O s hs, XX]
    simp only [map_sub, map_pow, map_add, map_one, phi, act_nat_X]
    rw [add_sub_cancel, ← pow_mul, ← pow_succ', Nat.sub_add_cancel hs]
  · simp [QQ, map_sum, h0]
  · obtain ⟨r, hr⟩ := geom_sum_one_add_prime hp (XX l O s)
    obtain ⟨t, ht⟩ := exists_add_pow_prime_pow_eq hp (PowerSeries.X : PowerSeries O) 1 (s - 1)
    have h1 : (l : PowerSeries O) ∣ XX l O s - PowerSeries.X ^ l ^ (s - 1) :=
      ⟨PowerSeries.X * t, by rw [XX, add_comm, ht]; ring⟩
    obtain ⟨q, hq⟩ := h1.trans (sub_dvd_pow_sub_pow _ _ (l - 1))
    refine ⟨q + r, ?_⟩
    rw [QQ, hr, pow_mul]
    linear_combination hq
  · have : XX l O s ∣ QQ l O s - l := by
      have e : QQ l O s - l = ∑ k ∈ Finset.range l, ((1 + XX l O s) ^ k - 1) := by
        simp [QQ, Finset.sum_sub_distrib]
      rw [e]
      refine Finset.dvd_sum fun k _ => ?_
      simpa using sub_one_dvd_pow_sub_one (1 + XX l O s) k
    obtain ⟨b, hb⟩ := this
    exact ⟨b, by linear_combination hb⟩
  · obtain ⟨b, hb⟩ := cyc_eq_X_mul l O c
    refine ⟨act l O ((l ^ (s - 1) : ℕ) : ℤ_[l]) b, ?_⟩
    conv_lhs => rw [← hψ, act_comm', act_X_eq, hb]
    simp only [map_mul, map_add, act_C, hψ]
  · obtain ⟨b, hb⟩ := act_QQ_one l O c
    refine ⟨act l O ((l ^ (s - 1) : ℕ) : ℤ_[l]) b, ?_⟩
    conv_lhs => rw [← hψQ, act_comm', hb]
    simp only [map_mul, map_add, map_one, hψ, hψQ]
  · intro u w hu a
    have hX : PowerSeries.X ∣ act l O u PowerSeries.X := by
      rw [act_X_eq, PowerSeries.X_dvd_iff]; exact cyc_const l O u
    refine Dvd.dvd.trans ?_ (algHom_sub_dvd (act l O u) hX a)
    obtain ⟨b, hb⟩ := cyc_eq_X_mul l O w
    have h1 : cyc l O (((l ^ s : ℕ) : ℤ_[l]) * w) = XX l O s * QQ l O s *
        act l O ((l ^ s : ℕ) : ℤ_[l]) (PowerSeries.C (algebraMap ℤ_[l] O w) + PowerSeries.X * b) := by
      rw [← act_X_eq, ← (GlobalTheory.Cyc.act_laws l O).2.1, act_X_eq l O w, hb, map_mul, act_nat_X,
        XX_mul_QQ' l O s hs]
    have h2 : cyc l O u + 1 = (cyc l O ((1 : ℕ) : ℤ_[l]) + 1) * (cyc l O (((l ^ s : ℕ) : ℤ_[l]) * w) + 1) := by
      simp only [cyc, sub_add_cancel]
      rw [← map_mul, ← PowerSeries.binomialSeries_add, hu]
      push_cast
      rfl
    rw [(GlobalTheory.Cyc.act_laws l O).2.2.2.1, h1] at h2
    rw [act_X_eq]
    exact ⟨(1 + PowerSeries.X) * act l O ((l ^ s : ℕ) : ℤ_[l])
      (PowerSeries.C (algebraMap ℤ_[l] O w) + PowerSeries.X * b), by linear_combination h2⟩

end GlobalTheory.Cyc
