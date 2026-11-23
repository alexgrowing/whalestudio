import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ImagePolynomialAction
open PowerSeries GlobalTheory.BK

noncomputable section
namespace GlobalTheory.BK.SDec

open Filter Topology

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] (l : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K]

omit [IsUltrametricDist K] in
theorem norm_factorial_eq_one {k : ℕ} (hk : k < l) : ‖(k.factorial : K)‖ = 1 := by
  rw [norm_natCast_eq l, Padic.norm_natCast_eq_one_iff]
  exact (Nat.Prime.coprime_iff_not_dvd Fact.out).2 fun h =>
    absurd ((Nat.Prime.dvd_factorial Fact.out).1 h) (not_le.2 hk)

omit [IsUltrametricDist K] in
theorem norm_choose_mul_le (q k : ℕ) :
    ‖((q.choose k : K) * (k.factorial : K) * (-(l : K)) ^ (q - k))‖ ≤ ‖(q.factorial : K)‖ := by
  rcases le_or_gt k q with hkq | hkq
  · have h := congrArg (Nat.cast : ℕ → K) (Nat.choose_mul_factorial_mul_factorial hkq)
    push_cast at h
    rw [← h, norm_mul, norm_mul, norm_pow, norm_neg, norm_mul, norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_pow_le_norm_factorial l _)
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  · simp [Nat.choose_eq_zero_of_lt hkq]

variable (K) in

def beta (e : ℕ) (c : K) (m k : ℕ) : K :=
  c * (((m / e).choose k : K) * (k.factorial : K) * (-(l : K)) ^ (m / e - k))

theorem norm_beta_le (e : ℕ) (c : K) (m k : ℕ) : ‖beta K l e c m k‖ ≤ ‖c‖ * wS K e m := by
  rw [beta, norm_mul, wS]
  exact mul_le_mul_of_nonneg_left (norm_choose_mul_le l _ _) (norm_nonneg _)

theorem beta_eq_zero {e : ℕ} (c : K) {m k : ℕ} (h : m / e < k) : beta K l e c m k = 0 := by
  simp [beta, Nat.choose_eq_zero_of_lt h]

theorem expand (e : ℕ) (c : K) (m N : ℕ) (hN : m / e < N) :
    C c * X ^ m = ∑ k ∈ Finset.range N, C (beta K l e c m k) * X ^ (m % e) * Ediv K l e k := by
  have hX : (X : K⟦X⟧) ^ m = X ^ (m % e) * (E K l e + C (-(l : K))) ^ (m / e) := by
    rw [E, map_neg, map_natCast, add_neg_cancel_right, ← pow_mul, ← pow_add, Nat.mod_add_div]
  rw [← Finset.sum_subset (Finset.range_mono (Nat.succ_le_of_lt hN)) (fun k _ hk => by
      rw [beta_eq_zero l c (by simpa using hk), map_zero, zero_mul, zero_mul])]
  rw [hX, add_pow, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hk : (k.factorial : K) ≠ 0 := natCast_ne_zero' l k.factorial_ne_zero
  have h1 : C (beta K l e c m k) * C ((k.factorial : K)⁻¹) =
      C (c * (((m / e).choose k : K) * (-(l : K)) ^ (m / e - k))) := by
    rw [← map_mul]; congr 1; rw [beta]; field_simp
  calc _ = C (c * (((m / e).choose k : K) * (-(l : K)) ^ (m / e - k))) * X ^ (m % e) *
        E K l e ^ k := by simp only [map_mul, map_pow, map_natCast, map_neg]; ring
    _ = _ := by rw [Ediv, ← h1]; ring

end GlobalTheory.BK.SDec

namespace GlobalTheory.BK.SDec

open Filter Topology

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] (l : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K]

omit [Fact l.Prime] [NormedAlgebra ℚ_[l] K] in
theorem C_mem_A {c : K} (hc : ‖c‖ ≤ 1) : C c ∈ A O K := fun n => by
  rw [coeff_C]; split_ifs <;> simp [hc]

theorem term_mem_A (e : ℕ) {c : K} (hc : ‖c‖ ≤ 1) (r : ℕ) {k : ℕ} (hk : k < l) :
    C c * X ^ r * Ediv K l e k ∈ A O K := by
  rw [Ediv]
  refine (A O K).mul_mem ((A O K).mul_mem (C_mem_A hc) ((A O K).pow_mem HasU.X_mem r))
    ((A O K).mul_mem (C_mem_A ?_) ((A O K).pow_mem (E_mem l e (A O K)) k))
  rw [norm_inv, norm_factorial_eq_one l hk, inv_one]

theorem CX_mem_S {e : ℕ} {c : K} (hc : ‖c‖ ≤ 1) {r : ℕ} (hr : r < e) :
    C c * X ^ r ∈ S O K e := by
  rw [← monomial_eq_C_mul_X_pow]
  refine monomial_mem_S ?_
  rw [wS, Nat.div_eq_of_lt hr, Nat.factorial_zero, Nat.cast_one, norm_one, mul_one]
  exact hc

theorem sum_range_mul {M : Type*} [AddCommMonoid M] (F : ℕ → M) (Q e : ℕ) :
    ∑ m ∈ Finset.range (Q * e), F m = ∑ q ∈ Finset.range Q, ∑ r ∈ Finset.range e, F (q * e + r) := by
  induction Q with
  | zero => simp
  | succ Q ih => rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]

theorem low_eq (e j Q : ℕ) (b : ℕ → ℕ → K) :
    ∑ m ∈ Finset.range (Q * e), ∑ k ∈ Finset.range j, C (b m k) * X ^ (m % e) * Ediv K l e k =
      ∑ k ∈ Finset.range j, ∑ r ∈ Finset.range e,
        C (∑ q ∈ Finset.range Q, b (q * e + r) k) * X ^ r * Ediv K l e k := by
  rw [sum_range_mul]
  simp_rw [map_sum, Finset.sum_mul]
  calc _ = ∑ q ∈ Finset.range Q, ∑ r ∈ Finset.range e, ∑ k ∈ Finset.range j,
        C (b (q * e + r) k) * X ^ r * Ediv K l e k :=
      Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun r hr => Finset.sum_congr rfl
        fun k _ => by
          rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (Finset.mem_range.1 hr)]
    _ = ∑ r ∈ Finset.range e, ∑ q ∈ Finset.range Q, ∑ k ∈ Finset.range j,
        C (b (q * e + r) k) * X ^ r * Ediv K l e k := Finset.sum_comm
    _ = ∑ r ∈ Finset.range e, ∑ k ∈ Finset.range j, ∑ q ∈ Finset.range Q,
        C (b (q * e + r) k) * X ^ r * Ediv K l e k :=
      Finset.sum_congr rfl fun r _ => Finset.sum_comm
    _ = _ := Finset.sum_comm

theorem coeff_head (f : K⟦X⟧) (M m : ℕ) :
    coeff m (∑ m' ∈ Finset.range M, C (coeff m' f) * X ^ m') = if m < M then coeff m f else 0 := by
  simp_rw [map_sum, coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  simp

end GlobalTheory.BK.SDec

namespace GlobalTheory.BK.SDec

open Filter Topology

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] (l : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K]

theorem tail_mem {e : ℕ} {f : K⟦X⟧} (hf : f ∈ S O K e) (n M : ℕ)
    (hM : ∀ m, M ≤ m → ‖coeff m f‖ * wS K e m ≤ ‖(l : K)‖ ^ n) :
    C ((l : K) ^ n)⁻¹ * (f - ∑ m ∈ Finset.range M, C (coeff m f) * X ^ m) ∈ S O K e := by
  have hl : 0 < ‖(l : K)‖ ^ n := pow_pos (norm_pos_iff.2 (l_ne_zero l)) n
  have hc : ∀ m, coeff m (C ((l : K) ^ n)⁻¹ * (f - ∑ m ∈ Finset.range M, C (coeff m f) * X ^ m)) =
      ((l : K) ^ n)⁻¹ * (if m < M then 0 else coeff m f) := fun m => by
    rw [coeff_C_mul, map_sub, coeff_head]; split_ifs <;> simp
  have key : ∀ m, ‖coeff m (C ((l : K) ^ n)⁻¹ * (f - ∑ m ∈ Finset.range M, C (coeff m f) * X ^ m))‖ *
      wS K e m ≤ (‖(l : K)‖ ^ n)⁻¹ * (‖coeff m f‖ * wS K e m) := fun m => by
    rw [hc, norm_mul, norm_inv, norm_pow, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hl.le)
    split_ifs
    · simpa using mul_nonneg (norm_nonneg _) (wS_nonneg e m)
    · exact le_rfl
  refine ⟨fun m => ?_, squeeze_zero (fun m => mul_nonneg (norm_nonneg _) (wS_nonneg e m)) key
    (by simpa using hf.2.const_mul (‖(l : K)‖ ^ n)⁻¹)⟩
  by_cases h : m < M
  · rw [hc, if_pos h]; simp
  · refine (key m).trans ?_
    rw [inv_mul_le_iff₀ hl, mul_one]
    exact hM m (not_lt.1 h)

theorem S_eq_A_add_Fil : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e : ℕ) [Fact l.Prime]
    [NormedAlgebra ℚ_[l] K] [NeZero e] (j : ℕ), j < l → ∀ f ∈ S O K e,
    ∃ g ∈ A O K, ∃ φ ∈ Fil O K l e j, f = g + (φ : K⟦X⟧) := by
  intro O K _ _ _ _ _ _ l e _ _ _ j hj f hf
  have hb : ∀ m k, ‖beta K l e (coeff m f) m k‖ ≤ ‖coeff m f‖ * wS K e m := fun m k =>
    norm_beta_le l e _ m k
  have hT : Tendsto (fun m => ‖coeff m f‖ * wS K e m) atTop (𝓝 0) := hf.2
  have hle : ∀ q r, q ≤ q * e + r := fun q r =>
    (Nat.le_mul_of_pos_right q (NeZero.pos e)).trans (Nat.le_add_right _ _)
  have hs : ∀ r k, Summable fun q => beta K l e (coeff (q * e + r) f) (q * e + r) k := by
    intro r k
    refine NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ?_
    rw [Nat.cofinite_eq_atTop]
    exact squeeze_zero_norm (fun q => hb _ _)
      (hT.comp (tendsto_atTop_mono (fun q => hle q r) tendsto_id))
  set γ : ℕ → ℕ → K := fun r k => ∑' q, beta K l e (coeff (q * e + r) f) (q * e + r) k with hγ
  have hγ1 : ∀ r k, ‖γ r k‖ ≤ 1 := fun r k =>
    IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg zero_le_one fun q => (hb _ _).trans (hf.1 _)
  set g : K⟦X⟧ := ∑ k ∈ Finset.range j, ∑ r ∈ Finset.range e, C (γ r k) * X ^ r * Ediv K l e k
    with hgdef
  have hg : g ∈ A O K := Subalgebra.sum_mem _ fun k hk => Subalgebra.sum_mem _ fun r _ =>
    term_mem_A l e (hγ1 r k) r ((Finset.mem_range.1 hk).trans hj)
  have hφS : f - g ∈ S O K e := Subalgebra.sub_mem _ hf (A_le_S l e hg)
  refine ⟨g, hg, ⟨f - g, hφS⟩, ?_, by simp⟩
  rw [mem_Fil]
  intro n
  have hpos : 0 < ‖(l : K)‖ ^ n := pow_pos (norm_pos_iff.2 (l_ne_zero l)) n
  obtain ⟨Q, hQ⟩ := eventually_atTop.1 (hT.eventually (ge_mem_nhds hpos))
  have hQ' : ∀ m, Q * e ≤ m → ‖coeff m f‖ * wS K e m ≤ ‖(l : K)‖ ^ n := fun m hm =>
    hQ m ((Nat.le_mul_of_pos_right Q (NeZero.pos e)).trans hm)
  set P : K⟦X⟧ := ∑ m ∈ Finset.range (Q * e), C (coeff m f) * X ^ m with hPdef
  set T : ℕ → ℕ → K⟦X⟧ := fun m k => C (beta K l e (coeff m f) m k) * X ^ (m % e) * Ediv K l e k
    with hTdef
  have hTS : ∀ m k, C (beta K l e (coeff m f) m k) * X ^ (m % e) ∈ S O K e := fun m k =>
    CX_mem_S ((hb m k).trans (hf.1 m)) (Nat.mod_lt _ (NeZero.pos e))
  set G : S O K e := ∑ m ∈ Finset.range (Q * e), ∑ k ∈ Finset.Ico j (j + m / e + 1),
    (⟨_, hTS m k⟩ : S O K e) * ⟨Ediv K l e k, Ediv_mem_S l e k⟩ with hGdef
  have hG : G ∈ FilPre O K l e j := Ideal.sum_mem _ fun m _ => Ideal.sum_mem _ fun k hk =>
    Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨k, (Finset.mem_Ico.1 hk).1, rfl⟩)
  have hGc : (G : K⟦X⟧) = ∑ m ∈ Finset.range (Q * e), ∑ k ∈ Finset.Ico j (j + m / e + 1), T m k := by
    simp [hGdef, hTdef]
  set Low : K⟦X⟧ := ∑ m ∈ Finset.range (Q * e), ∑ k ∈ Finset.range j, T m k with hLowdef
  have hP : P = Low + G := by
    rw [hGc, hLowdef, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [expand l e _ m (j + m / e + 1) (by omega), Finset.sum_range_add_sum_Ico _ (Nat.le_add_right_of_le (Nat.le_add_right j (m / e)))]
  have hLow : Low = ∑ k ∈ Finset.range j, ∑ r ∈ Finset.range e,
      C (∑ q ∈ Finset.range Q, beta K l e (coeff (q * e + r) f) (q * e + r) k) * X ^ r *
        Ediv K l e k := low_eq l e j Q (fun m k => beta K l e (coeff m f) m k)
  set tl : ℕ → ℕ → K := fun r k => ∑' q, beta K l e (coeff ((q + Q) * e + r) f) ((q + Q) * e + r) k
    with htldef
  have htl : ∀ r k, γ r k - ∑ q ∈ Finset.range Q, beta K l e (coeff (q * e + r) f) (q * e + r) k =
      tl r k := fun r k => by
    simp only [hγ, htldef]
    rw [← (hs r k).sum_add_tsum_nat_add Q, add_sub_cancel_left]
  have htln : ∀ r k, ‖tl r k‖ ≤ ‖(l : K)‖ ^ n := fun r k =>
    IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg hpos.le fun q => (hb _ _).trans
      (hQ' _ (Nat.le_add_right_of_le (Nat.mul_le_mul_right e (Nat.le_add_left Q q))))
  have hgL : g - Low = ∑ k ∈ Finset.range j, ∑ r ∈ Finset.range e, C (tl r k) * X ^ r * Ediv K l e k := by
    rw [hgdef, hLow, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [← htl, map_sub]; ring
  set h0 : K⟦X⟧ := C ((l : K) ^ n)⁻¹ * ((f - P) - (g - Low)) with hh0
  have hh : h0 ∈ S O K e := by
    have : h0 = C ((l : K) ^ n)⁻¹ * (f - P) - ∑ k ∈ Finset.range j, ∑ r ∈ Finset.range e,
        C (((l : K) ^ n)⁻¹ * tl r k) * X ^ r * Ediv K l e k := by
      rw [hh0, hgL, mul_sub, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [map_mul]; ring
    rw [this]
    refine Subalgebra.sub_mem _ (tail_mem l hf n (Q * e) hQ') (Subalgebra.sum_mem _ fun k _ =>
      Subalgebra.sum_mem _ fun r hr => (S O K e).mul_mem (CX_mem_S ?_ (Finset.mem_range.1 hr))
        (Ediv_mem_S l e k))
    rw [norm_mul, norm_inv, norm_pow, inv_mul_le_iff₀ hpos, mul_one]
    exact htln r k
  refine ⟨G, hG, ⟨h0, hh⟩, Subtype.ext ?_⟩
  have hlC : (l : K⟦X⟧) ^ n * C ((l : K) ^ n)⁻¹ = 1 := by
    rw [← map_natCast C, ← map_pow, ← map_mul, mul_inv_cancel₀ (pow_ne_zero _ (l_ne_zero l)),
      map_one]
  simp only [Subalgebra.coe_add, Subalgebra.coe_mul, Subalgebra.coe_pow, SubringClass.coe_natCast]
  rw [hh0, ← mul_assoc, hlC, one_mul]
  linear_combination hP

end GlobalTheory.BK.SDec
