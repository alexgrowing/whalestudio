import Mathlib

noncomputable section

namespace GlobalTheory.NearlyPrimitive

open Finset Filter Topology

section Factorial

variable {C : Type} [NormedField C] [IsUltrametricDist C]

theorem norm_natCast_eq_one_of_coprime {p m : ℕ} (hp : ‖(p : C)‖ < 1) (h : Nat.Coprime p m) :
    ‖(m : C)‖ = 1 := by
  refine le_antisymm (IsUltrametricDist.norm_natCast_le_one C m) ?_
  by_contra hlt
  push Not at hlt
  have hb : ((Nat.gcd p m : ℤ) : C) = ((p * Nat.gcdA p m + m * Nat.gcdB p m : ℤ) : C) := by
    rw [← Nat.gcd_eq_gcd_ab]
  rw [h.gcd_eq_one] at hb
  push_cast at hb
  have h1 : ‖(p : C) * ((Nat.gcdA p m : ℤ) : C)‖ < 1 := by
    rw [norm_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _)
      (IsUltrametricDist.norm_intCast_le_one C _)) hp
  have h2 : ‖(m : C) * ((Nat.gcdB p m : ℤ) : C)‖ < 1 := by
    rw [norm_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _)
      (IsUltrametricDist.norm_intCast_le_one C _)) hlt
  have h3 := (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt h1 h2)
  rw [← hb, norm_one] at h3
  exact lt_irrefl _ h3

theorem norm_factorial_inv_le (p : ℕ) [hp : Fact p.Prime] (h : ‖(p : C)‖ = (p : ℝ)⁻¹) (n : ℕ) :
    ‖((n.factorial : C))⁻¹‖ ≤ ((p : ℝ) ^ (1 / ((p : ℝ) - 1))) ^ n := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hlt : ‖(p : C)‖ < 1 := by rw [h]; exact inv_lt_one_of_one_lt₀ hp1
  obtain ⟨v, m, hm, hv⟩ := Nat.exists_eq_pow_mul_and_not_dvd (Nat.factorial_ne_zero n) p
    hp.out.ne_one
  have hval : padicValNat p n.factorial = v := by
    have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero _)
    rw [hv, padicValNat.mul (pow_ne_zero _ hp.out.ne_zero) hm0, padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd hm, add_zero]
  have hle : (p - 1) * v ≤ n := by
    rw [← hval, sub_one_mul_padicValNat_factorial]
    exact Nat.sub_le _ _
  have hle' : ((p : ℝ) - 1) * v ≤ n := by
    have : (((p - 1) * v : ℕ) : ℝ) ≤ n := by exact_mod_cast hle
    rwa [Nat.cast_mul, Nat.cast_sub hp.out.one_le, Nat.cast_one] at this
  have hm1 : ‖(m : C)‖ = 1 :=
    norm_natCast_eq_one_of_coprime hlt ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hm)
  rw [norm_inv, hv, Nat.cast_mul, Nat.cast_pow, norm_mul, norm_pow, hm1, h, mul_one, inv_pow,
    inv_inv, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
  refine Real.rpow_le_rpow_of_exponent_le hp1.le ?_
  rw [one_div, inv_mul_eq_div, le_div_iff₀ (by linarith)]
  linarith

end Factorial

def dpow (C : Type) [Field C] {B : Type} [CommRing B] [Algebra C B] (n : ℕ) (x : B) : B :=
  ((n.factorial : C))⁻¹ • x ^ n

theorem dpow_add {C : Type} [Field C] [CharZero C] {B : Type} [CommRing B] [Algebra C B]
    (n : ℕ) (x y : B) :
    dpow C n (x + y) = ∑ m ∈ antidiagonal n, dpow C m.1 x * dpow C m.2 y := by
  unfold dpow
  rw [(Commute.all x y).add_pow', Finset.smul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm' := Finset.HasAntidiagonal.mem_antidiagonal.mp hm
  rw [smul_mul_smul_comm, ← Nat.cast_smul_eq_nsmul C, smul_smul]
  congr 1
  have h := Nat.choose_mul_factorial_mul_factorial (n := n) (k := m.1) (by omega)
  rw [show n - m.1 = m.2 by omega] at h
  have h' : (n.choose m.1 : C) * m.1.factorial * m.2.factorial = n.factorial := by
    exact_mod_cast h
  have h1 : (m.1.factorial : C) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have h2 : (m.2.factorial : C) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have h3 : (n.factorial : C) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  field_simp
  linear_combination h'

theorem map_dpow {C : Type} [Field C] {B B' : Type} [CommRing B] [Algebra C B] [CommRing B']
    [Algebra C B'] (f : B →ₐ[C] B') (n : ℕ) (x : B) : f (dpow C n x) = dpow C n (f x) := by
  simp [dpow]

theorem sum_lt {B ι : Type} [AddCommGroup B] (N : B → ℝ) (h0 : N 0 = 0)
    (hadd : ∀ x y, N (x + y) ≤ max (N x) (N y)) {T : ℝ} (hT : 0 < T) (s : Finset ι) (f : ι → B)
    (hf : ∀ i ∈ s, N (f i) < T) : N (∑ i ∈ s, f i) < T := by
  refine Finset.sum_induction f (fun x => N x < T) (fun a b ha hb => ?_) (by rwa [h0]) hf
  exact (hadd a b).trans_lt (max_lt ha hb)

theorem sum_le {B ι : Type} [AddCommGroup B] (N : B → ℝ) (h0 : N 0 = 0)
    (hadd : ∀ x y, N (x + y) ≤ max (N x) (N y)) {T : ℝ} (hT : 0 ≤ T) (s : Finset ι) (f : ι → B)
    (hf : ∀ i ∈ s, N (f i) ≤ T) : N (∑ i ∈ s, f i) ≤ T := by
  refine Finset.sum_induction f (fun x => N x ≤ T) (fun a b ha hb => ?_) (by rwa [h0]) hf
  exact (hadd a b).trans (max_le ha hb)

theorem exists_last_max (t : ℕ → ℝ) (ht : Tendsto t atTop (𝓝 0)) (n : ℕ) (hn : 1 < t n) :
    ∃ k, 1 < t k ∧ (∀ a, t a ≤ t k) ∧ ∀ a, k < a → t a < t k := by
  obtain ⟨M, hM⟩ := eventually_atTop.1 (ht.eventually (gt_mem_nhds (zero_lt_one' ℝ)))
  have hnM : n ∈ range M := by
    rw [mem_range]
    by_contra h
    exact absurd (hM n (not_lt.1 h)) (not_lt.2 hn.le)
  obtain ⟨k₀, hk₀, hmax⟩ := Finset.exists_max_image (range M) t ⟨n, hnM⟩
  obtain ⟨k, hk, hlast⟩ := Finset.exists_max_image ((range M).filter fun a => t a = t k₀) id
    ⟨k₀, by simp [mem_range.1 hk₀]⟩
  rw [mem_filter] at hk
  have h1 : 1 < t k := by rw [hk.2]; exact hn.trans_le (hmax n hnM)
  have hall : ∀ a, t a ≤ t k := fun a => by
    by_cases ha : a < M
    · rw [hk.2]; exact hmax a (mem_range.2 ha)
    · exact ((hM a (not_lt.1 ha)).trans h1).le
  refine ⟨k, h1, hall, fun a hka => ?_⟩
  by_cases ha : a < M
  · refine lt_of_le_of_ne (hall a) fun h => ?_
    have := hlast a (by rw [mem_filter]; exact ⟨mem_range.2 ha, h.trans hk.2⟩)
    exact absurd hka (not_lt.2 this)
  · exact (hM a (not_lt.1 ha)).trans h1

theorem norm_smul_le_one_of_lt (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C]
    [CharZero C] (p : ℕ) [hp : Fact p.Prime] (hpn : ‖(p : C)‖ = (p : ℝ)⁻¹)
    (B₁ B₂ : Type) [CommRing B₁] [Algebra C B₁] [CommRing B₂] [Algebra C B₂]
    (N₁ : B₁ → ℝ) (N₂ : B₂ → ℝ) (Δ i j : B₁ →ₐ[C] B₂)
    (hs₁ : ∀ (c : C) x, N₁ (c • x) = ‖c‖ * N₁ x) (hs₂ : ∀ (c : C) x, N₂ (c • x) = ‖c‖ * N₂ x)
    (hn₁ : ∀ x, 0 ≤ N₁ x) (hn₂ : ∀ x, 0 ≤ N₂ x)
    (hadd : ∀ x y, N₂ (x + y) ≤ max (N₂ x) (N₂ y)) (hmul : ∀ x y, N₂ (x * y) ≤ N₂ x * N₂ y)
    (hΔ : ∀ x, N₂ (Δ x) ≤ N₁ x) (hij : ∀ x y, N₂ (i x * j y) = N₁ x * N₁ y)
    (y : B₁) (K : ℝ) (hK : ∀ k : ℕ, N₁ (y ^ k) ≤ K) (he : N₂ (Δ y - i y - j y) ≤ 1)
    (c : C) (hc : ‖c‖ < (p : ℝ) ^ (-(1 / ((p : ℝ) - 1)))) : N₁ (c • y) ≤ 1 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  set q : ℝ := (p : ℝ) ^ (1 / ((p : ℝ) - 1)) with hq
  have hq0 : 0 < q := Real.rpow_pos_of_pos hp0 _
  set ρ : ℝ := q * ‖c‖ with hρ
  have hρ0 : 0 ≤ ρ := mul_nonneg hq0.le (norm_nonneg _)
  have hρ1 : ρ < 1 := by
    rw [Real.rpow_neg hp0.le, ← hq] at hc
    calc ρ < q * q⁻¹ := mul_lt_mul_of_pos_left hc hq0
      _ = 1 := mul_inv_cancel₀ hq0.ne'
  have hcoef : ∀ n : ℕ, ‖((n.factorial : C))⁻¹‖ * ‖c ^ n‖ ≤ ρ ^ n := fun n => by
    rw [hρ, mul_pow, norm_pow]
    exact mul_le_mul_of_nonneg_right (norm_factorial_inv_le p hpn n) (by positivity)
  have h0 : N₂ 0 = 0 := by simpa using hs₂ 0 0
  have hneg : ∀ x, N₂ (-x) = N₂ x := fun x => by simpa using hs₂ (-1) x
  set e := Δ y - i y - j y with hedef
  have hepow : ∀ l : ℕ, N₂ (e ^ (l + 1)) ≤ 1 := fun l => by
    induction l with
    | zero => simpa using he
    | succ l ih =>
      rw [pow_succ]
      exact (hmul _ _).trans (mul_le_one₀ ih (hn₂ _) he)
  have hd : ∀ l : ℕ, l ≠ 0 → N₂ (dpow C l (c • e)) < 1 := fun l hl => by
    obtain ⟨l', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hl
    rw [dpow, smul_pow, hs₂, hs₂, ← mul_assoc]
    calc _ ≤ ρ ^ (l' + 1) * 1 := mul_le_mul (hcoef _) (hepow _) (hn₂ _) (by positivity)
      _ < 1 := by rw [mul_one]; exact pow_lt_one₀ hρ0 hρ1 hl
  set t : ℕ → ℝ := fun n => N₁ (dpow C n (c • y)) with ht
  have ht0 : ∀ n, 0 ≤ t n := fun n => hn₁ _
  have htle : ∀ n, t n ≤ ρ ^ n * K := fun n => by
    simp only [ht]
    rw [dpow, smul_pow, hs₁, hs₁, ← mul_assoc]
    exact mul_le_mul (hcoef _) (hK _) (hn₁ _) (by positivity)
  have hlim : Tendsto t atTop (𝓝 0) := by
    refine squeeze_zero ht0 htle ?_
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).mul_const K
  by_contra hcon
  have h1 : 1 < t 1 := by simpa [ht, dpow] using hcon
  obtain ⟨k, hk1, hmax, hlast⟩ := exists_last_max t hlim 1 h1
  have hk0 : 0 < t k := by linarith
  have hT : 0 < t k * t k := mul_pos hk0 hk0
  set s := i (c • y) + j (c • y) with hsdef
  have hγs : ∀ m, dpow C m s =
      ∑ x ∈ antidiagonal m, i (dpow C x.1 (c • y)) * j (dpow C x.2 (c • y)) := fun m => by
    rw [hsdef, dpow_add]
    simp only [map_dpow]
  have hsle : ∀ m, N₂ (dpow C m s) ≤ t k * t k := fun m => by
    rw [hγs]
    refine sum_le N₂ h0 hadd hT.le _ _ fun x _ => ?_
    rw [hij]
    exact mul_le_mul (hmax _) (hmax _) (ht0 _) hk0.le
  have hΔz : Δ (c • y) = s + c • e := by
    simp only [hsdef, hedef, map_smul, smul_sub]
    abel
  have hkk : (k, k) ∈ antidiagonal (k + k) := by simp
  have h2k : (k + k, 0) ∈ antidiagonal (k + k) := by simp
  have E1 := dpow_add (C := C) (k + k) s (c • e)
  rw [← hΔz, ← map_dpow, ← Finset.add_sum_erase _ _ h2k] at E1
  have E2 := hγs (k + k)
  rw [← Finset.add_sum_erase _ _ hkk] at E2
  have hz : dpow C 0 (c • e) = 1 := by simp [dpow]
  simp only [hz, mul_one] at E1 E2
  have hA : N₂ (Δ (dpow C (k + k) (c • y))) < t k * t k := by
    refine (hΔ _).trans_lt ((hmax (k + k)).trans_lt ?_)
    nlinarith
  have hB : N₂ (∑ x ∈ (antidiagonal (k + k)).erase (k + k, 0),
      dpow C x.1 s * dpow C x.2 (c • e)) < t k * t k := by
    refine sum_lt N₂ h0 hadd hT _ _ fun x hx => ?_
    rw [mem_erase, Finset.HasAntidiagonal.mem_antidiagonal] at hx
    have hx2 : x.2 ≠ 0 := fun h => hx.1 (Prod.ext (by have := hx.2; simp only; omega) h)
    calc _ ≤ N₂ (dpow C x.1 s) * N₂ (dpow C x.2 (c • e)) := hmul _ _
      _ ≤ t k * t k * N₂ (dpow C x.2 (c • e)) := mul_le_mul_of_nonneg_right (hsle _) (hn₂ _)
      _ < t k * t k := mul_lt_of_lt_one_right hT (hd _ hx2)
  have hC : N₂ (∑ x ∈ (antidiagonal (k + k)).erase (k, k),
      i (dpow C x.1 (c • y)) * j (dpow C x.2 (c • y))) < t k * t k := by
    refine sum_lt N₂ h0 hadd hT _ _ fun x hx => ?_
    rw [mem_erase, Finset.HasAntidiagonal.mem_antidiagonal] at hx
    rw [hij]
    change t x.1 * t x.2 < _
    have : k < x.1 ∨ k < x.2 := by
      by_contra h
      push Not at h
      have := hx.2
      exact hx.1 (Prod.ext (by simp only; omega) (by simp only; omega))
    rcases this with h | h
    · exact (mul_le_mul_of_nonneg_left (hmax _) (ht0 _)).trans_lt
        (mul_lt_mul_of_pos_right (hlast _ h) hk0)
    · exact mul_lt_mul' (hmax _) (hlast _ h) (ht0 _) hk0
  have E3 : i (dpow C k (c • y)) * j (dpow C k (c • y)) =
      Δ (dpow C (k + k) (c • y)) + -(∑ x ∈ (antidiagonal (k + k)).erase (k + k, 0),
      dpow C x.1 s * dpow C x.2 (c • e)) + -(∑ x ∈ (antidiagonal (k + k)).erase (k, k),
      i (dpow C x.1 (c • y)) * j (dpow C x.2 (c • y))) := by
    rw [E1, E2]; abel
  have hfin : N₂ (i (dpow C k (c • y)) * j (dpow C k (c • y))) < t k * t k := by
    rw [E3]
    refine (hadd _ _).trans_lt (max_lt ((hadd _ _).trans_lt (max_lt hA ?_)) ?_)
    · rwa [hneg]
    · rwa [hneg]
  rw [hij] at hfin
  exact lt_irrefl _ hfin

theorem norm_smul_le_one : ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C] [CharZero C] (p : ℕ) [Fact p.Prime], ‖(p : C)‖ = (p : ℝ)⁻¹ → ∀ (B₁ B₂ : Type) [CommRing B₁] [Algebra C B₁] [CommRing B₂] [Algebra C B₂] (N₁ : B₁ → ℝ) (N₂ : B₂ → ℝ) (Δ i j : B₁ →ₐ[C] B₂), (∀ (c : C) x, N₁ (c • x) = ‖c‖ * N₁ x) → (∀ (c : C) x, N₂ (c • x) = ‖c‖ * N₂ x) → (∀ x, 0 ≤ N₁ x) → (∀ x, 0 ≤ N₂ x) → (∀ x y, N₂ (x + y) ≤ max (N₂ x) (N₂ y)) → (∀ x y, N₂ (x * y) ≤ N₂ x * N₂ y) → (∀ x, N₂ (Δ x) ≤ N₁ x) → (∀ x y, N₂ (i x * j y) = N₁ x * N₁ y) → ∀ y : B₁, (∃ K : ℝ, ∀ k : ℕ, N₁ (y ^ k) ≤ K) → N₂ (Δ y - i y - j y) ≤ 1 → ∀ a : C, ‖a‖ ≤ (p : ℝ) ^ (-(1 / ((p : ℝ) - 1))) → N₁ (a • y) ≤ 1 := by
  intro C _ _ _ _ p hp hpn B₁ B₂ _ _ _ _ N₁ N₂ Δ i j hs₁ hs₂ hn₁ hn₂ hadd hmul hΔ hij y ⟨K, hK⟩
    he a ha
  by_contra hcon
  push Not at hcon
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (p : ℝ) hcon
  have hn0 : n ≠ 0 := by rintro rfl; rw [pow_zero] at hn; linarith
  obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq (p : C) (Nat.pos_of_ne_zero hn0)
  have hbn : ‖b‖ ^ n = (p : ℝ)⁻¹ := by rw [← norm_pow, hb, hpn]
  have hb1 : ‖b‖ < 1 := by
    rw [← pow_lt_one_iff_of_nonneg (norm_nonneg b) hn0, hbn]
    exact inv_lt_one_of_one_lt₀ hp1
  have hpos : 0 < (p : ℝ) ^ (-(1 / ((p : ℝ) - 1))) := Real.rpow_pos_of_pos (by linarith) _
  have hc : ‖b * a‖ < (p : ℝ) ^ (-(1 / ((p : ℝ) - 1))) := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left ha (norm_nonneg b)).trans_lt
      (mul_lt_of_lt_one_left hpos hb1)
  have h := norm_smul_le_one_of_lt C p hpn B₁ B₂ N₁ N₂ Δ i j hs₁ hs₂ hn₁ hn₂ hadd hmul hΔ hij y K
    hK he (b * a) hc
  rw [mul_smul, hs₁] at h
  have h2 := pow_le_one₀ (n := n) (mul_nonneg (norm_nonneg b) (hn₁ _)) h
  rw [mul_pow, hbn, inv_mul_le_iff₀ (by linarith), mul_one] at h2
  linarith

end GlobalTheory.NearlyPrimitive
