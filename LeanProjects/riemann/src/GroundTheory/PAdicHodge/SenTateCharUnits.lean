import Mathlib
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

namespace SenTateChar

variable (p : ℕ) [hp : Fact p.Prime]

def unitsOneAdd (k : ℕ) : Subgroup ℤ_[p]ˣ where
  carrier := {u | (p : ℤ_[p]) ^ k ∣ (u : ℤ_[p]) - 1}
  one_mem' := by simp
  mul_mem' := fun {a b} ha hb => by
    have e : ((a * b : ℤ_[p]ˣ) : ℤ_[p]) - 1 =
        (a : ℤ_[p]) * ((b : ℤ_[p]) - 1) + ((a : ℤ_[p]) - 1) := by push_cast; ring
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rw [e]
    exact dvd_add (dvd_mul_of_dvd_right hb _) ha
  inv_mem' := fun {a} ha => by
    have e : ((a⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) - 1 = -(((a⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * ((a : ℤ_[p]) - 1)) := by
      rw [mul_sub, Units.inv_mul, mul_one]; ring
    simp only [Set.mem_ofPred_eq] at ha ⊢
    rw [e]
    exact (dvd_mul_of_dvd_right ha _).neg_right

variable {p}

theorem mem_unitsOneAdd {k : ℕ} {u : ℤ_[p]ˣ} :
    u ∈ unitsOneAdd p k ↔ (p : ℤ_[p]) ^ k ∣ (u : ℤ_[p]) - 1 := Iff.rfl

theorem unitsOneAdd_antitone : Antitone (unitsOneAdd p) := fun _ _ h _ hu =>
  (pow_dvd_pow _ h).trans hu

@[simp]
theorem unitsOneAdd_zero : unitsOneAdd p 0 = ⊤ := by
  ext u; simp [mem_unitsOneAdd]

theorem eq_one_of_forall_mem_unitsOneAdd {u : ℤ_[p]ˣ} (hu : ∀ k, u ∈ unitsOneAdd p k) : u = 1 := by
  by_contra hne
  have h0 : (u : ℤ_[p]) - 1 ≠ 0 := by
    intro h; apply hne; ext; simpa [sub_eq_zero] using h
  have h := (PadicInt.mem_span_pow_iff_le_valuation _ h0 (((u : ℤ_[p]) - 1).valuation + 1)).1
    (Ideal.mem_span_singleton.2 (hu _))
  omega

theorem mem_unitsOneAdd_iff_norm {k : ℕ} {u : ℤ_[p]ˣ} :
    u ∈ unitsOneAdd p k ↔ ‖(u : ℤ_[p]) - 1‖ ≤ (p : ℝ) ^ (-(k : ℤ)) := by
  rw [mem_unitsOneAdd, PadicInt.norm_le_pow_iff_mem_span_pow, Ideal.mem_span_singleton]

theorem isOpen_unitsOneAdd (k : ℕ) : IsOpen (unitsOneAdd p k : Set ℤ_[p]ˣ) := by
  have hr : (p : ℝ) ^ (-(k : ℤ)) ≠ 0 := zpow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)
  have hset : (unitsOneAdd p k : Set ℤ_[p]ˣ) =
      (fun u : ℤ_[p]ˣ => (u : ℤ_[p])) ⁻¹' Metric.closedBall (1 : ℤ_[p]) ((p : ℝ) ^ (-(k : ℤ))) := by
    ext u
    simp only [SetLike.mem_coe, Set.mem_preimage, Metric.mem_closedBall, dist_eq_norm]
    exact mem_unitsOneAdd_iff_norm
  rw [hset]
  exact (IsUltrametricDist.isOpen_closedBall _ hr).preimage Units.continuous_val

theorem dvd_one_add_pow_sub {k : ℕ} (hk : 2 ≤ k) {x : ℤ_[p]} (hx : (p : ℤ_[p]) ^ k ∣ x) :
    (p : ℤ_[p]) ^ (k + 2) ∣ (1 + x) ^ p - 1 - p * x := by
  obtain ⟨c, rfl⟩ := hx
  have hp2 : 2 ≤ p := hp.out.two_le
  rw [add_comm (1 : ℤ_[p]), add_pow]
  have hsplit : ∑ m ∈ Finset.range (p + 1),
      ((p : ℤ_[p]) ^ k * c) ^ m * 1 ^ (p - m) * (p.choose m : ℤ_[p]) =
      1 + p * ((p : ℤ_[p]) ^ k * c) +
        ∑ m ∈ Finset.Ico 2 (p + 1), ((p : ℤ_[p]) ^ k * c) ^ m * (p.choose m : ℤ_[p]) := by
    rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (show 0 ≤ 2 by omega)
      (by omega : 2 ≤ p + 1)]
    simp only [one_pow, mul_one]
    rw [show Finset.Ico 0 2 = {0, 1} by decide, Finset.sum_pair (by norm_num)]
    simp [Nat.choose_one_right]
    ring
  rw [hsplit]
  have e : 1 + ↑p * (↑p ^ k * c) +
      ∑ m ∈ Finset.Ico 2 (p + 1), (↑p ^ k * c) ^ m * (p.choose m : ℤ_[p]) - 1 - ↑p * (↑p ^ k * c) =
      ∑ m ∈ Finset.Ico 2 (p + 1), ((p : ℤ_[p]) ^ k * c) ^ m * (p.choose m : ℤ_[p]) := by
    ring
  rw [e]
  refine Finset.dvd_sum fun m hm => ?_
  rw [Finset.mem_Ico] at hm
  rw [mul_pow, ← pow_mul]
  rcases lt_or_eq_of_le (Nat.lt_succ_iff.1 hm.2) with hmp | hmp
  ·
    have hch : (p : ℤ_[p]) ∣ (p.choose m : ℤ_[p]) := by
      exact Nat.cast_dvd_cast (hp.out.dvd_choose_self (by omega : m ≠ 0) hmp)
    have h1 : (p : ℤ_[p]) ^ (k + 1) ∣ (p : ℤ_[p]) ^ (k * m) :=
      pow_dvd_pow _ (by nlinarith)
    calc (p : ℤ_[p]) ^ (k + 2) = (p : ℤ_[p]) ^ (k + 1) * p := by ring
      _ ∣ (p : ℤ_[p]) ^ (k * m) * c ^ m * (p.choose m : ℤ_[p]) :=
        mul_dvd_mul (h1.mul_right _) hch
  ·
    rw [hmp]
    have h1 : (p : ℤ_[p]) ^ (k + 2) ∣ (p : ℤ_[p]) ^ (k * p) := pow_dvd_pow _ (by nlinarith)
    exact (h1.mul_right _).mul_right _

theorem pow_prime_mem_iff {k : ℕ} (hk : 2 ≤ k) {u : ℤ_[p]ˣ} (hu : u ∈ unitsOneAdd p k) :
    u ^ p ∈ unitsOneAdd p (k + 1) ∧ (u ^ p ∈ unitsOneAdd p (k + 2) ↔ u ∈ unitsOneAdd p (k + 1)) := by
  have hx : (p : ℤ_[p]) ^ k ∣ (u : ℤ_[p]) - 1 := hu
  have h := dvd_one_add_pow_sub hk hx
  rw [add_sub_cancel] at h
  have hpow : ((u ^ p : ℤ_[p]ˣ) : ℤ_[p]) - 1 =
      ((u : ℤ_[p]) ^ p - 1 - p * ((u : ℤ_[p]) - 1)) + p * ((u : ℤ_[p]) - 1) := by
    push_cast; ring
  have hp0 : (p : ℤ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  refine ⟨?_, ?_⟩
  · change (p : ℤ_[p]) ^ (k + 1) ∣ _
    rw [hpow]
    refine dvd_add ((pow_dvd_pow _ (by omega)).trans h) ?_
    rw [pow_succ, mul_comm]
    exact mul_dvd_mul_left _ hx
  · change (p : ℤ_[p]) ^ (k + 2) ∣ _ ↔ (p : ℤ_[p]) ^ (k + 1) ∣ _
    rw [hpow, dvd_add_right h]
    rw [show (p : ℤ_[p]) ^ (k + 2) = p * p ^ (k + 1) by ring]
    exact mul_dvd_mul_iff_left hp0

def levelQuot {k : ℕ} (u : unitsOneAdd p k) : ℤ_[p] :=
  Classical.choose (mem_unitsOneAdd.1 u.2)

theorem levelQuot_spec {k : ℕ} (u : unitsOneAdd p k) :
    ((u : ℤ_[p]ˣ) : ℤ_[p]) - 1 = (p : ℤ_[p]) ^ k * levelQuot u :=
  Classical.choose_spec (mem_unitsOneAdd.1 u.2)

theorem levelQuot_eq {k : ℕ} (u : unitsOneAdd p k) {c : ℤ_[p]}
    (hc : ((u : ℤ_[p]ˣ) : ℤ_[p]) - 1 = (p : ℤ_[p]) ^ k * c) : levelQuot u = c := by
  have hp0 : (p : ℤ_[p]) ^ k ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)
  exact mul_left_cancel₀ hp0 ((levelQuot_spec u).symm.trans hc)

theorem toZMod_natCast_prime_pow {k : ℕ} (hk : 1 ≤ k) :
    PadicInt.toZMod ((p : ℤ_[p]) ^ k) = 0 := by
  rw [map_pow, map_natCast, ZMod.natCast_self, zero_pow (by omega)]

variable (p) in

def levelHom (k : ℕ) (hk : 1 ≤ k) : unitsOneAdd p k →* Multiplicative (ZMod p) where
  toFun u := Multiplicative.ofAdd (PadicInt.toZMod (levelQuot u))
  map_one' := by
    have : levelQuot (1 : unitsOneAdd p k) = 0 := levelQuot_eq _ (by simp)
    rw [this, map_zero, ofAdd_zero]
  map_mul' u v := by
    have e : (((u * v : unitsOneAdd p k) : ℤ_[p]ˣ) : ℤ_[p]) - 1 = (p : ℤ_[p]) ^ k *
        (levelQuot u + levelQuot v + (p : ℤ_[p]) ^ k * levelQuot u * levelQuot v) := by
      have hu := levelQuot_spec u
      have hv := levelQuot_spec v
      have : (((u * v : unitsOneAdd p k) : ℤ_[p]ˣ) : ℤ_[p]) =
          ((u : ℤ_[p]ˣ) : ℤ_[p]) * ((v : ℤ_[p]ˣ) : ℤ_[p]) := rfl
      rw [this]
      linear_combination (((v : ℤ_[p]ˣ) : ℤ_[p])) * hu + (1 + (p : ℤ_[p]) ^ k * levelQuot u) * hv
    rw [levelQuot_eq _ e, ← ofAdd_add]
    congr 1
    rw [map_add, map_add, map_mul, map_mul, toZMod_natCast_prime_pow hk, zero_mul, zero_mul, add_zero]

theorem levelHom_apply {k : ℕ} (hk : 1 ≤ k) (u : unitsOneAdd p k) :
    levelHom p k hk u = Multiplicative.ofAdd (PadicInt.toZMod (levelQuot u)) := rfl

theorem levelHom_eq_one_iff {k : ℕ} (hk : 1 ≤ k) (u : unitsOneAdd p k) :
    levelHom p k hk u = 1 ↔ (u : ℤ_[p]ˣ) ∈ unitsOneAdd p (k + 1) := by
  rw [levelHom_apply, ← ofAdd_zero, EmbeddingLike.apply_eq_iff_eq, ← RingHom.mem_ker, PadicInt.ker_toZMod,
    PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton, mem_unitsOneAdd, levelQuot_spec,
    pow_succ]
  have hp0 : (p : ℤ_[p]) ^ k ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)
  exact (mul_dvd_mul_iff_left hp0).symm

theorem pow_prime_pow_mem_not_mem {s : ℕ} (hs : 2 ≤ s) {a : ℤ_[p]ˣ} (ha : a ∈ unitsOneAdd p s)
    (ha' : a ∉ unitsOneAdd p (s + 1)) (i : ℕ) :
    a ^ p ^ i ∈ unitsOneAdd p (s + i) ∧ a ^ p ^ i ∉ unitsOneAdd p (s + i + 1) := by
  induction i with
  | zero => simpa using ⟨ha, ha'⟩
  | succ i ih =>
    have h := pow_prime_mem_iff (by omega : 2 ≤ s + i) ih.1
    rw [pow_succ, pow_mul]
    refine ⟨by simpa [add_assoc] using h.1, fun hc => ih.2 (h.2.1 ?_)⟩
    simpa [add_assoc] using hc

theorem pow_not_mem_of_not_dvd {s : ℕ} (hs : 1 ≤ s) {a : ℤ_[p]ˣ} (ha : a ∈ unitsOneAdd p s)
    (ha' : a ∉ unitsOneAdd p (s + 1)) {m : ℕ} (hm : ¬ p ∣ m) :
    a ^ m ∈ unitsOneAdd p s ∧ a ^ m ∉ unitsOneAdd p (s + 1) := by
  refine ⟨pow_mem ha m, fun h => ?_⟩
  have h1 : levelHom p s hs (⟨a, ha⟩ ^ m) = 1 := (levelHom_eq_one_iff hs _).2 (by simpa using h)
  have h2 : levelHom p s hs ⟨a, ha⟩ ≠ 1 := fun h' => ha' ((levelHom_eq_one_iff hs _).1 h')
  rw [map_pow, levelHom_apply, ← ofAdd_nsmul, ← ofAdd_zero, EmbeddingLike.apply_eq_iff_eq,
    nsmul_eq_mul] at h1
  rw [levelHom_apply, ← ofAdd_zero, Ne, EmbeddingLike.apply_eq_iff_eq] at h2
  have hm' : (m : ZMod p) ≠ 0 := by
    rwa [Ne, ZMod.natCast_eq_zero_iff]
  exact h2 ((mul_eq_zero.1 h1).resolve_left hm')

theorem exists_level {a : ℤ_[p]ˣ} (ha : a ≠ 1) :
    ∃ s, a ∈ unitsOneAdd p s ∧ a ∉ unitsOneAdd p (s + 1) := by
  have hex : ∃ k, a ∉ unitsOneAdd p k := by
    by_contra h
    push Not at h
    exact ha (eq_one_of_forall_mem_unitsOneAdd h)
  classical
  refine ⟨Nat.find hex - 1, ?_, ?_⟩
  · by_contra h
    have := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by
      have : Nat.find hex ≠ 0 := by
        intro h0
        have := Nat.find_spec hex
        rw [h0, unitsOneAdd_zero] at this
        exact this (Subgroup.mem_top _)
      omega)
    exact this h
  · have h0 : Nat.find hex ≠ 0 := by
      intro h0
      have := Nat.find_spec hex
      rw [h0, unitsOneAdd_zero] at this
      exact this (Subgroup.mem_top _)
    rw [Nat.sub_add_cancel (by omega)]
    exact Nat.find_spec hex

theorem exists_mul_inv_pow_mem {s : ℕ} (hs : 2 ≤ s) {a : ℤ_[p]ˣ} (ha : a ∈ unitsOneAdd p s)
    (ha' : a ∉ unitsOneAdd p (s + 1)) {b : ℤ_[p]ˣ} (hb : b ∈ unitsOneAdd p s) (k : ℕ) :
    ∃ j : ℕ, b * (a ^ j)⁻¹ ∈ unitsOneAdd p k := by
  induction k with
  | zero => exact ⟨0, by simp⟩
  | succ k ih =>
    obtain ⟨j, hj⟩ := ih
    by_cases hks : k + 1 ≤ s
    · exact ⟨0, by simpa using unitsOneAdd_antitone hks hb⟩
    push Not at hks

    obtain ⟨hc, hc'⟩ := pow_prime_pow_mem_not_mem hs ha ha' (k - s)
    rw [Nat.add_sub_cancel' (by omega)] at hc hc'
    have hk1 : 1 ≤ k := by omega
    set c := a ^ p ^ (k - s)
    set d := b * (a ^ j)⁻¹
    set φ := levelHom p k hk1
    have hcφ : Multiplicative.toAdd (φ ⟨c, hc⟩) ≠ 0 := by
      intro h
      exact hc' ((levelHom_eq_one_iff hk1 ⟨c, hc⟩).1
        (Multiplicative.toAdd.injective (h.trans toAdd_one.symm)))
    set r : ℕ := (Multiplicative.toAdd (φ ⟨d, hj⟩) / Multiplicative.toAdd (φ ⟨c, hc⟩)).val
    refine ⟨j + p ^ (k - s) * r, ?_⟩
    have hmem : d * (c ^ r)⁻¹ ∈ unitsOneAdd p k := mul_mem hj (inv_mem (pow_mem hc r))
    have hφ : φ ⟨d * (c ^ r)⁻¹, hmem⟩ = 1 := by
      have e : (⟨d * (c ^ r)⁻¹, hmem⟩ : unitsOneAdd p k) = ⟨d, hj⟩ * (⟨c, hc⟩ ^ r)⁻¹ := rfl
      rw [e, map_mul, map_inv, map_pow]
      apply Multiplicative.toAdd.injective
      rw [toAdd_mul, toAdd_inv, toAdd_pow, toAdd_one, nsmul_eq_mul]
      simp only [r, ZMod.natCast_val, ZMod.cast_id', id]
      rw [div_mul_cancel₀ _ hcφ, add_neg_cancel]
    have h := (levelHom_eq_one_iff hk1 _).1 hφ
    have e2 : b * (a ^ (j + p ^ (k - s) * r))⁻¹ = d * (c ^ r)⁻¹ := by
      simp only [d, c, pow_add, pow_mul, mul_inv_rev]
      group
    rw [e2]
    exact h

theorem relIndex_unitsOneAdd_inf_succ {k : ℕ} (hk : 1 ≤ k) (R : Subgroup ℤ_[p]ˣ) {c : ℤ_[p]ˣ}
    (hcR : c ∈ R) (hc : c ∈ unitsOneAdd p k) (hc' : c ∉ unitsOneAdd p (k + 1)) :
    (unitsOneAdd p (k + 1) ⊓ R).relIndex (unitsOneAdd p k ⊓ R) = p := by
  set S := unitsOneAdd p k ⊓ R
  let φ : S →* Multiplicative (ZMod p) :=
    (levelHom p k hk).comp (Subgroup.inclusion inf_le_left)
  have hker : φ.ker = (unitsOneAdd p (k + 1) ⊓ R).subgroupOf S := by
    ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    change levelHom p k hk _ = 1 ↔ _
    rw [levelHom_eq_one_iff]
    exact ⟨fun h => ⟨h, u.2.2⟩, fun h => h.1⟩
  have hrange : φ.range = ⊤ := by
    have hne : φ ⟨c, hc, hcR⟩ ≠ 1 := by
      change levelHom p k hk _ ≠ 1
      rw [Ne, levelHom_eq_one_iff]
      exact hc'
    have hcard : Nat.card (Multiplicative (ZMod p)) = p := by
      rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
    have := Subgroup.eq_bot_or_eq_top_of_prime_card φ.range (hp := ⟨by rw [hcard]; exact hp.out⟩)
    rcases this with h | h
    · exact absurd (h ▸ φ.mem_range.2 ⟨_, rfl⟩ : φ ⟨c, hc, hcR⟩ ∈ (⊥ : Subgroup _))
        (by rw [Subgroup.mem_bot]; exact hne)
    · exact h
  rw [Subgroup.relIndex, ← hker, Subgroup.index_ker, hrange, Subgroup.card_top,
    Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]

theorem relIndex_unitsOneAdd_inf {s : ℕ} (hs : 2 ≤ s) (R : Subgroup ℤ_[p]ˣ) {a : ℤ_[p]ˣ}
    (haR : a ∈ R) (ha : a ∈ unitsOneAdd p s) (ha' : a ∉ unitsOneAdd p (s + 1)) (i : ℕ) :
    (unitsOneAdd p (s + i) ⊓ R).relIndex (unitsOneAdd p s ⊓ R) = p ^ i := by
  induction i with
  | zero => simp
  | succ i ih =>
    obtain ⟨h1, h2⟩ := pow_prime_pow_mem_not_mem hs ha ha' i
    have hstep := relIndex_unitsOneAdd_inf_succ (by omega : 1 ≤ s + i) R
      (pow_mem haR _) h1 h2
    rw [← add_assoc, ← Subgroup.relIndex_mul_relIndex _ _ _
      (inf_le_inf_right _ (unitsOneAdd_antitone (show s + i ≤ s + i + 1 by omega)))
      (inf_le_inf_right _ (unitsOneAdd_antitone (show s ≤ s + i by omega))), hstep, ih, pow_succ,
      mul_comm]

end SenTateChar

end GroundTheory.PAdicHodge
