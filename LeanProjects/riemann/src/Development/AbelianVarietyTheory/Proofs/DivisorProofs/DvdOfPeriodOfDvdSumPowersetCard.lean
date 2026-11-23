import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardDvdSumOfInvariantOfCardStabilizerDvd

open Pointwise

namespace GlobalTheory

namespace PeriodDvd

def killed (d : ℕ) [NeZero d] (s : ℕ) : Finset (ZMod d) :=
  Finset.univ.filter fun x => s • x = 0

lemma mem_killed {d : ℕ} [NeZero d] {s : ℕ} {x : ZMod d} : x ∈ killed d s ↔ s • x = 0 := by
  simp [killed]

lemma killed_eq_image {d : ℕ} [NeZero d] {s e : ℕ} (h : s * e = d) :
    killed d s = (Finset.range s).image fun j => ((e * j : ℕ) : ZMod d) := by
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hs : 0 < s := Nat.pos_of_mul_pos_right (h ▸ hd)
  have he : 0 < e := Nat.pos_of_mul_pos_left (h ▸ hd)
  ext x
  rw [mem_killed, Finset.mem_image]
  constructor
  · intro hx
    have h1 : ((s * x.val : ℕ) : ZMod d) = 0 := by
      rw [Nat.cast_mul, ZMod.natCast_zmod_val, ← nsmul_eq_mul, hx]
    rw [ZMod.natCast_eq_zero_iff] at h1
    have h2 : s * e ∣ s * x.val := by rw [h]; exact h1
    obtain ⟨j, hj⟩ := Nat.dvd_of_mul_dvd_mul_left hs h2
    refine ⟨j, ?_, ?_⟩
    · rw [Finset.mem_range]
      have h3 := ZMod.val_lt x
      rw [hj] at h3
      by_contra hc
      have : e * s ≤ e * j := Nat.mul_le_mul_left _ (not_lt.mp hc)
      nlinarith
    · rw [← hj, ZMod.natCast_zmod_val]
  · rintro ⟨j, -, rfl⟩
    rw [nsmul_eq_mul, ← Nat.cast_mul, ← mul_assoc, h, Nat.cast_mul, ZMod.natCast_self, zero_mul]

lemma val_mul {d : ℕ} [NeZero d] {s e : ℕ} (h : s * e = d) {j : ℕ} (hj : j < s) :
    ((e * j : ℕ) : ZMod d).val = e * j := by
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have he : 0 < e := Nat.pos_of_mul_pos_left (h ▸ hd)
  apply ZMod.val_cast_of_lt
  rw [← h, mul_comm s e]
  exact Nat.mul_lt_mul_of_pos_left hj he

lemma injOn_mul {d : ℕ} [NeZero d] {s e : ℕ} (h : s * e = d) :
    Set.InjOn (fun j => ((e * j : ℕ) : ZMod d)) (Finset.range s : Set ℕ) := by
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have he : 0 < e := Nat.pos_of_mul_pos_left (h ▸ hd)
  intro i hi j hj hij
  have hi' : i < s := by simpa using hi
  have hj' : j < s := by simpa using hj
  have := congrArg ZMod.val hij
  simp only at this
  rw [val_mul h hi', val_mul h hj'] at this
  exact Nat.eq_of_mul_eq_mul_left he this

lemma card_killed {d : ℕ} [NeZero d] {s e : ℕ} (h : s * e = d) : (killed d s).card = s := by
  rw [killed_eq_image h, Finset.card_image_of_injOn (injOn_mul h), Finset.card_range]

lemma sum_killed {d : ℕ} [NeZero d] {s e : ℕ} (h : s * e = d) (q : ℕ) :
    ∑ x ∈ killed d s, q ^ x.val = ∑ j ∈ Finset.range s, (q ^ e) ^ j := by
  rw [killed_eq_image h, Finset.sum_image (injOn_mul h)]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [val_mul h (Finset.mem_range.mp hj), pow_mul]

lemma mem_iff_mem_killed {d : ℕ} [NeZero d] (H : AddSubgroup (ZMod d)) (x : ZMod d) :
    x ∈ H ↔ x ∈ killed d (Nat.card H) := by
  classical
  have hdvd : Nat.card H ∣ d := by
    have := AddSubgroup.card_addSubgroup_dvd_card H
    rwa [Nat.card_zmod] at this
  obtain ⟨e, he⟩ := hdvd
  have hsub : Finset.univ.filter (· ∈ H) ⊆ killed d (Nat.card H) := by
    intro y hy
    have hy' : y ∈ H := (Finset.mem_filter.mp hy).2
    rw [mem_killed]
    have : Nat.card H • (⟨y, hy'⟩ : H) = 0 := card_nsmul_eq_zero'
    exact congrArg Subtype.val this
  have hc : (Finset.univ.filter (· ∈ H)).card = Nat.card H := by
    rw [← Nat.card_eq_finsetCard]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun y => by simp)
  have := Finset.eq_of_subset_of_card_le hsub (by rw [hc, card_killed he.symm])
  rw [← this]
  simp

lemma pow_mod_modEq (q d m : ℕ) (hq : 1 ≤ q) : q ^ (m % d) ≡ q ^ m [MOD q ^ d - 1] := by
  have h1 : q ^ d ≡ 1 [MOD q ^ d - 1] :=
    ((Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ hq)).mpr dvd_rfl).symm
  conv_rhs => rw [← Nat.mod_add_div m d, pow_add, pow_mul]
  have := (h1.pow (m / d)).mul_left (q ^ (m % d))
  simpa using this.symm

lemma sum_vadd_modEq {d : ℕ} [NeZero d] (q : ℕ) (hq : 1 ≤ q) (g : ZMod d) (I : Finset (ZMod d)) :
    (∑ x ∈ I, q ^ x.val) * q ^ g.val ≡ ∑ x ∈ g +ᵥ I, q ^ x.val [MOD q ^ d - 1] := by
  rw [Finset.vadd_finset_def, Finset.sum_image (fun x _ y _ hxy => by simpa using hxy),
    Finset.sum_mul]
  refine Nat.ModEq.sum fun x _ => ?_
  rw [vadd_eq_add, ZMod.val_add, ← pow_add, add_comm]
  exact (pow_mod_modEq q d _ hq).symm

lemma vadd_killed_subset {d : ℕ} [NeZero d] (I : Finset (ZMod d)) {x : ZMod d} (hx : x ∈ I) :
    x +ᵥ killed d (Nat.card (AddAction.stabilizer (ZMod d) I)) ⊆ I := by
  intro y hy
  obtain ⟨z, hz, rfl⟩ := Finset.mem_vadd_finset.mp hy
  have hz' : z +ᵥ I = I := (mem_iff_mem_killed _ z).mpr hz
  have : z +ᵥ x ∈ z +ᵥ I := Finset.vadd_mem_vadd_finset hx
  rw [hz'] at this
  simpa [add_comm] using this

lemma card_stabilizer_dvd {d : ℕ} [NeZero d] (I : Finset (ZMod d)) :
    Nat.card (AddAction.stabilizer (ZMod d) I) ∣ d := by
  have := AddSubgroup.card_addSubgroup_dvd_card (AddAction.stabilizer (ZMod d) I)
  rwa [Nat.card_zmod] at this

lemma le_card_stabilizer_killed {d : ℕ} [NeZero d] {s e : ℕ} (h : s * e = d) :
    s ∣ Nat.card (AddAction.stabilizer (ZMod d) (killed d s)) := by
  obtain ⟨e', he'⟩ := card_stabilizer_dvd (killed d s)
  have h1 : killed d s ⊆ killed d (Nat.card (AddAction.stabilizer (ZMod d) (killed d s))) := by
    intro y hy
    rw [← mem_iff_mem_killed, AddAction.mem_stabilizer_iff]
    refine Finset.eq_of_subset_of_card_le ?_ (by rw [Finset.card_vadd_finset])
    intro z hz
    obtain ⟨w, hw, rfl⟩ := Finset.mem_vadd_finset.mp hz
    rw [mem_killed] at *
    rw [vadd_eq_add, nsmul_add, hy, hw, add_zero]
  have h2 := vadd_killed_subset (killed d s) (x := 0) (by simp [mem_killed])
  have h3 := Finset.card_le_card h1
  have h4 := Finset.card_le_card h2
  rw [Finset.card_vadd_finset] at h4
  rw [card_killed h, card_killed he'.symm] at h3 h4
  exact dvd_of_eq (le_antisymm h3 h4)

lemma sum_finset_zmod {d : ℕ} [NeZero d] (s : ℕ) (f : ℕ → ℤ) (q : ℕ) :
    ∑ I : Finset (ZMod d), (if I.card = s then f (∑ x ∈ I, q ^ x.val) else 0)
      = ∑ I ∈ (Finset.range d).powersetCard s, f (∑ i ∈ I, q ^ i) := by
  have hinj : Function.Injective (ZMod.val : ZMod d → ℕ) := ZMod.val_injective d
  rw [← Finset.sum_filter]
  refine Finset.sum_bij (fun I _ => I.image ZMod.val) ?_ ?_ ?_ ?_
  · intro I hI
    rw [Finset.mem_powersetCard, Finset.card_image_of_injective _ hinj]
    refine ⟨fun y hy => ?_, (Finset.mem_filter.mp hI).2⟩
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hy
    exact Finset.mem_range.mpr (ZMod.val_lt x)
  · intro I _ J _ hIJ
    exact Finset.image_injective hinj hIJ
  · intro J hJ
    rw [Finset.mem_powersetCard] at hJ
    have hJ' : (J.image (fun n : ℕ => (n : ZMod d))).image ZMod.val = J := by
      rw [Finset.image_image]
      refine (Finset.image_congr (g := id) fun n hn => ?_).trans Finset.image_id
      exact ZMod.val_cast_of_lt (Finset.mem_range.mp (hJ.1 hn))
    refine ⟨J.image (fun n : ℕ => (n : ZMod d)), ?_, hJ'⟩
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [← Finset.card_image_of_injective _ hinj, hJ', hJ.2]
  · intro I _
    rw [Finset.sum_image fun x _ y _ h => hinj h]

lemma exists_eq_mul_geom {q d s e l : ℕ} (hq : 2 ≤ q) (hd : 0 < d) (h : s * e = d)
    (hl : l * q ^ e ≡ l [MOD q ^ d - 1]) :
    ∃ k, l = k * ∑ j ∈ Finset.range s, (q ^ e) ^ j := by
  have he : 0 < e := Nat.pos_of_mul_pos_left (h ▸ hd)
  have hqe : 2 ≤ q ^ e := le_trans hq (Nat.le_self_pow he.ne' q)
  obtain ⟨m, hm⟩ : ∃ m, q ^ e = m + 1 := ⟨q ^ e - 1, by omega⟩
  have hm0 : 0 < m := by omega
  have hg := geom_sum_mul_add m s
  have hN : q ^ d - 1 = (∑ j ∈ Finset.range s, (m + 1) ^ j) * m := by
    rw [← h, mul_comm s e, pow_mul, hm, ← hg]; simp
  rw [hN, hm] at hl
  have h2 := (Nat.modEq_iff_dvd' (by nlinarith)).mp hl.symm
  have h3 : l * (m + 1) - l = l * m := by rw [mul_add]; omega
  rw [h3] at h2
  obtain ⟨k, hk⟩ := Nat.dvd_of_mul_dvd_mul_right hm0 h2
  exact ⟨k, by rw [hm, hk, mul_comm]⟩

end PeriodDvd

open PeriodDvd in

theorem dvd_of_period_of_dvd_sum_powersetCard (q d : ℕ) (a : ℕ → ℤ) (hq : 2 ≤ q) (hd : 0 < d)
    (hinv : ∀ k l i : ℕ, k * q ^ i ≡ l [MOD q ^ d - 1] → a k = a l)
    (hsum : ∀ k s : ℕ, (d : ℤ) ∣ ∑ I ∈ (Finset.range d).powersetCard s, a (k * ∑ i ∈ I, q ^ i))
    (s e l : ℕ) (hse : s * e = d) (hl : l * q ^ e ≡ l [MOD q ^ d - 1]) : (s : ℤ) ∣ a l := by
  classical
  haveI : NeZero d := ⟨hd.ne'⟩
  have hq1 : 1 ≤ q := by omega
  induction s using Nat.strong_induction_on generalizing e l with
  | _ s ih =>
  have hs : 0 < s := Nat.pos_of_mul_pos_right (hse ▸ hd)
  obtain ⟨k, hk⟩ := exists_eq_mul_geom hq hd hse hl
  rw [← sum_killed hse] at hk
  set h : Finset (ZMod d) → ℤ :=
    fun I => if I.card = s then a (k * ∑ x ∈ I, q ^ x.val) else 0 with hh
  have hmod : ∀ (g : ZMod d) (I : Finset (ZMod d)),
      (k * ∑ x ∈ I, q ^ x.val) * q ^ g.val ≡ k * ∑ x ∈ g +ᵥ I, q ^ x.val [MOD q ^ d - 1] := by
    intro g I
    rw [mul_assoc]
    exact (sum_vadd_modEq q hq1 g I).mul_left k
  have hhinv : ∀ (g : ZMod d) (I : Finset (ZMod d)), h (g +ᵥ I) = h I := by
    intro g I
    simp only [hh, Finset.card_vadd_finset]
    rw [hinv _ _ _ (hmod g I)]
  have htot : (d : ℤ) ∣ ∑ I, h I := by
    have := sum_finset_zmod (d := d) s (fun n => a (k * n)) q
    rw [hh, this]
    exact hsum k s
  set O := AddAction.orbit (ZMod d) (killed d s) with hO
  have hoff : (d : ℤ) ∣ ∑ I, (if I ∈ O then 0 else h I) := by
    have := card_dvd_sum_of_invariant_of_card_stabilizer_dvd (ZMod d) (Finset (ZMod d))
      (fun I => if I ∈ O then 0 else h I) ?_ ?_
    · rwa [Nat.card_zmod] at this
    · intro g I
      have : g +ᵥ I ∈ O ↔ I ∈ O := by
        constructor
        · intro hg
          have := AddAction.mem_orbit_of_mem_orbit (-g) hg
          simpa using this
        · exact fun hI => AddAction.mem_orbit_of_mem_orbit g hI
      simp only [this, hhinv]
    · intro I
      by_cases hI : I ∈ O
      · simp [hI]
      simp only [hI, if_false]
      by_cases hc : I.card = s
      swap
      · simp [hh, hc]
      obtain ⟨x, hx⟩ : I.Nonempty := Finset.card_pos.mp (hc ▸ hs)
      obtain ⟨e', he'⟩ := card_stabilizer_dvd I
      have hsub := vadd_killed_subset I hx
      have hle := Finset.card_le_card hsub
      rw [Finset.card_vadd_finset, card_killed he'.symm, hc] at hle
      rcases hle.lt_or_eq with hlt | heq
      · simp only [hh, hc, if_true]
        refine ih _ hlt e' _ he'.symm ?_
        have hmem : (e' : ZMod d) +ᵥ I = I := by
          refine (mem_iff_mem_killed (AddAction.stabilizer (ZMod d) I) _).mpr ?_
          rw [mem_killed, nsmul_eq_mul, ← Nat.cast_mul, ← he', ZMod.natCast_self]
        have h1 := hmod (e' : ZMod d) I
        rw [hmem, ZMod.val_natCast] at h1
        exact ((pow_mod_modEq q d e' hq1).mul_left _).symm.trans h1
      · exfalso
        apply hI
        rw [heq] at hsub
        have := Finset.eq_of_subset_of_card_le hsub
          (by rw [Finset.card_vadd_finset, card_killed hse, hc])
        exact ⟨x, this⟩
  have hon : ∑ I, (if I ∈ O then h I else 0) = (Nat.card O : ℤ) * a l := by
    rw [← Finset.sum_filter, Finset.sum_congr rfl (g := fun _ => a l), Finset.sum_const,
      nsmul_eq_mul]
    · congr 2
      rw [← Nat.card_eq_finsetCard]
      exact Nat.card_congr (Equiv.subtypeEquivRight fun y => by simp)
    · intro I hI
      obtain ⟨g, rfl⟩ : I ∈ O := (Finset.mem_filter.mp hI).2
      change h (g +ᵥ killed d s) = _
      rw [hhinv]
      simp only [hh, card_killed hse, if_true, hk]
  have hsplit : ∑ I, h I = ∑ I, (if I ∈ O then h I else 0) + ∑ I, (if I ∈ O then 0 else h I) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun I _ => ?_
    split_ifs <;> simp
  rw [hsplit, hon] at htot
  have h1 : (d : ℤ) ∣ (Nat.card O : ℤ) * a l := (dvd_add_left hoff).mp htot
  have hG : d = Nat.card O * Nat.card (AddAction.stabilizer (ZMod d) (killed d s)) := by
    rw [hO, Nat.card_congr (AddAction.orbitEquivQuotientStabilizer (ZMod d) (killed d s)),
      ← AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup, Nat.card_zmod]
  have hO0 : (Nat.card O : ℤ) ≠ 0 := by
    intro h0
    have : Nat.card O = 0 := by exact_mod_cast h0
    rw [this, zero_mul] at hG
    omega
  have h2 : (Nat.card O : ℤ) * (Nat.card (AddAction.stabilizer (ZMod d) (killed d s)) : ℤ)
      ∣ (Nat.card O : ℤ) * a l := by
    rw [← Nat.cast_mul, ← hG]; exact h1
  exact (Int.natCast_dvd_natCast.mpr (le_card_stabilizer_killed hse)).trans
    ((mul_dvd_mul_iff_left hO0).mp h2)

end GlobalTheory
