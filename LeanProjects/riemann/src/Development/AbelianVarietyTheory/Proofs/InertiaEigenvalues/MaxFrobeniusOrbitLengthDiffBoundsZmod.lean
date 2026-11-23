import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot

open PowerSeries GlobalTheory.BK Function Finset

namespace GlobalTheory.BK.OrbitBound

variable {e : ℕ} (u : ZMod e)

theorem iter_mul (n : ℕ) (x : ZMod e) : (fun y => u * y)^[n] x = u ^ n * x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih => rw [iterate_succ_apply, ih, pow_succ, mul_assoc]

noncomputable def orb (x : ZMod e) : Finset (ZMod e) :=
  (range (minimalPeriod (fun y => u * y) x)).image fun k => u ^ k * x

variable {a : ℕ} (ha : 0 < a) (hu : u ^ a = 1)
include ha hu

theorem mp_pos (x : ZMod e) : 0 < minimalPeriod (fun y => u * y) x :=
  IsPeriodicPt.minimalPeriod_pos ha (by
    change (fun y => u * y)^[a] x = x
    rw [iter_mul, hu, one_mul])

theorem pow_mp_mul (x : ZMod e) : u ^ minimalPeriod (fun y => u * y) x * x = x := by
  rw [← iter_mul]; exact iterate_minimalPeriod

theorem pow_mp_mul_mul (x : ZMod e) (k : ℕ) :
    u ^ (minimalPeriod (fun y => u * y) x * k) * x = x := by
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.mul_succ, pow_add, mul_assoc, pow_mp_mul u ha hu x, ih]

theorem mp_sub_dvd (x y : ZMod e) : minimalPeriod (fun z => u * z) (x - y) ∣
    minimalPeriod (fun z => u * z) x * minimalPeriod (fun z => u * z) y := by
  apply IsPeriodicPt.minimalPeriod_dvd
  change (fun z => u * z)^[_] (x - y) = x - y
  rw [iter_mul, mul_sub, pow_mp_mul_mul u ha hu x, mul_comm (minimalPeriod _ x),
    pow_mp_mul_mul u ha hu y]

theorem mp_sub_pow_dvd (x : ZMod e) (k : ℕ) : minimalPeriod (fun z => u * z) (x - u ^ k * x) ∣
    minimalPeriod (fun z => u * z) x := by
  apply IsPeriodicPt.minimalPeriod_dvd
  change (fun z => u * z)^[_] (x - u ^ k * x) = x - u ^ k * x
  rw [iter_mul, mul_sub, mul_left_comm, pow_mp_mul u ha hu x]

theorem isUnit_u : IsUnit u :=
  have h : u * u ^ (a - 1) = 1 := by rw [← pow_succ', Nat.sub_add_cancel ha, hu]
  ⟨⟨u, u ^ (a - 1), h, by rw [mul_comm]; exact h⟩, rfl⟩

theorem card_orb (x : ZMod e) : (orb u x).card = minimalPeriod (fun y => u * y) x := by
  rw [orb, card_image_of_injOn, card_range]
  rw [coe_range]
  intro i hi j hj h
  refine iterate_injOn_Iio_minimalPeriod hi hj ?_
  simp only [iter_mul]
  exact h

theorem mem_orb (x : ZMod e) (n : ℕ) : u ^ n * x ∈ orb u x := by
  refine mem_image.2 ⟨n % minimalPeriod (fun y => u * y) x, mem_range.2 (Nat.mod_lt _ (mp_pos u ha hu x)), ?_⟩
  show u ^ (n % _) * x = u ^ n * x
  rw [← iter_mul, ← iter_mul]
  exact iterate_mod_minimalPeriod_eq

omit ha hu in
theorem orb_subset {Sig : Finset (ZMod e)} (hcl : ∀ c ∈ Sig, u * c ∈ Sig) {x : ZMod e}
    (hx : x ∈ Sig) : orb u x ⊆ Sig := by
  have key : ∀ k : ℕ, u ^ k * x ∈ Sig := by
    intro k
    induction k with
    | zero => simpa using hx
    | succ k ih => rw [pow_succ', mul_assoc]; exact hcl _ ih
  intro z hz
  obtain ⟨k, -, rfl⟩ := mem_image.1 hz
  exact key k

theorem four_mp_le (Sig : Finset (ZMod e)) (N : ℕ) (hcl : ∀ c ∈ Sig, u * c ∈ Sig) (h0 : (0 : ZMod e) ∈ Sig)
    (hN : Sig.card ≤ N) (h2 : 2 ≤ N) {x y : ZMod e} (hx : x ∈ Sig) (hy : y ∈ Sig) :
    4 * minimalPeriod (fun z => u * z) (x - y) ≤ N ^ 2 := by
  classical
  by_cases hyo : y ∈ orb u x
  · obtain ⟨k, -, rfl⟩ := mem_image.1 hyo
    have hle := Nat.le_of_dvd (mp_pos u ha hu x) (mp_sub_pow_dvd u ha hu x k)
    by_cases hx0 : x = 0
    · have h1 : minimalPeriod (fun y => u * y) x = 1 :=
        minimalPeriod_eq_one_iff_isFixedPt.2 (by simp [IsFixedPt, hx0])
      nlinarith
    · have hn0 : (0 : ZMod e) ∉ orb u x := by
        intro h
        obtain ⟨j, -, hj⟩ := mem_image.1 h
        exact hx0 (((isUnit_u u ha hu).pow j).mul_right_eq_zero.1 hj)
      have hsub : insert 0 (orb u x) ⊆ Sig := insert_subset h0 (orb_subset u hcl hx)
      have hc := card_le_card hsub
      rw [card_insert_of_notMem hn0, card_orb u ha hu] at hc
      nlinarith
  · have hdisj : Disjoint (orb u x) (orb u y) := by
      rw [disjoint_left]
      intro z hz1 hz2
      obtain ⟨i, -, rfl⟩ := mem_image.1 hz1
      obtain ⟨j, hj, hji⟩ := mem_image.1 hz2
      apply hyo
      have hy' : y = u ^ (minimalPeriod (fun z => u * z) y - j + i) * x := by
        rw [pow_add, mul_assoc, ← hji, ← mul_assoc, ← pow_add,
          Nat.sub_add_cancel (le_of_lt (mem_range.1 hj)), pow_mp_mul u ha hu y]
      rw [hy']
      exact mem_orb u ha hu x _
    have hsub : orb u x ∪ orb u y ⊆ Sig := union_subset (orb_subset u hcl hx) (orb_subset u hcl hy)
    have hc := card_le_card hsub
    rw [card_union_of_disjoint hdisj, card_orb u ha hu, card_orb u ha hu] at hc
    have hle := Nat.le_of_dvd (Nat.mul_pos (mp_pos u ha hu x) (mp_pos u ha hu y)) (mp_sub_dvd u ha hu x y)
    set m1 := minimalPeriod (fun z => u * z) x
    set m2 := minimalPeriod (fun z => u * z) y
    have h4 : 4 * (m1 * m2) ≤ (m1 + m2) ^ 2 := by
      zify; nlinarith [sq_nonneg ((m1 : ℤ) - m2)]
    have h5 : (m1 + m2) ^ 2 ≤ N ^ 2 := Nat.pow_le_pow_left (hc.trans hN) 2
    omega

end GlobalTheory.BK.OrbitBound

namespace GlobalTheory.BK

open OrbitBound in

theorem maxPeriod_bounds : ∀ (l e a : ℕ), l.Prime → 1 ≤ a → e + 1 = l ^ a → ∀ (Sig : Finset (ZMod e)) (N : ℕ),
    (∀ c ∈ Sig, (l : ZMod e) * c ∈ Sig) → (0 : ZMod e) ∈ Sig → Sig.card ≤ N → 2 ≤ N →
    1 ≤ maxPeriod l Sig ∧ 4 * maxPeriod l Sig ≤ N ^ 2 ∧ ∀ c ∈ Sig, frobPeriod l c ≤ maxPeriod l Sig := by
  intro l e a _ ha hea Sig N hcl h0 hN h2
  have hu : (l : ZMod e) ^ a = 1 := by
    rw [← Nat.cast_pow, ← hea]
    push_cast
    rw [ZMod.natCast_self, zero_add]
  have h00 : ((0 : ZMod e), (0 : ZMod e)) ∈ Sig ×ˢ Sig := mem_product.2 ⟨h0, h0⟩
  refine ⟨?_, ?_, ?_⟩
  · exact le_trans (Nat.succ_le_of_lt (mp_pos (l : ZMod e) ha hu ((0 : ZMod e) - 0)))
      (Finset.le_sup (f := fun p : ZMod e × ZMod e => frobPeriod l (p.1 - p.2)) h00)
  · obtain ⟨p, hp, hpe⟩ := Finset.exists_mem_eq_sup (Sig ×ˢ Sig) ⟨_, h00⟩
      (fun p : ZMod e × ZMod e => frobPeriod l (p.1 - p.2))
    unfold maxPeriod
    rw [hpe]
    exact four_mp_le (l : ZMod e) ha hu Sig N hcl h0 hN h2 (mem_product.1 hp).1 (mem_product.1 hp).2
  · intro c hc
    have := Finset.le_sup (f := fun p : ZMod e × ZMod e => frobPeriod l (p.1 - p.2))
      (mem_product.2 ⟨hc, h0⟩ : (c, (0 : ZMod e)) ∈ Sig ×ˢ Sig)
    simp only [sub_zero] at this
    exact this

end GlobalTheory.BK
