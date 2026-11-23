import Mathlib
open scoped NNReal

namespace GlobalTheory

theorem phiEq_iterate (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] [ExpChar R l] (u : R)
    (κ : Type) [Fintype κ] (D : κ → R) (c : κ → κ → R) (h : ℕ)
    (hD : ∀ j, u ^ h * D j = ∑ i, D i ^ l * c i j) (k : ℕ) :
    ∃ a : ℕ, a + h ≤ h * l ^ k ∧ ∃ e : κ → κ → R,
      ∀ j, u ^ a * D j = ∑ i, D i ^ (l ^ k) * e i j := by
  classical
  have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  induction k with
  | zero =>
    refine ⟨0, by simp, fun i j => if i = j then 1 else 0, fun j => ?_⟩
    simp
  | succ k ih =>
    obtain ⟨a, ha, e, he⟩ := ih
    refine ⟨h + l * a, ?_, fun i' j => ∑ i, e i' i ^ l * c i j, fun j => ?_⟩
    · have h1 : l * (a + h) ≤ l * (h * l ^ k) := Nat.mul_le_mul_left _ ha
      have h2 : 2 * h ≤ l * h := Nat.mul_le_mul_right _ hl2
      calc h + l * a + h = 2 * h + l * a := by ring
        _ ≤ l * h + l * a := by omega
        _ = l * (a + h) := by ring
        _ ≤ l * (h * l ^ k) := h1
        _ = h * l ^ (k + 1) := by ring
    · calc u ^ (h + l * a) * D j = ∑ i, (u ^ a * D i) ^ l * c i j := by
            rw [pow_add, mul_comm (u ^ h) (u ^ (l * a)), mul_assoc, hD j, Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [mul_pow, ← pow_mul, mul_comm a l]; ring
        _ = ∑ i, (∑ i', D i' ^ (l ^ k) * e i' i) ^ l * c i j := by
            simp only [he]
        _ = ∑ i, ∑ i', D i' ^ (l ^ (k + 1)) * (e i' i ^ l * c i j) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [sum_pow_char, Finset.sum_mul]
            refine Finset.sum_congr rfl fun i' _ => ?_
            rw [mul_pow, ← pow_mul, pow_succ]; ring
        _ = ∑ i', D i' ^ (l ^ (k + 1)) * ∑ i, e i' i ^ l * c i j := by
            rw [Finset.sum_comm]
            simp only [Finset.mul_sum]

theorem phiEq_dvd_all_pow : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (u : R),
    ((l : ℕ) : R) = 0 → u ∈ nonZeroDivisors R → ∀ (κ : Type) [Fintype κ] (D : κ → R)
    (c : κ → κ → R) (h : ℕ), (∀ j, u ^ h * D j = ∑ i, D i ^ l * c i j) →
    (∀ j (M : ℕ), ∃ c : ℕ, ∀ n : ℕ, u ^ (M * n) ∣ u ^ c * D j ^ n) → ∀ (m : ℕ) j, u ^ m ∣ D j := by
  intro l _ R _ u hl hu κ _ D c h hD hnil m j
  classical
  have hlp : l.Prime := Fact.out
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact ⟨0, Subsingleton.elim _ _⟩
  have hchar : ringChar R = l := by
    rcases (Nat.dvd_prime hlp).1 (ringChar.dvd hl) with h1 | h1
    · exact absurd h1 CharP.ringChar_ne_one
    · exact h1
  haveI : CharP R l := hchar ▸ ringChar.charP R
  haveI : ExpChar R l := ExpChar.prime hlp
  choose C hC using fun i => hnil i (h + 1)
  set Cm := ∑ i, C i with hCm
  obtain ⟨k, hk⟩ : ∃ k, m + Cm < l ^ k := ⟨m + Cm, Nat.lt_pow_self hlp.one_lt⟩
  obtain ⟨a, ha, e, he⟩ := phiEq_iterate l R u κ D c h hD k
  have hdiv : u ^ ((h + 1) * l ^ k) ∣ u ^ (Cm + a) * D j := by
    rw [pow_add, mul_assoc, he j, Finset.mul_sum]
    refine Finset.dvd_sum fun i _ => ?_
    rw [← mul_assoc]
    refine Dvd.dvd.mul_right ?_ _
    have hCi : C i ≤ Cm := Finset.single_le_sum (fun i _ => Nat.zero_le (C i)) (Finset.mem_univ i)
    refine (hC i (l ^ k)).trans ?_
    have hsp : u ^ Cm = u ^ C i * u ^ (Cm - C i) := by rw [← pow_add, Nat.add_sub_cancel' hCi]
    rw [hsp]
    exact ⟨u ^ (Cm - C i), by ring⟩
  have hle : Cm + a + m ≤ (h + 1) * l ^ k := by
    have : h * l ^ k + l ^ k = (h + 1) * l ^ k := by ring
    omega
  obtain ⟨y, hy⟩ := hdiv
  have hsplit : (h + 1) * l ^ k = (Cm + a) + ((h + 1) * l ^ k - (Cm + a)) := by omega
  rw [hsplit, pow_add u (Cm + a), mul_assoc] at hy
  have hreg : u ^ (Cm + a) ∈ nonZeroDivisors R := pow_mem hu _
  have hDj := (mul_cancel_left_mem_nonZeroDivisors hreg).1 hy
  rw [hDj]
  refine Dvd.dvd.mul_right (pow_dvd_pow u ?_) _
  omega

end GlobalTheory
