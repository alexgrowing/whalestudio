import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MapSmulOfIsHausdorff

set_option autoImplicit false

open GlobalTheory.HTLat

namespace GlobalTheory

theorem exists_pow_prime_root_of_card_torsion {M : Type} [CommGroup M] {l : ℕ} [Fact l.Prime]
    {c : ℕ} (hcard : ∀ k : ℕ, Nat.card {x : M // x ^ (l ^ k) = 1} = l ^ (c * k)) (k : ℕ) (y : M)
    (hy : y ^ (l ^ k) = 1) : ∃ z : M, z ^ (l ^ (k + 1)) = 1 ∧ z ^ l = y := by
  have hl : 0 < l := (Fact.out : l.Prime).pos
  let T : ℕ → Subgroup M := fun n => (powMonoidHom (l ^ n)).ker
  have hT : ∀ n, Nat.card (T n) = l ^ (c * n) := fun n => by
    rw [← hcard n]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun x => by simp [T, MonoidHom.mem_ker])
  let φ : T (k + 1) →* M := (powMonoidHom l).comp (T (k + 1)).subtype
  have hker : Nat.card φ.ker = l ^ c := by
    rw [← mul_one c, ← hT 1]
    refine Nat.card_congr
      { toFun := fun y => ⟨y.1.1, ?_⟩
        invFun := fun z => ⟨⟨z.1, ?_⟩, ?_⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    · have := y.2
      simp only [T, φ, MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply,
        powMonoidHom_apply, Subgroup.coe_subtype] at this
      simpa [T, MonoidHom.mem_ker] using this
    · have hz : (z : M) ^ l = 1 := by simpa [T] using MonoidHom.mem_ker.1 z.2
      simp only [T, MonoidHom.mem_ker, powMonoidHom_apply]
      rw [pow_succ' l k, pow_mul, hz, one_pow]
    · have := z.2
      simpa [T, φ, MonoidHom.mem_ker] using this
  have hrange : Nat.card φ.range = l ^ (c * k) := by
    have h1 := Subgroup.card_mul_index φ.ker
    rw [Subgroup.index_ker, hker, hT (k + 1), mul_add, mul_one, pow_add, mul_comm] at h1
    exact Nat.eq_of_mul_eq_mul_right (pow_pos hl c) h1
  have hfin : Finite (T k) := Nat.finite_of_card_ne_zero (by rw [hT k]; exact (pow_pos hl _).ne')
  have hle : φ.range ≤ T k := by
    rintro _ ⟨z, rfl⟩
    have := z.2
    simp only [T, MonoidHom.mem_ker, powMonoidHom_apply] at this ⊢
    simp only [φ, MonoidHom.coe_comp, Function.comp_apply, powMonoidHom_apply,
      Subgroup.coe_subtype]
    rw [← pow_mul, ← pow_succ', this]
  have heq : φ.range = T k := Subgroup.eq_of_le_of_card_ge hle (by rw [hrange, hT k])
  have hyT : y ∈ T k := by simpa [T, MonoidHom.mem_ker] using hy
  rw [← heq] at hyT
  obtain ⟨z, hz⟩ := hyT
  exact ⟨z.1, MonoidHom.mem_ker.1 z.2, hz⟩

theorem exists_tate_lev_eq_of_card_torsion :
    ∀ (M : Type) [CommGroup M] (l : ℕ) [Fact l.Prime] (c : ℕ),
      (∀ k : ℕ, Nat.card {x : M // x ^ (l ^ k) = 1} = l ^ (c * k)) →
      ∀ (N : ℕ) (x : M), x ^ (l ^ N) = 1 → ∃ t : Tate l M, t.lev N = x := by
  intro M _ l _ c hcard N x hx
  have h := exists_pow_prime_root_of_card_torsion hcard
  choose r hr1 hr2 using h
  let g : (n : ℕ) → {y : M // y ^ (l ^ (N + n)) = 1} := fun n =>
    Nat.rec ⟨x, hx⟩ (fun n y => ⟨r (N + n) y.1 y.2, hr1 (N + n) y.1 y.2⟩) n
  have hg0 : (g 0).1 = x := rfl
  have hgs : ∀ n, (g (n + 1)).1 ^ l = (g n).1 := fun n => hr2 (N + n) (g n).1 (g n).2
  have hgk : ∀ n k, (g (n + k)).1 ^ (l ^ k) = (g n).1 := fun n k => by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', pow_mul]
      show ((g (n + k + 1)).1 ^ l) ^ (l ^ k) = _
      rw [hgs, ih]
  let s : ℕ → M := fun n => (g n).1 ^ (l ^ N)
  have hs : ∀ n, s n ^ l ^ n = 1 ∧ s (n + 1) ^ l = s n := fun n => by
    refine ⟨?_, ?_⟩
    · simp only [s]
      rw [← pow_mul, ← pow_add, (g n).2]
    · simp only [s]
      rw [← pow_mul, mul_comm, pow_mul, hgs]
  refine ⟨Tate.mk s hs, ?_⟩
  rw [Tate.lev_mk]
  simp only [s]
  have := hgk 0 N
  rw [zero_add] at this
  rw [this, hg0]

end GlobalTheory
