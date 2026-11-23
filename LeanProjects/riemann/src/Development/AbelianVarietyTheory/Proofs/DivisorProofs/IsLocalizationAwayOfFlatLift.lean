import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LiftAway

theorem mul_eq_zero_of_mem_map {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
    {I : Ideal R} (hI : I ^ 2 = 0) {u v : S} (hu : u ∈ I.map (algebraMap R S))
    (hv : v ∈ I.map (algebraMap R S)) : u * v = 0 := by
  have h := Ideal.mul_mem_mul hu hv
  rw [← Ideal.map_mul, ← pow_two, hI, Ideal.zero_eq_bot, Ideal.map_bot] at h
  exact h

theorem frac_add {B B' : Type} [CommRing B] [CommRing B'] [Algebra B B'] {a : B} {y z : B'}
    (hy : ∃ (n : ℕ) (b : B), y * algebraMap B B' a ^ n = algebraMap B B' b)
    (hz : ∃ (n : ℕ) (b : B), z * algebraMap B B' a ^ n = algebraMap B B' b) :
    ∃ (n : ℕ) (b : B), (y + z) * algebraMap B B' a ^ n = algebraMap B B' b := by
  obtain ⟨n, b, hb⟩ := hy
  obtain ⟨m, c, hc⟩ := hz
  refine ⟨n + m, b * a ^ m + c * a ^ n, ?_⟩
  rw [map_add, map_mul, map_mul, map_pow, map_pow, ← hb, ← hc]
  ring

theorem isLocalization_away_of_flat_lift (R B B' B₀ B₀' : Type) [CommRing R] [CommRing B]
    [CommRing B'] [CommRing B₀] [CommRing B₀'] [Algebra R B] [Algebra R B'] [Algebra B B']
    [IsScalarTower R B B'] [Algebra B₀ B₀'] (I : Ideal R) (hI : I ^ 2 = 0)
    (hflat : Module.Flat R B') (p : B →+* B₀) (p' : B' →+* B₀') (hp : Function.Surjective p)
    (hp' : Function.Surjective p') (hker : ∀ b, p b = 0 ↔ b ∈ I.map (algebraMap R B))
    (hker' : ∀ b, p' b = 0 ↔ b ∈ I.map (algebraMap R B'))
    (hcomm : ∀ b, p' (algebraMap B B' b) = algebraMap B₀ B₀' (p b)) (a : B)
    (hloc : IsLocalization.Away (p a) B₀') : IsLocalization.Away a B' := by
  haveI := hloc
  haveI := hflat
  set φ := algebraMap B B' with hφ
  have hφs : ∀ (r : R) (b : B), φ (r • b) = r • φ b := fun r b => by
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, hφ, ← IsScalarTower.algebraMap_apply]

  have hunit : IsUnit (φ a) := by
    have hu : IsUnit (p' (φ a)) := by
      rw [hcomm]; exact IsLocalization.Away.algebraMap_isUnit (p a)
    obtain ⟨v, hv⟩ := hp' (↑hu.unit⁻¹ : B₀')
    have hn : φ a * v - 1 ∈ I.map (algebraMap R B') := by
      rw [← hker', map_sub, map_mul, hv, map_one, IsUnit.mul_val_inv, sub_self]
    have h2 := mul_eq_zero_of_mem_map hI hn hn
    refine isUnit_iff_exists_inv.mpr ⟨v * (1 - (φ a * v - 1)), ?_⟩
    linear_combination (-1 : B') * h2

  have lift0 : ∀ y : B', ∃ (n : ℕ) (b : B), y * φ a ^ n - φ b ∈ I.map (algebraMap R B') := by
    intro y
    obtain ⟨⟨z, s, hs⟩, hz⟩ := IsLocalization.surj (Submonoid.powers (p a)) (p' y)
    obtain ⟨n, rfl⟩ := hs
    obtain ⟨b, rfl⟩ := hp z
    refine ⟨n, b, ?_⟩
    dsimp only at hz
    rw [← hker', map_sub, map_mul, map_pow, hcomm, hcomm, ← map_pow, hz, sub_self]
  have fracI : ∀ i ∈ I, ∀ y : B', ∃ (n : ℕ) (b : B),
      algebraMap R B' i * y * φ a ^ n = φ b := by
    intro i hi y
    obtain ⟨n, b, hb⟩ := lift0 y
    refine ⟨n, algebraMap R B i * b, ?_⟩
    have h0 := mul_eq_zero_of_mem_map hI (Ideal.mem_map_of_mem (algebraMap R B') hi) hb
    rw [map_mul, hφ, ← IsScalarTower.algebraMap_apply]
    linear_combination h0
  have fracMem : ∀ z ∈ I.map (algebraMap R B'), ∃ (n : ℕ) (b : B), z * φ a ^ n = φ b := by
    intro z hz
    change z ∈ Submodule.span B' (algebraMap R B' '' I) at hz
    have key : ∀ c : B', ∃ (n : ℕ) (b : B), (c * z) * φ a ^ n = φ b := by
      induction hz using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨i, hi, rfl⟩ := hx
        intro c
        obtain ⟨n, b, hb⟩ := fracI i hi c
        exact ⟨n, b, by rw [← hb]; ring⟩
      | zero => intro c; exact ⟨0, 0, by simp⟩
      | add x y _ _ hx hy => intro c; rw [mul_add]; exact frac_add (hx c) (hy c)
      | smul d x _ hx => intro c; rw [smul_eq_mul, ← mul_assoc]; exact hx (c * d)
    simpa using key 1
  have surj : ∀ y : B', ∃ (n : ℕ) (b : B), y * φ a ^ n = φ b := by
    intro y
    obtain ⟨n, b, hb⟩ := lift0 y
    obtain ⟨m, c, hc⟩ := fracMem _ hb
    refine ⟨n + m, c + b * a ^ m, ?_⟩
    rw [map_add, map_mul, map_pow, ← hc]
    ring

  have kerI : ∀ x : B, φ x = 0 → ∃ n : ℕ, a ^ n * x ∈ I.map (algebraMap R B) := by
    intro x hx
    have h : algebraMap B₀ B₀' (p x) = 0 := by rw [← hcomm, hx, map_zero]
    obtain ⟨⟨s, hs⟩, h2⟩ :=
      (IsLocalization.map_eq_zero_iff (M := Submonoid.powers (p a)) (S := B₀') (p x)).mp h
    obtain ⟨n, rfl⟩ := hs
    refine ⟨n, (hker _).mp ?_⟩
    rw [map_mul, map_pow]
    exact h2
  have core : ∀ x ∈ I.map (algebraMap R B), φ x = 0 → ∃ N : ℕ, a ^ N * x = 0 := by
    intro x hxI hx
    change x ∈ Submodule.span B (algebraMap R B '' I) at hxI
    obtain ⟨k, c, g, rfl⟩ := Submodule.mem_span_set'.mp hxI
    choose i hi hgi using fun j => (g j).2
    have hrel : ∑ j, i j • φ (c j) = 0 := by
      rw [← hx, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_eq_mul, map_mul, Algebra.smul_def, ← hgi j, hφ,
        IsScalarTower.algebraMap_apply R B B', mul_comm]
    obtain ⟨l, A, y, hy, hA⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero
      (R := R) (M := B') (f := i) (x := fun j => φ (c j)) hrel
    choose m d hd using fun j => surj (y j)
    obtain ⟨M, hMdef⟩ : ∃ M, M = ∑ j, m j := ⟨_, rfl⟩
    have hMle : ∀ j, m j ≤ M := fun j => hMdef ▸
      Finset.single_le_sum (fun j _ => Nat.zero_le (m j)) (Finset.mem_univ j)
    have hM : ∀ j, y j * φ a ^ M = φ (d j * a ^ (M - m j)) := by
      intro j
      obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le (hMle j)
      rw [ht, Nat.add_sub_cancel_left, map_mul, map_pow, ← hd j, pow_add]
      ring
    have he : ∀ q, φ (c q * a ^ M - ∑ j, A q j • (d j * a ^ (M - m j))) = 0 := by
      intro q
      rw [map_sub, map_mul, map_pow, map_sum]
      simp_rw [hφs, ← hM]
      rw [show φ (c q) = ∑ j, A q j • y j from hy q, Finset.sum_mul]
      simp [smul_mul_assoc]
    choose n' hn' using fun q => kerI _ (he q)
    obtain ⟨N, hNdef⟩ : ∃ N, N = ∑ q, n' q := ⟨_, rfl⟩
    have hNle : ∀ q, n' q ≤ N := fun q => hNdef ▸
      Finset.single_le_sum (fun q _ => Nat.zero_le (n' q)) (Finset.mem_univ q)
    have hz : ∀ q, algebraMap R B (i q) *
        (a ^ N * (c q * a ^ M - ∑ j, A q j • (d j * a ^ (M - m j)))) = 0 := by
      intro q
      obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le (hNle q)
      rw [ht, pow_add, mul_comm (a ^ n' q), mul_assoc, mul_left_comm,
        mul_eq_zero_of_mem_map hI (Ideal.mem_map_of_mem _ (hi q)) (hn' q), mul_zero]
    refine ⟨N + M, ?_⟩
    have step : ∀ q, a ^ (N + M) * (c q • (g q : B)) =
        ∑ j, algebraMap R B (i q * A q j) * (a ^ N * (d j * a ^ (M - m j))) := by
      intro q
      have h1 := hz q
      rw [← hgi q, smul_eq_mul]
      simp_rw [map_mul, Algebra.smul_def] at h1 ⊢
      rw [mul_sub, mul_sub, sub_eq_zero, Finset.mul_sum, Finset.mul_sum] at h1
      calc a ^ (N + M) * (c q * algebraMap R B (i q))
          = algebraMap R B (i q) * (a ^ N * (c q * a ^ M)) := by ring
        _ = ∑ j, algebraMap R B (i q) * (a ^ N * (algebraMap R B (A q j) * (d j * a ^ (M - m j)))) := h1
        _ = _ := Finset.sum_congr rfl fun j _ => by ring
    rw [Finset.mul_sum, Finset.sum_congr rfl fun q _ => step q, Finset.sum_comm]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [← Finset.sum_mul, ← map_sum, hA j, map_zero, zero_mul]
  have kerAll : ∀ x : B, φ x = 0 → ∃ N : ℕ, a ^ N * x = 0 := by
    intro x hx
    obtain ⟨n, hn⟩ := kerI x hx
    obtain ⟨N, hN⟩ := core _ hn (by rw [map_mul, hx, mul_zero])
    exact ⟨N + n, by rw [pow_add, mul_assoc, hN]⟩
  refine (isLocalization_iff _ _).mpr ⟨?_, ?_, ?_⟩
  · rintro ⟨_, n, rfl⟩
    exact (map_pow φ a n).symm ▸ hunit.pow n
  · intro y
    obtain ⟨n, b, hb⟩ := surj y
    exact ⟨(b, ⟨a ^ n, n, rfl⟩), by simpa only [map_pow] using hb⟩
  · intro x y hxy
    obtain ⟨n, hn⟩ := kerAll (x - y) (by rw [map_sub, hxy, sub_self])
    exact ⟨⟨a ^ n, n, rfl⟩, by rw [← sub_eq_zero, ← mul_sub]; exact hn⟩

end GlobalTheory.LiftAway
