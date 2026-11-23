import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotRedOfMem
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.WeierstrassCurvePointOfLatticeAddOfGeneric

open Formalism.L2.Th1.F GlobalTheory.Klein
open scoped ComplexConjugate BigOperators

namespace GlobalTheory.Klein

private theorem ultra_add_le {K : Type*} [NormedField K] [IsUltrametricDist K] {x y : K} {C : ℝ}
    (hx : ‖x‖ ≤ C) (hy : ‖y‖ ≤ C) : ‖x + y‖ ≤ C :=
  (IsUltrametricDist.norm_add_le_max x y).trans (max_le hx hy)

private theorem mul_le_of {K : Type*} [NormedField K] {x y : K} {C D : ℝ}
    (hx : ‖x‖ ≤ C) (hy : ‖y‖ ≤ D) : ‖x * y‖ ≤ C * D := by
  rw [norm_mul]
  exact mul_le_mul hx hy (norm_nonneg _) ((norm_nonneg _).trans hx)

private theorem cubic_le {K : Type*} [NormedField K] [IsUltrametricDist K] {x k₂ k₁ k₀ : K} {ρ : ℝ}
    (h2 : ‖(2 : K)‖ = 1) (hρ : 1 ≤ ρ) (hx : ‖x‖ ≤ ρ) (hk₂ : ‖k₂‖ ≤ 1) (hk₁ : ‖k₁‖ ≤ 1) (hk₀ : ‖k₀‖ ≤ 1) :
    ‖2 * 2 * (x * x * x) + k₂ * (x * x) + k₁ * x + k₀‖ ≤ ρ * ρ * ρ := by
  have h1 : 1 ≤ ρ * ρ := by nlinarith
  refine ultra_add_le (ultra_add_le (ultra_add_le ?_ ?_) ?_) ?_
  · simpa using mul_le_of (mul_le_of h2.le h2.le) (mul_le_of (mul_le_of hx hx) hx)
  · exact (mul_le_of hk₂ (mul_le_of hx hx)).trans (by nlinarith)
  · exact (mul_le_of hk₁ hx).trans (by nlinarith)
  · exact hk₀.trans (by nlinarith)

private theorem le_of_mul_self_le_mul_self' {x y : ℝ} (h : x * x ≤ y * y) (hy : 0 ≤ y) : x ≤ y :=
  (abs_le_of_sq_le_sq' (by simpa only [sq] using h) hy).2

theorem chord_norm_le_one {K : Type*} [NormedField K] [IsUltrametricDist K] {a b A B X k₂ k₁ k₀ : K}
    (h2 : ‖(2 : K)‖ = 1) (ha : 1 < ‖a‖) (hb : ‖b‖ ≤ 1) (hk₂ : ‖k₂‖ ≤ 1) (hk₁ : ‖k₁‖ ≤ 1) (hk₀ : ‖k₀‖ ≤ 1)
    (hA : A ^ 2 = 4 * a ^ 3 + k₂ * a ^ 2 + k₁ * a + k₀)
    (hB : B ^ 2 = 4 * b ^ 3 + k₂ * b ^ 2 + k₁ * b + k₀)
    (hX : 4 * (a - b) ^ 2 * X = (A - B) ^ 2 - (4 * (a + b) + k₂) * (a - b) ^ 2) : ‖X‖ ≤ 1 := by
  set ρ := ‖a‖ with hρ
  have haa : ‖a‖ ≤ ρ := le_rfl
  have hab : ‖a - b‖ = ρ := by
    rw [sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_neg]; linarith),
      norm_neg, max_eq_left (by linarith)]
  have hA' : ‖A‖ * ‖A‖ ≤ ρ * ρ * ρ := by
    rw [← norm_mul, show A * A = 2 * 2 * (a * a * a) + k₂ * (a * a) + k₁ * a + k₀ by
      linear_combination hA]
    exact cubic_le h2 ha.le haa hk₂ hk₁ hk₀
  have hB' : ‖B‖ * ‖B‖ ≤ 1 * 1 * 1 := by
    rw [← norm_mul, show B * B = 2 * 2 * (b * b * b) + k₂ * (b * b) + k₁ * b + k₀ by
      linear_combination hB]
    exact cubic_le h2 le_rfl hb hk₂ hk₁ hk₀
  have h1 : 1 ≤ ρ * ρ := by nlinarith
  have hρρ : ρ ≤ ρ * ρ := by nlinarith
  have hA1 : ‖A‖ ≤ ρ * ρ := by
    exact le_of_mul_self_le_mul_self' (hA'.trans (by nlinarith)) (by linarith)
  have hB1 : ‖B‖ ≤ 1 := by
    exact le_of_mul_self_le_mul_self' (hB'.trans (by norm_num)) (by linarith)
  have hN : 2 * 2 * ((a - b) * (a - b)) * X =
      2 * 2 * b * (a * (a + b)) + 2 * k₂ * b * a + k₁ * (a + b) + 2 * k₀ + 2 * B * (-A) := by
    linear_combination hX + hA + hB
  have hs : ‖a + b‖ ≤ ρ := ultra_add_le haa (by linarith)
  have hn : ‖2 * 2 * b * (a * (a + b)) + 2 * k₂ * b * a + k₁ * (a + b) + 2 * k₀ + 2 * B * (-A)‖
      ≤ ρ * ρ := by
    refine ultra_add_le (ultra_add_le (ultra_add_le (ultra_add_le ?_ ?_) ?_) ?_) ?_
    · simpa using mul_le_of (mul_le_of (mul_le_of h2.le h2.le) hb) (mul_le_of haa hs)
    · exact (mul_le_of (mul_le_of (mul_le_of h2.le hk₂) hb) haa).trans (by linarith)
    · exact (mul_le_of hk₁ hs).trans (by linarith)
    · exact (mul_le_of h2.le hk₀).trans (by linarith)
    · exact (mul_le_of (mul_le_of h2.le hB1) ((norm_neg A).le.trans hA1)).trans (by linarith)
  rw [← hN, norm_mul, norm_mul, norm_mul, norm_mul, h2, hab] at hn
  by_contra hc
  push_neg at hc
  nlinarith

theorem norm_two_of_ne {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) : ‖(2 : ℂ_[p])‖ = 1 := by
  have h : ‖((2 : ℕ) : ℚ_[p])‖ = 1 := by
    rw [Padic.norm_natCast_eq_one_iff]
    exact (Nat.coprime_primes Fact.out Nat.prime_two).2 hp
  have e : (2 : ℂ_[p]) = algebraMap ℚ_[p] ℂ_[p] ((2 : ℕ) : ℚ_[p]) := by
    rw [map_natCast]; norm_num
  rw [e, norm_algebraMap', h]

variable {p : ℕ} [Fact p.Prime]

theorem Red.neg {ι : ℂ ≃+* ℂ_[p]} {L : PeriodPair} {r z : ℂ} (h : Red ι L r z) : Red ι L r (-z) :=
  ⟨fun h' => h.1 (by simpa using h'), by rw [L.weierstrassP_neg]; exact h.2⟩

theorem Red.add_lattice {ι : ℂ ≃+* ℂ_[p]} {L : PeriodPair} {r z ω : ℂ} (h : Red ι L r z)
    (hω : ω ∈ L.lattice) : Red ι L r (z + ω) :=
  ⟨fun h' => h.1 ((L.lattice.add_mem_iff_left hω).1 h'), by
    have e : L.weierstrassP (z + ω) = L.weierstrassP z := L.weierstrassP_add_coe z ⟨ω, hω⟩
    rw [e]; exact h.2⟩

theorem Red.add_of_not {ι : ℂ ≃+* ℂ_[p]} {L : PeriodPair} {r u w : ℂ} (hg : Good ι L r)
    (hu : ¬ Red ι L r u) (hw : Red ι L r w) : Red ι L r (u + w) := by
  by_cases hL : u ∈ L.lattice
  · rw [add_comm]; exact hw.add_lattice hL
  have ha : 1 < ‖ι (L.weierstrassP u - r)‖ := not_le.1 fun h => hu ⟨hL, h⟩
  have hne : L.weierstrassP u ≠ L.weierstrassP w := fun h => by
    rw [h] at ha; exact absurd hw.2 (not_le.2 ha)
  refine ⟨fun h => hu ?_, ?_⟩
  · have := hw.neg.add_lattice h
    rwa [show -w + (u + w) = u by ring] at this
  obtain ⟨hp, hk₂, hk₁, hk₀, -⟩ := hg
  have hs := (GlobalTheory.weierstrassP_add L hL hw.1 hne).1
  have e1 := L.derivWeierstrassP_sq u hL
  have e2 := L.derivWeierstrassP_sq w hw.1
  have hd := sub_ne_zero.2 hne
  have key : ∀ x y : ℂ, y ^ 2 = 4 * x ^ 3 - L.g₂ * x - L.g₃ →
      ι y ^ 2 = 4 * ι (x - r) ^ 3 + ι (12 * r) * ι (x - r) ^ 2 + ι (12 * r ^ 2 - L.g₂) * ι (x - r)
        + ι (4 * r ^ 3 - L.g₂ * r - L.g₃) := fun x y h => by
    have : y ^ 2 = 4 * (x - r) ^ 3 + (12 * r) * (x - r) ^ 2 + (12 * r ^ 2 - L.g₂) * (x - r)
        + (4 * r ^ 3 - L.g₂ * r - L.g₃) := by linear_combination h
    rw [← map_pow, this, map_add, map_add, map_add, map_mul ι 4, map_mul ι (12 * r),
      map_mul ι _ (x - r), map_pow, map_pow, map_ofNat]
  refine chord_norm_le_one (norm_two_of_ne hp) ha hw.2 hk₂ hk₁ hk₀ (key _ _ e1) (key _ _ e2) ?_
  have : 4 * ((L.weierstrassP u - r) - (L.weierstrassP w - r)) ^ 2 * (L.weierstrassP (u + w) - r)
      = (L.derivWeierstrassP u - L.derivWeierstrassP w) ^ 2
        - (4 * ((L.weierstrassP u - r) + (L.weierstrassP w - r)) + 12 * r)
          * ((L.weierstrassP u - r) - (L.weierstrassP w - r)) ^ 2 := by
    rw [hs]; field_simp; ring
  have := congrArg ι this
  simpa only [map_mul, map_sub, map_add, map_pow, map_ofNat] using this

theorem not_red_addSubgroup : ∀ (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) (L : PeriodPair) (r : ℂ), Good ι L r → (∀ z, Red ι L r z → Red ι L r (-z)) ∧ (∀ z, Red ι L r z → ∀ ω ∈ L.lattice, Red ι L r (z + ω)) ∧ (∀ u w, ¬ Red ι L r u → Red ι L r w → Red ι L r (u + w)) ∧ ∃ G : AddSubgroup ℂ, (∀ z, z ∈ G ↔ ¬ Red ι L r z) ∧ ∀ ω ∈ L.lattice, ω ∈ G := by
  intro p _ ι L r hg
  refine ⟨fun z h => h.neg, fun z h ω hω => h.add_lattice hω, fun u w hu hw => Red.add_of_not hg hu hw, ?_⟩
  have hneg : ∀ {z : ℂ}, ¬ Red ι L r z → ¬ Red ι L r (-z) := fun hz h => hz (by simpa using h.neg)
  refine ⟨{ carrier := {z | ¬ Red ι L r z}
            add_mem' := fun {u v} hu hv h => hu ?_
            zero_mem' := not_red_of_mem ι L r L.lattice.zero_mem
            neg_mem' := hneg }, fun z => Iff.rfl, fun ω hω => not_red_of_mem ι L r hω⟩
  have := Red.add_of_not hg (hneg hv) h
  rwa [show -v + (u + v) = u by ring] at this

end GlobalTheory.Klein
