import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RatBasisLinearIndependentInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDividedPowersOfCompOnGeneratorsStatement
open DividedPowers GlobalTheory.Cris GlobalTheory.PDA

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SplitDP

open Finset

theorem conv_mul_choose {R : Type} [CommRing R] (f g : ℕ → R)
    (hf : ∀ a c, f a * f c = ((a + c).choose a : R) * f (a + c))
    (hg : ∀ b d, g b * g d = ((b + d).choose b : R) * g (b + d)) (m n : ℕ) :
    (∑ p ∈ antidiagonal m, f p.1 * g p.2) * (∑ q ∈ antidiagonal n, f q.1 * g q.2) =
      ((m + n).choose m : R) * ∑ r ∈ antidiagonal (m + n), f r.1 * g r.2 := by
  have inner : ∀ p ∈ antidiagonal m,
      ∑ q ∈ antidiagonal n, ((p.1 + q.1).choose p.1 : R) * ((p.2 + q.2).choose p.2 : R) *
          (f (p.1 + q.1) * g (p.2 + q.2)) =
        ∑ r ∈ antidiagonal (m + n), ((r.1.choose p.1 : R) * (r.2.choose p.2 : R)) * (f r.1 * g r.2) := by
    intro p hp
    rw [HasAntidiagonal.mem_antidiagonal] at hp
    have hsub : (antidiagonal n).image (fun q : ℕ × ℕ ↦ (p.1 + q.1, p.2 + q.2)) ⊆ antidiagonal (m + n) := by
      intro r hr
      simp only [mem_image, HasAntidiagonal.mem_antidiagonal] at hr ⊢
      obtain ⟨q, hq, rfl⟩ := hr
      simp only
      omega
    rw [← sum_subset hsub, sum_image]
    · intro q _ q' _ h
      simp only [Prod.mk.injEq] at h
      exact Prod.ext (by omega) (by omega)
    · intro r hr hn
      rw [HasAntidiagonal.mem_antidiagonal] at hr
      by_cases h1 : p.1 ≤ r.1
      · by_cases h2 : p.2 ≤ r.2
        · exfalso
          apply hn
          rw [mem_image]
          exact ⟨(r.1 - p.1, r.2 - p.2), by rw [HasAntidiagonal.mem_antidiagonal]; omega,
            Prod.ext (by simp only; omega) (by simp only; omega)⟩
        · rw [Nat.choose_eq_zero_of_lt (by omega : r.2 < p.2)]
          simp
      · rw [Nat.choose_eq_zero_of_lt (by omega : r.1 < p.1)]
        simp
  calc (∑ p ∈ antidiagonal m, f p.1 * g p.2) * (∑ q ∈ antidiagonal n, f q.1 * g q.2)
      = ∑ p ∈ antidiagonal m, ∑ q ∈ antidiagonal n, ((p.1 + q.1).choose p.1 : R) *
          ((p.2 + q.2).choose p.2 : R) * (f (p.1 + q.1) * g (p.2 + q.2)) := by
        rw [sum_mul_sum]
        refine sum_congr rfl fun p _ ↦ sum_congr rfl fun q _ ↦ ?_
        calc f p.1 * g p.2 * (f q.1 * g q.2) = (f p.1 * f q.1) * (g p.2 * g q.2) := by ring
          _ = _ := by rw [hf, hg]; ring
    _ = ∑ p ∈ antidiagonal m, ∑ r ∈ antidiagonal (m + n),
          ((r.1.choose p.1 : R) * (r.2.choose p.2 : R)) * (f r.1 * g r.2) := sum_congr rfl inner
    _ = ∑ r ∈ antidiagonal (m + n),
          (∑ p ∈ antidiagonal m, (r.1.choose p.1 : R) * (r.2.choose p.2 : R)) * (f r.1 * g r.2) := by
        rw [sum_comm]
        simp only [sum_mul]
    _ = _ := by
        rw [mul_sum]
        refine sum_congr rfl fun r hr ↦ ?_
        rw [HasAntidiagonal.mem_antidiagonal] at hr
        rw [← hr, Nat.add_choose_eq]
        push_cast
        rfl

variable {B : Type} [CommRing B] {J : Ideal B} {P : Type} [CommRing P] [Algebra B P]
  {𝔞 : Ideal P}

def th (δ : DividedPowers J) (ε : P →ₐ[B] B) (η : DividedPowers 𝔞) (n : ℕ) (x : P) : P :=
  ∑ p ∈ antidiagonal n, algebraMap B P (δ.dpow p.1 (ε x)) * η.dpow p.2 (x - algebraMap B P (ε x))

variable {δ : DividedPowers J} {ε : P →ₐ[B] B} {η : DividedPowers 𝔞}

theorem sub_mem_aug (h𝔞 : ∀ p, p ∈ 𝔞 ↔ ε p = 0) (x : P) : x - algebraMap B P (ε x) ∈ 𝔞 :=
  (h𝔞 _).2 (by simp)

theorem mem_ext_iff (h𝔞 : ∀ p, p ∈ 𝔞 ↔ ε p = 0) (x : P) :
    x ∈ J.map (algebraMap B P) ⊔ 𝔞 ↔ ε x ∈ J := by
  constructor
  · intro hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    have hy' : y ∈ J.comap ε := by
      refine Ideal.map_le_iff_le_comap.2 ?_ hy
      intro a ha
      simp [Ideal.mem_comap, ha]
    rw [map_add, (h𝔞 z).1 hz, add_zero]
    exact hy'
  · intro h
    have hx : x = algebraMap B P (ε x) + (x - algebraMap B P (ε x)) := by ring
    rw [hx]
    exact Submodule.add_mem_sup (Ideal.mem_map_of_mem _ h) (sub_mem_aug h𝔞 x)

theorem th_of_mem (h𝔞 : ∀ p, p ∈ 𝔞 ↔ ε p = 0) {y : P} (hy : y ∈ 𝔞) (n : ℕ) :
    th δ ε η n y = η.dpow n y := by
  simp only [th, (h𝔞 y).1 hy, map_zero, sub_zero]
  rw [sum_eq_single (0, n)]
  · rw [δ.dpow_zero J.zero_mem, map_one, one_mul]
  · intro p hp hne
    rw [HasAntidiagonal.mem_antidiagonal] at hp
    have : p.1 ≠ 0 := fun h ↦ hne (Prod.ext h (by simp only; omega))
    rw [δ.dpow_eval_zero this, map_zero, zero_mul]
  · intro h
    exact absurd (HasAntidiagonal.mem_antidiagonal.2 (zero_add n)) h

theorem th_algebraMap (j : B) (n : ℕ) : th δ ε η n (algebraMap B P j) = algebraMap B P (δ.dpow n j) := by
  simp only [th, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self]
  rw [sum_eq_single (n, 0)]
  · rw [η.dpow_zero 𝔞.zero_mem, mul_one]
  · intro p hp hne
    rw [HasAntidiagonal.mem_antidiagonal] at hp
    have : p.2 ≠ 0 := fun h ↦ hne (Prod.ext (by simp only; omega) h)
    rw [η.dpow_eval_zero this, mul_zero]
  · intro h
    exact absurd (HasAntidiagonal.mem_antidiagonal.2 (add_zero n)) h

theorem th_null (h𝔞 : ∀ p, p ∈ 𝔞 ↔ ε p = 0) (n : ℕ) (x : P) (hx : x ∉ J.map (algebraMap B P) ⊔ 𝔞) :
    th δ ε η n x = 0 := by
  rw [mem_ext_iff h𝔞] at hx
  refine sum_eq_zero fun p _ ↦ ?_
  rw [δ.dpow_null hx, map_zero, zero_mul]

theorem th_zero (h𝔞 : ∀ p, p ∈ 𝔞 ↔ ε p = 0) (x : P) (hx : x ∈ J.map (algebraMap B P) ⊔ 𝔞) :
    th δ ε η 0 x = 1 := by
  rw [mem_ext_iff h𝔞] at hx
  simp [th, δ.dpow_zero hx, η.dpow_zero (sub_mem_aug h𝔞 x)]

theorem th_one (h𝔞 : ∀ p, p ∈ 𝔞 ↔ ε p = 0) (x : P) (hx : x ∈ J.map (algebraMap B P) ⊔ 𝔞) :
    th δ ε η 1 x = x := by
  rw [mem_ext_iff h𝔞] at hx
  simp [th, Finset.Nat.antidiagonal_succ, δ.dpow_zero hx, δ.dpow_one hx, η.dpow_zero (sub_mem_aug h𝔞 x),
    η.dpow_one (sub_mem_aug h𝔞 x)]

theorem th_mem (h𝔞 : ∀ p, p ∈ 𝔞 ↔ ε p = 0) (n : ℕ) (hn : n ≠ 0) (x : P)
    (hx : x ∈ J.map (algebraMap B P) ⊔ 𝔞) : th δ ε η n x ∈ J.map (algebraMap B P) ⊔ 𝔞 := by
  have hu := (mem_ext_iff h𝔞 x).1 hx
  refine Ideal.sum_mem _ fun p hp ↦ ?_
  rw [HasAntidiagonal.mem_antidiagonal] at hp
  by_cases h1 : p.1 = 0
  · exact Ideal.mul_mem_left _ _
      (Ideal.mem_sup_right (η.dpow_mem (by omega) (sub_mem_aug h𝔞 x)))
  · exact Ideal.mul_mem_right _ _ (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ (δ.dpow_mem h1 hu)))

theorem mk_th (x : P) :
    PowerSeries.mk (fun k ↦ th δ ε η k x) =
      PowerSeries.mk (fun k ↦ algebraMap B P (δ.dpow k (ε x))) *
        PowerSeries.mk (fun k ↦ η.dpow k (x - algebraMap B P (ε x))) := by
  ext k
  simp [PowerSeries.coeff_mul, th]

theorem th_add (h𝔞 : ∀ p, p ∈ 𝔞 ↔ ε p = 0) (n : ℕ) (x : P) (hx : x ∈ J.map (algebraMap B P) ⊔ 𝔞)
    (y : P) (hy : y ∈ J.map (algebraMap B P) ⊔ 𝔞) :
    th δ ε η n (x + y) = ∑ k ∈ antidiagonal n, th δ ε η k.1 x * th δ ε η k.2 y := by
  have hu := (mem_ext_iff h𝔞 x).1 hx
  have hv := (mem_ext_iff h𝔞 y).1 hy
  have hA : PowerSeries.mk (fun k ↦ algebraMap B P (δ.dpow k (ε (x + y)))) =
      PowerSeries.mk (fun k ↦ algebraMap B P (δ.dpow k (ε x))) *
        PowerSeries.mk (fun k ↦ algebraMap B P (δ.dpow k (ε y))) := by
    ext k
    simp only [PowerSeries.coeff_mul, PowerSeries.coeff_mk, map_add]
    rw [δ.dpow_add hu hv, map_sum]
    simp only [map_mul]
  have hE : PowerSeries.mk (fun k ↦ η.dpow k (x + y - algebraMap B P (ε (x + y)))) =
      PowerSeries.mk (fun k ↦ η.dpow k (x - algebraMap B P (ε x))) *
        PowerSeries.mk (fun k ↦ η.dpow k (y - algebraMap B P (ε y))) := by
    ext k
    simp only [PowerSeries.coeff_mul, PowerSeries.coeff_mk]
    have e : x + y - algebraMap B P (ε (x + y)) =
        (x - algebraMap B P (ε x)) + (y - algebraMap B P (ε y)) := by
      rw [map_add, map_add]; ring
    rw [e, η.dpow_add (sub_mem_aug h𝔞 x) (sub_mem_aug h𝔞 y)]
  have key : PowerSeries.mk (fun k ↦ th δ ε η k (x + y)) =
      PowerSeries.mk (fun k ↦ th δ ε η k x) * PowerSeries.mk (fun k ↦ th δ ε η k y) := by
    rw [mk_th, mk_th, mk_th, hA, hE]
    ring
  have := congrArg (PowerSeries.coeff n) key
  simpa [PowerSeries.coeff_mul] using this

theorem th_mul_dpow (h𝔞 : ∀ p, p ∈ 𝔞 ↔ ε p = 0) (m n : ℕ) (x : P)
    (hx : x ∈ J.map (algebraMap B P) ⊔ 𝔞) :
    th δ ε η m x * th δ ε η n x = ((m + n).choose m : P) * th δ ε η (m + n) x := by
  have hu := (mem_ext_iff h𝔞 x).1 hx
  refine conv_mul_choose (fun k ↦ algebraMap B P (δ.dpow k (ε x)))
    (fun k ↦ η.dpow k (x - algebraMap B P (ε x))) (fun a c ↦ ?_) (fun b d ↦ ?_) m n
  · beta_reduce
    rw [← map_mul, δ.mul_dpow hu, map_mul, map_natCast]
  · exact η.mul_dpow (sub_mem_aug h𝔞 x)

theorem th_mul_alg (h𝔞 : ∀ p, p ∈ 𝔞 ↔ ε p = 0) (n : ℕ) (β : B) (x : P)
    (hx : x ∈ J.map (algebraMap B P) ⊔ 𝔞) :
    th δ ε η n (algebraMap B P β * x) = algebraMap B P β ^ n * th δ ε η n x := by
  have hu := (mem_ext_iff h𝔞 x).1 hx
  have e1 : ε (algebraMap B P β * x) = β * ε x := by simp
  have e2 : algebraMap B P β * x - algebraMap B P (ε (algebraMap B P β * x)) =
      algebraMap B P β * (x - algebraMap B P (ε x)) := by
    rw [e1, map_mul]; ring
  rw [th, th, e2, e1, mul_sum]
  refine sum_congr rfl fun p hp ↦ ?_
  rw [HasAntidiagonal.mem_antidiagonal] at hp
  rw [δ.dpow_mul hu, η.dpow_mul (sub_mem_aug h𝔞 x), map_mul, map_pow, ← hp, pow_add]
  ring

theorem th_mul_aug (h𝔞 : ∀ p, p ∈ 𝔞 ↔ ε p = 0) (n : ℕ) {q : P} (hq : q ∈ 𝔞) (x : P)
    (hx : x ∈ J.map (algebraMap B P) ⊔ 𝔞) :
    th δ ε η n (q * x) = q ^ n * th δ ε η n x := by
  have hu := (mem_ext_iff h𝔞 x).1 hx
  have hr := sub_mem_aug h𝔞 x
  rw [th_of_mem h𝔞 (Ideal.mul_mem_right x 𝔞 hq)]
  have e : q * x = algebraMap B P (ε x) * q + q * (x - algebraMap B P (ε x)) := by ring
  rw [e, η.dpow_add (Ideal.mul_mem_left _ _ hq) (Ideal.mul_mem_left _ _ hr), th, mul_sum]
  refine sum_congr rfl fun p hp ↦ ?_
  rw [HasAntidiagonal.mem_antidiagonal] at hp
  have hk : algebraMap B P (ε x) ^ p.1 * η.dpow p.1 q = algebraMap B P (δ.dpow p.1 (ε x)) * q ^ p.1 := by
    rw [← η.factorial_mul_dpow_eq_pow hq, ← map_pow, ← δ.factorial_mul_dpow_eq_pow hu, map_mul, map_natCast]
    ring
  rw [η.dpow_mul hq, η.dpow_mul hr, ← mul_assoc, hk, ← hp, pow_add]
  ring

theorem th_mul (h𝔞 : ∀ p, p ∈ 𝔞 ↔ ε p = 0) (n : ℕ) (c x : P) (hx : x ∈ J.map (algebraMap B P) ⊔ 𝔞) :
    th δ ε η n (c * x) = c ^ n * th δ ε η n x := by
  obtain ⟨β, q, hq, rfl⟩ : ∃ β q, q ∈ 𝔞 ∧ c = algebraMap B P β + q :=
    ⟨ε c, _, sub_mem_aug h𝔞 c, by ring⟩
  have h1 : algebraMap B P β * x ∈ J.map (algebraMap B P) ⊔ 𝔞 := Ideal.mul_mem_left _ _ hx
  have h2 : q * x ∈ J.map (algebraMap B P) ⊔ 𝔞 := Ideal.mul_mem_left _ _ hx
  rw [add_mul, th_add h𝔞 n _ h1 _ h2, (Commute.all _ _).add_pow', sum_mul]
  refine sum_congr rfl fun p hp ↦ ?_
  rw [HasAntidiagonal.mem_antidiagonal] at hp
  rw [th_mul_alg h𝔞 _ _ _ hx, th_mul_aug h𝔞 _ hq _ hx, nsmul_eq_mul]
  calc algebraMap B P β ^ p.1 * th δ ε η p.1 x * (q ^ p.2 * th δ ε η p.2 x)
      = algebraMap B P β ^ p.1 * q ^ p.2 * (th δ ε η p.1 x * th δ ε η p.2 x) := by ring
    _ = _ := by rw [th_mul_dpow h𝔞 _ _ _ hx, hp]; ring

theorem isPreDividedPowers_th (h𝔞 : ∀ p, p ∈ 𝔞 ↔ ε p = 0) :
    IsPreDP (J.map (algebraMap B P) ⊔ 𝔞) (th δ ε η) where
  null n x hx := th_null h𝔞 n x hx
  zero x hx := th_zero h𝔞 x hx
  one x hx := th_one h𝔞 x hx
  mem n hn x hx := th_mem h𝔞 n hn x hx
  add n x hx y hy := th_add h𝔞 n x hx y hy
  mul n c x hx := th_mul h𝔞 n c x hx
  mul_dpow m n x hx := th_mul_dpow h𝔞 m n x hx

theorem ext_eq_span : J.map (algebraMap B P) ⊔ 𝔞 = Ideal.span (algebraMap B P '' (J : Set B) ∪ (𝔞 : Set P)) := by
  rw [Ideal.span_union, Ideal.span_eq]
  rfl

theorem th_comp (h𝔞 : ∀ p, p ∈ 𝔞 ↔ ε p = 0) :
    ∀ x ∈ algebraMap B P '' (J : Set B) ∪ (𝔞 : Set P), ∀ m n : ℕ, n ≠ 0 →
      th δ ε η m (th δ ε η n x) = (m.uniformBell n : P) * th δ ε η (m * n) x := by
  rintro x (⟨j, hj, rfl⟩ | hx) m n hn
  · rw [th_algebraMap, th_algebraMap, th_algebraMap, δ.dpow_comp hn hj, map_mul, map_natCast]
  · rw [th_of_mem h𝔞 hx n, th_of_mem h𝔞 (η.dpow_mem hn hx), th_of_mem h𝔞 hx, η.dpow_comp hn hx]

theorem exists_dp_ext : ∀ (B : Type) [CommRing B] (J : Ideal B) (δ : DividedPowers J) (P : Type) [CommRing P]
    [Algebra B P] (ε : P →ₐ[B] B) (𝔞 : Ideal P) (η : DividedPowers 𝔞), (∀ p, p ∈ 𝔞 ↔ ε p = 0) →
    ∃ θ : DividedPowers (J.map (algebraMap B P) ⊔ 𝔞), IsDPMorphism δ θ (algebraMap B P) ∧
      ∀ n, ∀ p ∈ 𝔞, θ.dpow n p = η.dpow n p := by
  intro B _ J δ P _ _ ε 𝔞 η h𝔞
  obtain ⟨θ, hθ⟩ := GlobalTheory.T.exists_dividedPowers_of_comp_on_generators P (J.map (algebraMap B P) ⊔ 𝔞) (th δ ε η) _ (isPreDividedPowers_th h𝔞)
    ext_eq_span (th_comp h𝔞)
  refine ⟨θ, ⟨le_sup_left, fun {n} a _ ↦ ?_⟩, fun n p hp ↦ ?_⟩
  · rw [hθ, th_algebraMap]
  · rw [hθ, th_of_mem h𝔞 hp]

end GlobalTheory.SplitDP
