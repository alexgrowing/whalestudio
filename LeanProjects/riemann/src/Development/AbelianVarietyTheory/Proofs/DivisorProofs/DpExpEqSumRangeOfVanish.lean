import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham

namespace GlobalTheory.Cris

variable {B B' : Type} [CommRing B] [CommRing B'] {J : Ideal B} {J' : Ideal B'}

set_option autoImplicit false in
open CategoryTheory AlgebraicGeometry DividedPowers in
variable {B B' : Type} [CommRing B] [CommRing B'] {J : Ideal B} {J' : Ideal B'} in

theorem _root_.GlobalTheory.Cris.dpExp_eq_sum_range_of_vanish (δ : DividedPowers J) (a : B) (N : ℕ)
    (h : ∀ n, N ≤ n → δ.dpow n a = 0) :
    _root_.GlobalTheory.Cris.dpExp δ a = ∑ n ∈ Finset.range N, δ.dpow n a := by
  unfold _root_.GlobalTheory.Cris.dpExp
  apply finsum_eq_sum_of_support_subset
  intro n hn
  simp only [Finset.coe_range, Set.mem_Iio]
  by_contra hlt
  exact hn (h n (not_lt.mp hlt))

set_option autoImplicit false in
open CategoryTheory AlgebraicGeometry DividedPowers in
variable {B B' : Type} [CommRing B] [CommRing B'] {J : Ideal B} {J' : Ideal B'} in

theorem _root_.GlobalTheory.Cris.IsNilDP.dpExp_add_eq_mul {δ : DividedPowers J}
    (h : _root_.GlobalTheory.Cris.IsNilDP δ) {a b : B} (ha : a ∈ J) (hb : b ∈ J) :
    _root_.GlobalTheory.Cris.dpExp δ (a + b) = _root_.GlobalTheory.Cris.dpExp δ a * _root_.GlobalTheory.Cris.dpExp δ b := by
  obtain ⟨N, hN⟩ := h
  have hvan : ∀ x ∈ J, ∀ n, N ≤ n → δ.dpow n x = 0 := by
    intro x hx n hn
    simpa using hN [(n, x)] (by simpa using hx) (by simpa using hn)
  have hpair : ∀ i j, N ≤ i + j → δ.dpow i a * δ.dpow j b = 0 := by
    intro i j hij
    simpa using hN [(i, a), (j, b)] (by simp [ha, hb]) (by simpa using hij)
  let F : ℕ × ℕ → B := fun p => δ.dpow p.1 a * δ.dpow p.2 b
  rw [_root_.GlobalTheory.Cris.dpExp_eq_sum_range_of_vanish δ (a + b) N (hvan _ (J.add_mem ha hb)),
    _root_.GlobalTheory.Cris.dpExp_eq_sum_range_of_vanish δ a N (hvan a ha), _root_.GlobalTheory.Cris.dpExp_eq_sum_range_of_vanish δ b N (hvan b hb),
    Finset.sum_mul_sum, ← Finset.sum_product' (f := fun i j => δ.dpow i a * δ.dpow j b)]
  have hfilter : ∑ p ∈ Finset.range N ×ˢ Finset.range N with p.1 + p.2 < N, F p =
      ∑ p ∈ Finset.range N ×ˢ Finset.range N, F p := by
    refine Finset.sum_filter_of_ne fun p _ hp => ?_
    by_contra hlt
    exact hp (hpair p.1 p.2 (not_lt.mp hlt))
  rw [← hfilter, ← Finset.sum_fiberwise_of_maps_to (t := Finset.range N)
    (g := fun p : ℕ × ℕ => p.1 + p.2) (fun p hp => by simpa using (Finset.mem_filter.mp hp).2)]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [δ.dpow_add ha hb]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext ⟨i, j⟩
  simp only [Finset.mem_range] at hn
  simp only [Finset.HasAntidiagonal.mem_antidiagonal, Finset.mem_filter, Finset.mem_product,
    Finset.mem_range]
  omega

theorem IsNilDP.map_dpExp_eq {δ : DividedPowers J} {δ' : DividedPowers J'} (h : IsNilDP δ)
    {f : B →+* B'} (hf : IsDPMorphism δ δ' f) {a : B} (ha : a ∈ J) :
    f (dpExp δ a) = dpExp δ' (f a) := by
  obtain ⟨N, hN⟩ := h.exists_dpow_eq_zero
  rw [dpExp_eq_sum_range_of_vanish δ a N fun n hn ↦ hN n hn a,
    dpExp_eq_sum_range_of_vanish δ' (f a) N fun n hn ↦ by
      rw [← hf.map_dpow ha, hN n hn a, map_zero], map_sum]
  exact Finset.sum_congr rfl fun n _ ↦ hf.map_dpow ha

set_option autoImplicit false in
open CategoryTheory AlgebraicGeometry DividedPowers in
variable {B B' : Type} [CommRing B] [CommRing B'] {J : Ideal B} {J' : Ideal B'} in

theorem _root_.GlobalTheory.Cris.dpExp_add_and_natural (B B' : Type) [CommRing B] [CommRing B'] (J : Ideal B) (J' : Ideal B')
    (δ : DividedPowers J) (δ' : DividedPowers J') (h : _root_.GlobalTheory.Cris.IsNilDP δ) :
    (∀ a ∈ J, ∀ b ∈ J, _root_.GlobalTheory.Cris.dpExp δ (a + b) = _root_.GlobalTheory.Cris.dpExp δ a * _root_.GlobalTheory.Cris.dpExp δ b) ∧
      (∀ f : B →+* B', IsDPMorphism δ δ' f → ∀ a ∈ J,
        f (_root_.GlobalTheory.Cris.dpExp δ a) = _root_.GlobalTheory.Cris.dpExp δ' (f a)) := by
  refine ⟨fun a ha b hb => h.dpExp_add_eq_mul ha hb, fun f hf a ha => ?_⟩
  obtain ⟨N, hN⟩ := h
  have hvan : ∀ n, N ≤ n → δ.dpow n a = 0 := by
    intro n hn
    simpa using hN [(n, a)] (by simpa using ha) (by simpa using hn)
  have hvan' : ∀ n, N ≤ n → δ'.dpow n (f a) = 0 := by
    intro n hn
    rw [← hf.map_dpow ha, hvan n hn, map_zero]
  rw [_root_.GlobalTheory.Cris.dpExp_eq_sum_range_of_vanish δ a N hvan, _root_.GlobalTheory.Cris.dpExp_eq_sum_range_of_vanish δ' (f a) N hvan',
    map_sum]
  exact Finset.sum_congr rfl fun n _ => hf.map_dpow ha

end GlobalTheory.Cris
