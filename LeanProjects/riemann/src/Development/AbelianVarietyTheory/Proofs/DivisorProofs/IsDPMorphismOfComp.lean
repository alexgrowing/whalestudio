import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction

open CategoryTheory AlgebraicGeometry DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.DPLoc

variable {B S : Type} [CommRing B] [CommRing S] [Algebra B S] (M : Submonoid B)
  [IsLocalization M S] {J : Ideal B} (δ : DividedPowers J)

include M in

theorem wellDef {u v : S} {j j' : B} (hj : j ∈ J) (hj' : j' ∈ J)
    (h : u * algebraMap B S j = v * algebraMap B S j') (n : ℕ) :
    u ^ n * algebraMap B S (δ.dpow n j) = v ^ n * algebraMap B S (δ.dpow n j') := by
  obtain ⟨⟨a, s⟩, ha⟩ := IsLocalization.surj M u
  obtain ⟨⟨c, t⟩, hc⟩ := IsLocalization.surj M v
  simp only at ha hc
  have h1 : algebraMap B S (a * t * j) = algebraMap B S (c * s * j') := by
    simp only [map_mul, ← ha, ← hc]
    linear_combination (algebraMap B S s * algebraMap B S t) * h
  obtain ⟨m, hm⟩ := (IsLocalization.eq_iff_exists M S).1 h1
  have h2 : ((m : B) * (a * t)) ^ n * δ.dpow n j = ((m : B) * (c * s)) ^ n * δ.dpow n j' := by
    rw [← δ.dpow_mul hj, ← δ.dpow_mul hj']
    congr 1
    linear_combination hm
  have h3 := congrArg (algebraMap B S) h2
  simp only [map_mul, map_pow, ← ha, ← hc, mul_pow] at h3
  have hu : IsUnit ((algebraMap B S m) ^ n * (algebraMap B S s) ^ n * (algebraMap B S t) ^ n) :=
    (((IsLocalization.map_units S m).pow n).mul ((IsLocalization.map_units S s).pow n)).mul
      ((IsLocalization.map_units S t).pow n)
  apply hu.mul_left_cancel
  linear_combination h3

include M in

theorem rep₂ {x y : S} (hx : x ∈ J.map (algebraMap B S)) (hy : y ∈ J.map (algebraMap B S)) :
    ∃ (u : S) (j j' : B), j ∈ J ∧ j' ∈ J ∧ x = u * algebraMap B S j ∧
      y = u * algebraMap B S j' := by
  obtain ⟨⟨j, s⟩, hj⟩ := (IsLocalization.mem_map_algebraMap_iff M S).1 hx
  obtain ⟨⟨j', t⟩, hj'⟩ := (IsLocalization.mem_map_algebraMap_iff M S).1 hy
  simp only at hj hj'
  obtain ⟨u, hu⟩ := (IsLocalization.map_units S (s * t)).exists_left_inv
  simp only [Submonoid.coe_mul, map_mul] at hu
  refine ⟨u, t * j, s * j', J.mul_mem_left _ j.2, J.mul_mem_left _ j'.2, ?_, ?_⟩
  · rw [map_mul, ← hj]; linear_combination (-x) * hu
  · rw [map_mul, ← hj']; linear_combination (-y) * hu

include M in

theorem rep {x : S} (hx : x ∈ J.map (algebraMap B S)) :
    ∃ (u : S) (j : B), j ∈ J ∧ x = u * algebraMap B S j := by
  obtain ⟨u, j, _, hj, _, e, _⟩ := rep₂ M hx hx
  exact ⟨u, j, hj, e⟩

open Classical in

def ext (n : ℕ) (x : S) : S :=
  if h : ∃ p : S × B, p.2 ∈ J ∧ x = p.1 * algebraMap B S p.2 then
    h.choose.1 ^ n * algebraMap B S (δ.dpow n h.choose.2) else 0

include M in

theorem ext_eq (n : ℕ) (u : S) {j : B} (hj : j ∈ J) :
    ext δ n (u * algebraMap B S j) = u ^ n * algebraMap B S (δ.dpow n j) := by
  have h : ∃ p : S × B, p.2 ∈ J ∧ u * algebraMap B S j = p.1 * algebraMap B S p.2 :=
    ⟨(u, j), hj, rfl⟩
  rw [ext, dif_pos h]
  exact (wellDef M δ hj h.choose_spec.1 h.choose_spec.2 n).symm

def dp : DividedPowers (J.map (algebraMap B S)) where
  dpow := ext δ
  dpow_null {n x} hx := by
    rw [ext, dif_neg]
    rintro ⟨p, hp, rfl⟩
    exact hx (Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hp))
  dpow_zero hx := by
    obtain ⟨u, j, hj, rfl⟩ := rep M hx
    simp [ext_eq M δ _ _ hj, δ.dpow_zero hj]
  dpow_one hx := by
    obtain ⟨u, j, hj, rfl⟩ := rep M hx
    simp [ext_eq M δ _ _ hj, δ.dpow_one hj]
  dpow_mem hn hx := by
    obtain ⟨u, j, hj, rfl⟩ := rep M hx
    rw [ext_eq M δ _ _ hj]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (δ.dpow_mem hn hj))
  dpow_add hx hy := by
    obtain ⟨u, j, j', hj, hj', rfl, rfl⟩ := rep₂ M hx hy
    rw [← mul_add, ← map_add, ext_eq M δ _ _ (J.add_mem hj hj'), δ.dpow_add hj hj', map_sum,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    rw [ext_eq M δ _ _ hj, ext_eq M δ _ _ hj', ← (Finset.HasAntidiagonal.mem_antidiagonal.1 hk : k.1 + k.2 = _), map_mul]
    ring
  dpow_mul hx := by
    obtain ⟨u, j, hj, rfl⟩ := rep M hx
    rw [← mul_assoc, ext_eq M δ _ _ hj, ext_eq M δ _ _ hj]
    ring
  mul_dpow {m n x} hx := by
    obtain ⟨u, j, hj, rfl⟩ := rep M hx
    have := congrArg (algebraMap B S) (δ.mul_dpow (m := m) (n := n) hj)
    rw [map_mul, map_mul, map_natCast] at this
    simp only [ext_eq M δ _ _ hj]
    linear_combination u ^ (m + n) * this
  dpow_comp {m n x} hn hx := by
    obtain ⟨u, j, hj, rfl⟩ := rep M hx
    rw [ext_eq M δ _ _ hj, ext_eq M δ _ _ hj, ext_eq M δ _ _ (δ.dpow_mem hn hj),
      δ.dpow_comp hn hj, map_mul, map_natCast]
    ring

theorem dp_dpow (n : ℕ) (u : S) {j : B} (hj : j ∈ J) :
    (dp M δ).dpow n (u * algebraMap B S j) = u ^ n * algebraMap B S (δ.dpow n j) :=
  ext_eq M δ n u hj

theorem isDPMorphism : IsDPMorphism δ (dp (S := S) M δ) (algebraMap B S) :=
  ⟨le_rfl, fun {n} a ha ↦ by simpa using dp_dpow M δ n (1 : S) ha⟩

theorem isNilDP (h : IsNilDP δ) : IsNilDP (dp (S := S) M δ) := by
  obtain ⟨N, h⟩ := h
  have key : ∀ l : List (ℕ × S), (∀ p ∈ l, p.2 ∈ J.map (algebraMap B S)) →
      ∃ (c : S) (l' : List (ℕ × B)), (∀ p ∈ l', p.2 ∈ J) ∧
        (l'.map Prod.fst).sum = (l.map Prod.fst).sum ∧
        (l.map fun p ↦ (dp M δ).dpow p.1 p.2).prod =
          c * algebraMap B S (l'.map fun p ↦ δ.dpow p.1 p.2).prod := by
    intro l
    induction l with
    | nil => exact fun _ ↦ ⟨1, [], by simp⟩
    | cons p l ih =>
      intro hl
      obtain ⟨c, l', h1, h2, h3⟩ := ih fun q hq ↦ hl q (by simp [hq])
      obtain ⟨u, j, hj, e⟩ := rep M (hl p (by simp))
      refine ⟨u ^ p.1 * c, (p.1, j) :: l', ?_, by simp [h2], ?_⟩
      · intro q hq
        rcases List.mem_cons.1 hq with rfl | hq
        exacts [hj, h1 q hq]
      · simp only [List.map_cons, List.prod_cons, map_mul]
        rw [h3, e, dp_dpow M δ _ _ hj]
        ring
  refine ⟨N, fun l hl hN ↦ ?_⟩
  obtain ⟨c, l', h1, h2, h3⟩ := key l hl
  rw [h3, h l' h1 (h2 ▸ hN), map_zero, mul_zero]

theorem isDPMorphism_of_comp {C : Type} [CommRing C] {J'' : Ideal C} (δ'' : DividedPowers J'')
    (g : S →+* C) (h : IsDPMorphism δ δ'' (g.comp (algebraMap B S))) :
    IsDPMorphism (dp M δ) δ'' g := by
  refine ⟨by rw [Ideal.map_map]; exact h.1, fun {n} x hx ↦ ?_⟩
  obtain ⟨u, j, hj, rfl⟩ := rep M hx
  have hm : g (algebraMap B S j) ∈ J'' := h.1 (Ideal.mem_map_of_mem _ hj)
  have e : δ''.dpow n (g (algebraMap B S j)) = g (algebraMap B S (δ.dpow n j)) := h.2 j hj
  rw [dp_dpow M δ _ _ hj, map_mul, δ''.dpow_mul hm, e, map_mul, map_pow]

theorem exists_away : ∀ (B : Type) [CommRing B] (J : Ideal B) (δ : DividedPowers J) (b : B), IsNilDP δ → ∃ δ' : DividedPowers (J.map (algebraMap B (Localization.Away b))), IsNilDP δ' ∧ IsDPMorphism δ δ' (algebraMap B (Localization.Away b)) ∧ ∀ (C : Type) [CommRing C] (J'' : Ideal C) (δ'' : DividedPowers J'') (g : Localization.Away b →+* C), IsDPMorphism δ δ'' (g.comp (algebraMap B _)) → IsDPMorphism δ' δ'' g :=
  fun _ _ _ δ b h ↦ ⟨dp (Submonoid.powers b) δ, isNilDP _ δ h, isDPMorphism _ δ,
    fun _ _ _ δ'' g hg ↦ isDPMorphism_of_comp _ δ δ'' g hg⟩

end GlobalTheory.DPLoc
