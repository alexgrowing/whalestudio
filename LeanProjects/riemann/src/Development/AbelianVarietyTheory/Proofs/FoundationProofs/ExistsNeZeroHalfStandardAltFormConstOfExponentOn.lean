import Mathlib
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DualRestrictSurjectiveOfIsTorsionFreeQuotient
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.BaseOver

open Function

namespace GlobalTheory

section General

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

theorem pow_succ_dvd_bilin_of_const_on_cosets (h2 : IsUnit (2 : R)) (r : R)
    (B : LinearMap.BilinForm R M) (hB : ∀ x y, B x y = B y x) (T : Set M)
    (hT : ∀ x, ∃ t ∈ T, ∃ a, x = t + r • a) (c : R) (hc : ∀ t ∈ T, B t t = c) (i : ℕ)
    (hi : ∀ x y, r ^ i ∣ B x y) (x y : M) : r ^ (i + 1) ∣ B x y := by
  have h1 : ∀ z, r ^ (i + 1) ∣ B z z - c := by
    intro z
    obtain ⟨t, ht, a, rfl⟩ := hT z
    have : B (t + r • a) (t + r • a) - c = (B t a + B a t + r * B a a) * r := by
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
        ← hc t ht]
      ring
    rw [this, pow_succ]
    exact mul_dvd_mul_right (((hi _ _).add (hi _ _)).add ((hi _ _).mul_left _)) r
  have h0 : r ^ (i + 1) ∣ c := by simpa using h1 0
  have h3 : ∀ z, r ^ (i + 1) ∣ B z z := fun z => by simpa using (h1 z).add h0
  have h4 : 2 * B x y = B (x + y) (x + y) - B x x - B y y := by
    simp only [map_add, LinearMap.add_apply, hB y x]
    ring
  exact h2.dvd_mul_left.1 (h4 ▸ ((h3 _).sub (h3 _)).sub (h3 _))

theorem bilin_eq_zero_of_const_on_cosets (h2 : IsUnit (2 : R)) {r : R} (hr : IsNilpotent r)
    (B : LinearMap.BilinForm R M) (hB : ∀ x y, B x y = B y x) (T : Set M)
    (hT : ∀ x, ∃ t ∈ T, ∃ a, x = t + r • a) (c : R) (hc : ∀ t ∈ T, B t t = c) : B = 0 := by
  have h : ∀ (i : ℕ) (x y : M), r ^ i ∣ B x y := by
    intro i
    induction i with
    | zero => simp
    | succ i ih => exact pow_succ_dvd_bilin_of_const_on_cosets h2 r B hB T hT c hc i ih
  obtain ⟨k, hk⟩ := hr
  ext x y
  simpa [hk] using h k x y

theorem end_eq_zero_of_quad_const_on_cosets (h2 : IsUnit (2 : R)) {r : R} (hr : IsNilpotent r)
    (ω : LinearMap.BilinForm R M) (hω : Injective ω) (S : M →ₗ[R] M)
    (hS : ∀ x y, ω (S x) y = ω (S y) x) (u : Rˣ) (q : M → R)
    (hq : ∀ x, 2 * q x = u * ω (S x) x) (T : Set M)
    (hT : ∀ x, ∃ t ∈ T, ∃ a, x = t + r • a) (c : R) (hc : ∀ t ∈ T, q t = c) : S = 0 := by
  have h : (ω ∘ₗ S : LinearMap.BilinForm R M) = 0 := by
    refine bilin_eq_zero_of_const_on_cosets h2 hr (ω ∘ₗ S) hS T hT (↑u⁻¹ * (2 * c)) fun t ht => ?_
    rw [← hc t ht, hq, Units.inv_mul_cancel_left]
    rfl
  ext x
  exact hω ((LinearMap.congr_fun h x).trans (by simp))

end General

section ZMod

variable {n k : ℕ}

theorem isUnit_two_zmod_pow (hn : Odd n) (k : ℕ) : IsUnit (2 : ZMod (n ^ k)) := by
  have h : Nat.Coprime 2 (n ^ k) := (Nat.coprime_two_left.2 hn).pow_right k
  simpa using (ZMod.isUnit_iff_coprime 2 (n ^ k)).2 h

theorem isNilpotent_natCast_zmod_pow (n k : ℕ) : IsNilpotent (n : ZMod (n ^ k)) :=
  ⟨k, by rw [← Nat.cast_pow, ZMod.natCast_self]⟩

theorem exists_eq_nsmul_of_nsmul_eq_zero_zmod (hn : n ≠ 0) (hk : 2 ≤ k) (x : ZMod (n ^ k))
    (hx : n • x = 0) : ∃ a, x = n • a := by
  obtain ⟨z, rfl⟩ := ZMod.intCast_surjective x
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hk
  have h1 : (((n : ℤ) * z : ℤ) : ZMod (n ^ (j + 2))) = 0 := by
    rw [← hx]; simp
  obtain ⟨w, hw⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h1
  have h2 : z = n * ((n : ℤ) ^ j * w) := by
    apply mul_left_cancel₀ (Int.natCast_ne_zero.2 hn)
    rw [hw]; push_cast; ring
  exact ⟨(((n : ℤ) ^ j * w : ℤ) : ZMod (n ^ (j + 2))), by rw [h2]; simp⟩

theorem meets_cosets_nsmul_of_meets_cosets_torsion {ι : Type*} (hn : n ≠ 0) (hk : 2 ≤ k)
    (T : Set (ι → ZMod (n ^ k))) (hT : ∀ x, ∃ t ∈ T, n • (x - t) = 0) (x : ι → ZMod (n ^ k)) :
    ∃ t ∈ T, ∃ a, x = t + n • a := by
  obtain ⟨t, ht, h⟩ := hT x
  choose a ha using fun i =>
    exists_eq_nsmul_of_nsmul_eq_zero_zmod hn hk ((x - t) i) (congrFun h i)
  exact ⟨t, ht, a, by rw [← sub_eq_iff_eq_add']; exact funext ha⟩

theorem end_eq_zero_of_quad_const_on_cosets_zmod {ι : Type*} (hn : Odd n)
    (ω : LinearMap.BilinForm (ZMod (n ^ k)) (ι → ZMod (n ^ k))) (hω : Injective ω)
    (S : (ι → ZMod (n ^ k)) →ₗ[ZMod (n ^ k)] (ι → ZMod (n ^ k)))
    (hS : ∀ x y, ω (S x) y = ω (S y) x) (u : (ZMod (n ^ k))ˣ) (q : (ι → ZMod (n ^ k)) → ZMod (n ^ k))
    (hq : ∀ x, 2 * q x = u * ω (S x) x) (T : Set (ι → ZMod (n ^ k)))
    (hT : (∀ x, ∃ t ∈ T, ∃ a, x = t + n • a) ∨ (2 ≤ k ∧ ∀ x, ∃ t ∈ T, n • (x - t) = 0))
    (c : ZMod (n ^ k)) (hc : ∀ t ∈ T, q t = c) : S = 0 := by
  have hT' : ∀ x, ∃ t ∈ T, ∃ a, x = t + n • a :=
    hT.elim id fun h => meets_cosets_nsmul_of_meets_cosets_torsion hn.pos.ne' h.1 T h.2
  refine end_eq_zero_of_quad_const_on_cosets (isUnit_two_zmod_pow hn k)
    (isNilpotent_natCast_zmod_pow n k) ω hω S hS u q hq T (fun x => ?_) c hc
  simpa only [Nat.cast_smul_eq_nsmul] using hT' x

theorem end_eq_zero_of_twist_proportional {ι K : Type*} [CommRing K] [IsDomain K] (hn : Odd n)
    (ω : LinearMap.BilinForm (ZMod (n ^ k)) (ι → ZMod (n ^ k))) (hω : Injective ω)
    (S : (ι → ZMod (n ^ k)) →ₗ[ZMod (n ^ k)] (ι → ZMod (n ^ k)))
    (hS : ∀ x y, ω (S x) y = ω (S y) x) (u : (ZMod (n ^ k))ˣ) (q : (ι → ZMod (n ^ k)) → ZMod (n ^ k))
    (hq : ∀ x, 2 * q x = u * ω (S x) x) {ζ : K} (hζ : IsPrimitiveRoot ζ (n ^ k))
    (θ θ' : (ι → ZMod (n ^ k)) → K) (hθ : ∀ x, θ' x = ζ ^ (q x).val * θ x)
    (c : K) (hc : ∀ x, θ' x = c * θ x)
    (hT : (∀ x, ∃ t, θ t ≠ 0 ∧ ∃ a, x = t + n • a) ∨
      (2 ≤ k ∧ ∀ x, ∃ t, θ t ≠ 0 ∧ n • (x - t) = 0)) : S = 0 := by
  haveI : NeZero (n ^ k) := ⟨pow_ne_zero _ hn.pos.ne'⟩
  have h1 : ∀ t, θ t ≠ 0 → ζ ^ (q t).val = c := fun t ht =>
    mul_right_cancel₀ ht ((hθ t).symm.trans (hc t))
  obtain ⟨t₀, ht₀⟩ : ∃ t, θ t ≠ 0 :=
    hT.elim (fun h => (h 0).imp fun _ h => h.1) fun h => (h.2 0).imp fun _ h => h.1
  refine end_eq_zero_of_quad_const_on_cosets_zmod hn ω hω S hS u q hq {t | θ t ≠ 0} hT (q t₀)
    fun t ht => ?_
  exact ZMod.val_injective _
    (hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) ((h1 t ht).trans (h1 t₀ ht₀).symm))

end ZMod

section LevelForm

open ReciprocityTheory.ChartRestriction.G.Out

theorem injective_toBilin'_stdSymp {R : Type*} [CommRing R] (g : ℕ) :
    Injective (Matrix.toBilin' (Matrix.of fun i j => ((stdSymp g i j : ℤ) : R))) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  funext i
  have key : ∀ j, ∑ l, x l * ((stdSymp g l j : ℤ) : R) = 0 := fun j => by
    have := LinearMap.congr_fun hx (Pi.single j 1)
    simpa [Matrix.toBilin'_apply, Pi.single_apply] using this
  by_cases hi : (i : ℕ) < g
  · have h := key ⟨i + g, by omega⟩
    rw [Finset.sum_eq_single i] at h
    · simpa [stdSymp, hi] using h
    · intro l _ hl
      have h1 : (l : ℕ) ≠ i := fun h => hl (Fin.ext h)
      have : stdSymp g l ⟨i + g, by omega⟩ = 0 := by
        unfold stdSymp
        rw [if_neg (by simp only; omega), if_neg (by simp only; omega)]
      simp [this]
    · simp
  · have hi2 := i.2
    have h := key ⟨i - g, by omega⟩
    rw [Finset.sum_eq_single i] at h
    · have : stdSymp g i ⟨i - g, by omega⟩ = -1 := by
        unfold stdSymp
        rw [if_neg (by simp only; omega), if_pos (by simp only; omega)]
      simpa [this] using h
    · intro l _ hl
      have h1 : (l : ℕ) ≠ i := fun h => hl (Fin.ext h)
      have : stdSymp g l ⟨i - g, by omega⟩ = 0 := by
        unfold stdSymp
        rw [if_neg (by simp only; omega), if_neg (by simp only; omega)]
      simp [this]
    · simp

end LevelForm

end GlobalTheory
