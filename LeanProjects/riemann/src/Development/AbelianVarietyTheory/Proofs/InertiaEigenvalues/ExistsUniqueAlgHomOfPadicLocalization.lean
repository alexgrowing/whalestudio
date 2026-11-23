import Mathlib
open PowerSeries

namespace GlobalTheory

theorem existsUnique_algHom_of_padic_localization {O A E B : Type} [CommRing O] [CommRing A]
    [CommRing E] [CommRing B] [Algebra O A] [Algebra O E] [Algebra O B] (p : ℕ) (x : A)
    (ι : A →ₐ[O] E) (f : A →ₐ[O] B) (_hι : IsUnit (ι x)) (hf : IsUnit (f x))
    (hB : IsAdicComplete (Ideal.span {(p : B)}) B)
    (hd : ∀ (y : E) (k : ℕ), ∃ (a : A) (m : ℕ), (p : E) ^ k ∣ y * ι (x ^ m) - ι a)
    (hi : ∀ (a : A) (k : ℕ), (p : E) ^ k ∣ ι a → (p : A) ^ k ∣ a) :
    ∃! g : E →ₐ[O] B, ∀ a, g (ι a) = f a := by
  obtain ⟨v, hv⟩ := hf.exists_right_inv
  have hvm : ∀ m : ℕ, f x ^ m * v ^ m = 1 := fun m => by rw [← mul_pow, hv, one_pow]
  have smod : ∀ (k : ℕ) (z w : B),
      z ≡ w [SMOD ((Ideal.span {(p : B)}) ^ k • ⊤ : Submodule B B)] ↔ (p : B) ^ k ∣ z - w := by
    intro k z w
    rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton]
  have ext : ∀ z w : B, (∀ k, (p : B) ^ k ∣ z - w) → z = w := by
    intro z w h
    have := IsHausdorff.haus hB.toIsHausdorff (z - w) (fun k => by
      rw [smod, sub_zero]; exact h k)
    exact sub_eq_zero.mp this
  have key : ∀ (y : E) (k : ℕ) (a : A) (m : ℕ) (a' : A) (m' : ℕ),
      (p : E) ^ k ∣ y * ι (x ^ m) - ι a → (p : E) ^ k ∣ y * ι (x ^ m') - ι a' →
      (p : B) ^ k ∣ f a * v ^ m - f a' * v ^ m' := by
    intro y k a m a' m' h h'
    have h1 : (p : E) ^ k ∣ ι (a * x ^ m' - a' * x ^ m) := by
      have : ι (a * x ^ m' - a' * x ^ m) =
          ι (x ^ m) * (y * ι (x ^ m') - ι a') - ι (x ^ m') * (y * ι (x ^ m) - ι a) := by
        simp only [map_sub, map_mul]; ring
      rw [this]
      exact dvd_sub (h'.mul_left _) (h.mul_left _)
    have h2 := map_dvd f (hi _ _ h1)
    simp only [map_pow, map_natCast, map_sub, map_mul] at h2
    have : f a * v ^ m - f a' * v ^ m' =
        (f a * f x ^ m' - f a' * f x ^ m) * (v ^ m * v ^ m') := by
      linear_combination (-(f a * v ^ m)) * hvm m' + (f a' * v ^ m') * hvm m
    rw [this]
    exact h2.mul_right _
  have ex : ∀ y : E, ∃ z : B, ∀ (k : ℕ) (a : A) (m : ℕ),
      (p : E) ^ k ∣ y * ι (x ^ m) - ι a → (p : B) ^ k ∣ z - f a * v ^ m := by
    intro y
    choose a m ham using hd y
    obtain ⟨z, hz⟩ := IsPrecomplete.prec hB.toIsPrecomplete
      (f := fun k => f (a k) * v ^ (m k)) (fun {j k} hjk => by
        rw [smod]
        exact key y j _ _ _ _ (ham j) ((pow_dvd_pow _ hjk).trans (ham k)))
    refine ⟨z, fun k a' m' h => ?_⟩
    have h1 := (smod _ _ _).mp (hz k)
    have h2 := key y k _ _ _ _ (ham k) h
    have := dvd_sub h2 h1
    convert this using 1
    ring
  choose g hg using ex
  have hgι : ∀ a, g (ι a) = f a := by
    intro a
    refine ext _ _ fun k => ?_
    simpa using hg (ι a) k a 0 (by simp)
  have hadd : ∀ y y', g (y + y') = g y + g y' := by
    intro y y'
    refine ext _ _ fun k => ?_
    obtain ⟨a, m, h⟩ := hd y k
    obtain ⟨a', m', h'⟩ := hd y' k
    have h1 := hg (y + y') k (a * x ^ m' + a' * x ^ m) (m + m') (by
      have := dvd_add (h.mul_left (ι (x ^ m'))) (h'.mul_left (ι (x ^ m)))
      convert this using 1
      simp only [map_add, map_mul, map_pow]; ring)
    have := dvd_sub (dvd_sub h1 (hg y k a m h)) (hg y' k a' m' h')
    convert this using 1
    simp only [map_add, map_mul, map_pow, pow_add]
    linear_combination (f a * v ^ m) * hvm m' + (f a' * v ^ m') * hvm m
  have hmul : ∀ y y', g (y * y') = g y * g y' := by
    intro y y'
    refine ext _ _ fun k => ?_
    obtain ⟨a, m, h⟩ := hd y k
    obtain ⟨a', m', h'⟩ := hd y' k
    have h1 := hg (y * y') k (a * a') (m + m') (by
      have := dvd_add (h.mul_left (y' * ι (x ^ m'))) (h'.mul_left (ι a))
      convert this using 1
      simp only [map_add, map_mul, map_pow]; ring)
    have := dvd_sub (dvd_sub h1 ((hg y k a m h).mul_left (g y')))
      ((hg y' k a' m' h').mul_left (f a * v ^ m))
    convert this using 1
    simp only [map_add, map_mul, map_pow, pow_add]
    ring
  refine ⟨
    { toFun := g
      map_one' := by simpa using hgι 1
      map_mul' := hmul
      map_zero' := by simpa using hgι 0
      map_add' := hadd
      commutes' := fun r => by simpa using hgι (algebraMap O A r) }, hgι, ?_⟩
  intro g' hg'
  ext y
  refine ext _ _ fun k => ?_
  obtain ⟨a, m, h⟩ := hd y k
  have h1 := map_dvd g' h
  rw [map_sub, map_mul, hg', hg', map_pow, map_natCast, map_pow] at h1
  have := dvd_sub (h1.mul_right (v ^ m)) (hg y k a m h)
  convert this using 1
  show g' y - g y = _
  linear_combination (-(g' y)) * hvm m

end GlobalTheory
