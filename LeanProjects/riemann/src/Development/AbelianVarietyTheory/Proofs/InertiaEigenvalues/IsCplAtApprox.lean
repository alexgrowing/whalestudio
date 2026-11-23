import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ProjectionSurjective
open IsLocalRing GlobalTheory.Pat

namespace GlobalTheory.Pat

theorem IsCplAt.approx_step {R S : Type} [CommRing R] [CommRing S] [IsLocalRing S] {q : Ideal R}
    [hq : q.IsPrime] {φ : R →+* S} (h : IsCplAt q φ) (k : ℕ) (t : S) (ht : t ∈ maximalIdeal S ^ k) :
    ∀ c : S, ∃ a b : R, b ∉ q ∧ φ b * (c * t) - φ a ∈ maximalIdeal S ^ (k + 1) := by
  have e : maximalIdeal S ^ k = (q ^ k).map φ := by rw [h.max_eq, Ideal.map_pow]
  rw [e, Ideal.map] at ht
  induction ht using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨x, hx, rfl⟩ := hx
    intro c
    obtain ⟨a, b, hb, hab⟩ := h.res c
    refine ⟨a * x, b, hb, ?_⟩
    have : φ b * (c * φ x) - φ (a * x) = φ x * (φ b * c - φ a) := by rw [map_mul]; ring
    rw [this, pow_succ]
    exact Ideal.mul_mem_mul (e ▸ Ideal.mem_map_of_mem φ hx) hab
  | zero =>
    intro c
    exact ⟨0, 1, (Ideal.ne_top_iff_one q).1 hq.ne_top, by simp⟩
  | add x y _ _ hx hy =>
    intro c
    obtain ⟨a, b, hb, hab⟩ := hx c
    obtain ⟨a', b', hb', hab'⟩ := hy c
    refine ⟨b' * a + b * a', b * b', fun hh => (hq.mem_or_mem hh).elim hb hb', ?_⟩
    have : φ (b * b') * (c * (x + y)) - φ (b' * a + b * a')
        = φ b' * (φ b * (c * x) - φ a) + φ b * (φ b' * (c * y) - φ a') := by
      simp only [map_mul, map_add]; ring
    rw [this]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hab) (Ideal.mul_mem_left _ _ hab')
  | smul r x _ hx =>
    intro c
    obtain ⟨a, b, hb, hab⟩ := hx (c * r)
    exact ⟨a, b, hb, by simpa [mul_assoc] using hab⟩

theorem IsCplAt.approx_surj {R S : Type} [CommRing R] [CommRing S] [IsLocalRing S] {q : Ideal R}
    [hq : q.IsPrime] {φ : R →+* S} (h : IsCplAt q φ) (k : ℕ) (s : S) :
    ∃ a b : R, b ∉ q ∧ φ b * s - φ a ∈ maximalIdeal S ^ k := by
  induction k with
  | zero => exact ⟨0, 1, (Ideal.ne_top_iff_one q).1 hq.ne_top, by simp⟩
  | succ k ih =>
    obtain ⟨a, b, hb, hab⟩ := ih
    obtain ⟨a', b', hb', hab'⟩ := h.approx_step k _ hab 1
    refine ⟨b' * a + a', b * b', fun hh => (hq.mem_or_mem hh).elim hb hb', ?_⟩
    have : φ (b * b') * s - φ (b' * a + a') = φ b' * (1 * (φ b * s - φ a)) - φ a' := by
      simp only [map_mul, map_add]; ring
    rw [this]
    exact hab'

theorem IsCplAt.approx_inj {R S : Type} [CommRing R] [CommRing S] [IsLocalRing S] {q : Ideal R}
    [hq : q.IsPrime] {φ : R →+* S} (h : IsCplAt q φ) (k : ℕ) (a : R)
    (ha : φ a ∈ maximalIdeal S ^ k) : ∃ b ∉ q, b * a ∈ q ^ k := by
  let L := Localization.AtPrime q
  have hu : ∀ y : q.primeCompl, IsUnit (φ y) := by
    intro y
    by_contra hy
    have : (y : R) ∈ (maximalIdeal S).comap φ := (mem_maximalIdeal _).2 hy
    rw [h.comap_eq] at this
    exact y.2 this
  letI : Algebra R S := φ.toAlgebra
  let ψ : L →+* S := IsLocalization.lift (M := q.primeCompl) hu
  letI : Algebra L S := ψ.toAlgebra
  have hψ : ∀ r, ψ (algebraMap R L r) = φ r := fun r => IsLocalization.lift_eq hu r
  haveI : IsScalarTower R L S := IsScalarTower.of_algebraMap_eq fun r => (hψ r).symm
  have hfl : Module.Flat R S := h.flat
  haveI : Module.Flat L S := (Module.flat_iff_of_isLocalization L q.primeCompl S).2 hfl
  have hcomp : (algebraMap L S).comp (algebraMap R L) = φ := RingHom.ext hψ
  haveI : IsLocalHom (algebraMap L S) := by
    apply ((local_hom_TFAE (algebraMap L S)).out 0 2).2
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, hcomp, h.max_eq]
  haveI : Module.FaithfullyFlat L S := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have key := Ideal.comap_map_eq_self_of_faithfullyFlat (B := S) ((q ^ k).map (algebraMap R L))
  rw [Ideal.map_map, hcomp, Ideal.map_pow φ, ← h.max_eq] at key
  have ha' : algebraMap R L a ∈ (q ^ k).map (algebraMap R L) := by
    rw [← key, Ideal.mem_comap]
    exact (hψ a).symm ▸ ha
  obtain ⟨m, hm, hma⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff q.primeCompl L _ a).1 ha'
  exact ⟨m, hm, hma⟩

theorem isCplAt_approx : ∀ (R S : Type) [CommRing R] [CommRing S] [IsLocalRing S] (q : Ideal R)
    [q.IsPrime] (φ : R →+* S), IsCplAt q φ → ∀ k : ℕ,
    (∀ s : S, ∃ a b : R, b ∉ q ∧ φ b * s - φ a ∈ maximalIdeal S ^ k) ∧
      ∀ a : R, φ a ∈ maximalIdeal S ^ k → ∃ b ∉ q, b * a ∈ q ^ k :=
  fun _ _ _ _ _ _ _ _ h k => ⟨h.approx_surj k, h.approx_inj k⟩

end GlobalTheory.Pat
