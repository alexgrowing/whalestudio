import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
open Formalism.BasicNotions IsDedekindDomain NumberField

namespace GlobalTheory.LocGen

theorem exists_gen_mul_of_isIntegral {R S : Type*} [CommRing R] [CommRing S] [IsDedekindDomain S] [Algebra R S]
    [Algebra.IsIntegral R S] (hinj : Function.Injective (algebraMap R S)) (p : Ideal R) [p.IsPrime] (hp : p ≠ ⊥)
    (J : Ideal S) (hJ : J ≠ ⊥) :
    ∃ y ∈ J, y ≠ 0 ∧ ∃ c : R, c ∉ p ∧ ∀ j ∈ J, ∃ o : S, algebraMap R S c * j = y * o := by
  obtain ⟨r, hr, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hp
  have hr'0 : algebraMap R S r ≠ 0 := fun h => hr0 (hinj (by rw [h, map_zero]))
  have hJ0 : J ≠ 0 := hJ
  have hIv0 : J * Ideal.span {algebraMap R S r} ≠ 0 :=
    mul_ne_zero hJ0 (by rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hr'0)
  obtain ⟨y, hy⟩ := exists_sup_span_eq (Ideal.mul_le_left : J * Ideal.span {algebraMap R S r} ≤ J) hIv0
  have hyJ : y ∈ J := hy ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self y)
  obtain ⟨K, hK⟩ : J ∣ Ideal.span {y} := Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hyJ)
  have key : ¬ Ideal.comap (algebraMap R S) K ≤ p := by
    intro h
    obtain ⟨Q, hKQ, hQ, hQp⟩ := Ideal.exists_ideal_over_prime_of_isIntegral p K h
    have hrQ : algebraMap R S r ∈ Q := by
      rw [← Ideal.mem_comap, hQp]; exact hr
    have h1 : J * Ideal.span {algebraMap R S r} ≤ J * Q :=
      Ideal.mul_mono_right ((Ideal.span_singleton_le_iff_mem _).mpr hrQ)
    have h2 : Ideal.span {y} ≤ J * Q := hK ▸ Ideal.mul_mono_right hKQ
    have h3 : J ≤ J * Q := calc J = _ := hy.symm
      _ ≤ J * Q := sup_le h1 h2
    have h4 : J * Q = J * ⊤ := by
      rw [Ideal.mul_top]; exact le_antisymm Ideal.mul_le_left h3
    exact hQ.ne_top (mul_left_cancel₀ hJ0 h4)
  rw [SetLike.not_le_iff_exists] at key
  obtain ⟨c, hcK, hcp⟩ := key
  rw [Ideal.mem_comap] at hcK
  refine ⟨y, hyJ, ?_, c, hcp, ?_⟩
  · rintro rfl
    have hJK : J * K = 0 := by rw [← hK, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    have hK0 : K = 0 := (mul_eq_zero.mp hJK).resolve_left hJ0
    rw [hK0, Ideal.zero_eq_bot, Ideal.mem_bot] at hcK
    exact hcp (by rw [hinj (hcK.trans (map_zero _).symm)]; exact p.zero_mem)
  · intro j hj
    have hm : j * algebraMap R S c ∈ Ideal.span {y} := hK ▸ Ideal.mul_mem_mul hj hcK
    obtain ⟨o, ho⟩ := Ideal.mem_span_singleton'.mp hm
    exact ⟨o, by rw [mul_comm, ← ho, mul_comm]⟩

end GlobalTheory.LocGen

namespace GlobalTheory

open GlobalTheory.LocGen in

theorem fracIdeal_locGen : ∀ (D : D7) (I : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E), I ≠ 0 →
    ∀ v : HeightOneSpectrum (𝓞 D.host.F), ∃ a : D.host.E, a ≠ 0 ∧ ∃ c : 𝓞 D.host.F, c ∉ v.asIdeal ∧
      ((c : D.host.F) : D.host.E) * a ∈ I ∧
      ∀ b ∈ I, ∃ o : 𝓞 D.host.E, ((c : D.host.F) : D.host.E) * b = a * (o : D.host.E) := by
  intro D I hI v
  letI : Algebra (𝓞 D.host.F) (𝓞 D.host.E) := (RingOfIntegers.mapRingHom D.host.F.subtype).toAlgebra
  have hφ : ∀ c : 𝓞 D.host.F, ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) c : 𝓞 D.host.E) : D.host.E) =
      ((c : D.host.F) : D.host.E) := fun c => rfl
  haveI : Algebra.IsIntegral (𝓞 D.host.F) (𝓞 D.host.E) := Algebra.IsIntegral.tower_top (R := ℤ)
  have hinj : Function.Injective (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) := by
    intro x y h
    have h' := congrArg (fun z : 𝓞 D.host.E => (z : D.host.E)) h
    simp only [hφ] at h'
    exact RingOfIntegers.ext (Subtype.ext h')
  obtain ⟨d, J, hd, rfl⟩ := FractionalIdeal.exists_eq_spanSingleton_mul I
  have hJ : J ≠ ⊥ := by
    rintro rfl
    exact hI (by rw [FractionalIdeal.coeIdeal_bot, mul_zero])
  obtain ⟨y, hyJ, hy0, c, hcv, hc⟩ := exists_gen_mul_of_isIntegral hinj v.asIdeal v.ne_bot J hJ
  have hd' : ((d : 𝓞 D.host.E) : D.host.E) ≠ 0 := by
    rwa [Ne, RingOfIntegers.coe_eq_zero_iff]
  have hy' : ((y : 𝓞 D.host.E) : D.host.E) ≠ 0 := by
    rwa [Ne, RingOfIntegers.coe_eq_zero_iff]
  refine ⟨(y : D.host.E) * (d : D.host.E)⁻¹, mul_ne_zero hy' (inv_ne_zero hd'), c, hcv, ?_, ?_⟩
  · rw [FractionalIdeal.mem_singleton_mul]
    refine ⟨algebraMap (𝓞 D.host.E) D.host.E (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) c * y), ?_, ?_⟩
    · exact (FractionalIdeal.mem_coeIdeal _).mpr ⟨_, J.mul_mem_left _ hyJ, rfl⟩
    · rw [map_mul]
      show _ = _ * (((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) c : 𝓞 D.host.E) : D.host.E) * (y : D.host.E))
      rw [hφ]
      ring
  · intro b hb
    rw [FractionalIdeal.mem_singleton_mul] at hb
    obtain ⟨b', hb', rfl⟩ := hb
    obtain ⟨j, hj, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).mp hb'
    obtain ⟨o, ho⟩ := hc j hj
    refine ⟨o, ?_⟩
    have h2 : ((c : D.host.F) : D.host.E) * (j : D.host.E) = (y : D.host.E) * (o : D.host.E) := by
      have h3 := congrArg (algebraMap (𝓞 D.host.E) D.host.E) ho
      rw [map_mul, map_mul] at h3
      exact h3
    calc ((c : D.host.F) : D.host.E) * (((d : 𝓞 D.host.E) : D.host.E)⁻¹ * (j : D.host.E))
        = (d : D.host.E)⁻¹ * (((c : D.host.F) : D.host.E) * (j : D.host.E)) := by ring
      _ = (d : D.host.E)⁻¹ * ((y : D.host.E) * (o : D.host.E)) := by rw [h2]
      _ = _ := by ring

end GlobalTheory
