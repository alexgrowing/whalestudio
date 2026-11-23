import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HESmulRight

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators nonZeroDivisors

namespace GlobalTheory.IdealGenerator

theorem coe_ideal_mul {R K : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    (P : Ideal R) (I : FractionalIdeal R⁰ K) :
    (((P : FractionalIdeal R⁰ K) * I : FractionalIdeal R⁰ K) : Submodule R K) = P • (I : Submodule R K) := by
  rw [FractionalIdeal.coe_mul, FractionalIdeal.coe_coeIdeal]
  apply le_antisymm
  · rw [Submodule.mul_le]
    intro m hm n hn
    obtain ⟨p, hp, rfl⟩ := (IsLocalization.mem_coeSubmodule _ _).1 hm
    rw [← Algebra.smul_def]
    exact Submodule.smul_mem_smul hp hn
  · rw [Submodule.smul_le]
    intro p hp n hn
    rw [Algebra.smul_def]
    exact Submodule.mul_mem_mul ((IsLocalization.mem_coeSubmodule _ _).2 ⟨p, hp, rfl⟩) hn

theorem exists_gen {R K : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    (P : Ideal R) (hP : P.IsMaximal) (I : FractionalIdeal R⁰ K) (hI : I ≠ 0) :
    ∃ t₀ ∈ (I : Submodule R K), ∀ t ∈ (I : Submodule R K), ∃ a : R, t - a • t₀ ∈ P • (I : Submodule R K) := by
  have hle : (P : FractionalIdeal R⁰ K) * I ≤ I := by
    calc (P : FractionalIdeal R⁰ K) * I ≤ 1 * I := by
          gcongr; exact FractionalIdeal.coeIdeal_le_one
      _ = I := one_mul I
  have hne : (P : FractionalIdeal R⁰ K) * I ≠ I := by
    intro h
    have h1 : (P : FractionalIdeal R⁰ K) = 1 := mul_right_cancel₀ hI (by rw [h, one_mul])
    exact hP.ne_top (by simpa using (FractionalIdeal.coeIdeal_eq_one.1 h1))
  obtain ⟨t₀, ht₀, ht₀'⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hle hne)
  refine ⟨t₀, ht₀, ?_⟩
  set S : FractionalIdeal R⁰ K := FractionalIdeal.spanSingleton R⁰ t₀ + (P : FractionalIdeal R⁰ K) * I with hS
  have hSle : S ≤ I := by
    rw [hS, ← FractionalIdeal.sup_eq_add]
    exact sup_le (FractionalIdeal.spanSingleton_le_iff_mem.2 ht₀) hle
  have hPS : (P : FractionalIdeal R⁰ K) * I ≤ S := by
    rw [hS, ← FractionalIdeal.sup_eq_add]; exact le_sup_right
  have hJ : S * I⁻¹ ≤ 1 := by
    calc S * I⁻¹ ≤ I * I⁻¹ := by gcongr
      _ = 1 := mul_inv_cancel₀ hI
  obtain ⟨J, hJ'⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.1 hJ
  have hSJ : S = (J : FractionalIdeal R⁰ K) * I := by
    rw [hJ', mul_assoc, inv_mul_cancel₀ hI, mul_one]
  have hPJ : P ≤ J := by
    rw [← FractionalIdeal.coeIdeal_le_coeIdeal K, hJ']
    calc (P : FractionalIdeal R⁰ K) = (P * I) * I⁻¹ := by rw [mul_assoc, mul_inv_cancel₀ hI, mul_one]
      _ ≤ S * I⁻¹ := by gcongr
  have hJt : J = ⊤ := by
    by_contra h
    have hPJ' := hP.eq_of_le h hPJ
    apply ht₀'
    rw [hPJ', ← hSJ]
    have : FractionalIdeal.spanSingleton R⁰ t₀ ≤ S := by
      rw [hS, ← FractionalIdeal.sup_eq_add]; exact le_sup_left
    exact this (FractionalIdeal.mem_spanSingleton_self _ _)
  have hSI : S = I := by rw [hSJ, hJt, FractionalIdeal.coeIdeal_top, one_mul]
  intro t ht
  have ht' : t ∈ (S : Submodule R K) := by rw [hSI]; exact ht
  rw [hS, FractionalIdeal.coe_add, coe_ideal_mul, FractionalIdeal.coe_spanSingleton, Submodule.add_eq_sup,
    Submodule.mem_sup] at ht'
  obtain ⟨y, hy, z, hz, rfl⟩ := ht'
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hy
  exact ⟨a, by simpa using hz⟩

theorem mem_range_of_mul_mem {R K : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] (I : FractionalIdeal R⁰ K) (hI : I ≠ 0) (x : K)
    (h : ∀ t ∈ (I : Submodule R K), x * t ∈ (I : Submodule R K)) : x ∈ (algebraMap R K).range := by
  have h1 : FractionalIdeal.spanSingleton R⁰ x * I ≤ I :=
    FractionalIdeal.spanSingleton_mul_le_iff.2 h
  have h2 : FractionalIdeal.spanSingleton R⁰ x ≤ 1 := by
    calc FractionalIdeal.spanSingleton R⁰ x = (FractionalIdeal.spanSingleton R⁰ x * I) * I⁻¹ := by
          rw [mul_assoc, mul_inv_cancel₀ hI, mul_one]
      _ ≤ I * I⁻¹ := by gcongr
      _ = 1 := mul_inv_cancel₀ hI
  exact (FractionalIdeal.mem_one_iff _).1 (FractionalIdeal.spanSingleton_le_iff_mem.1 h2)

theorem exists_gen_and {R K : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    (P : Ideal R) (hP : P.IsMaximal) (I : FractionalIdeal R⁰ K) (hI : I ≠ 0) :
    ∃ t₀ ∈ (I : Submodule R K), (∀ t ∈ (I : Submodule R K), ∃ a : R, t - a • t₀ ∈ P • (I : Submodule R K)) ∧
      ∀ θ : K, θ ∉ (algebraMap R K).range → (∀ p ∈ P, p • θ ∈ (algebraMap R K).range) →
        ∀ a : R, a • (t₀ * θ) ∈ (I : Submodule R K) → a ∈ P := by
  obtain ⟨t₀, ht₀, hgen⟩ := exists_gen P hP I hI
  refine ⟨t₀, ht₀, hgen, fun θ hθ hPθ a ha => ?_⟩
  by_contra haP
  have hθP : ∀ z ∈ P • (I : Submodule R K), θ * z ∈ (I : Submodule R K) := by
    intro z hz
    refine Submodule.smul_induction_on hz (fun p hp n hn => ?_) (fun x y hx hy => ?_)
    · obtain ⟨q, hq⟩ := hPθ p hp
      have : θ * p • n = q • n := by
        rw [Algebra.smul_def q, hq, smul_mul_assoc, mul_smul_comm]
      rw [this]; exact Submodule.smul_mem _ _ hn
    · rw [mul_add]; exact add_mem hx hy
  have haθ : a • θ ∈ (algebraMap R K).range := by
    refine mem_range_of_mul_mem I hI _ fun t ht => ?_
    obtain ⟨b, hb⟩ := hgen t ht
    have : a • θ * t = a • (θ * (t - b • t₀)) + b • (a • (t₀ * θ)) := by
      simp only [Algebra.smul_def]; ring
    rw [this]
    exact add_mem (Submodule.smul_mem _ _ (hθP _ hb)) (Submodule.smul_mem _ _ ha)
  obtain ⟨u, p, hp, hup⟩ := hP.exists_inv haP
  apply hθ
  have : θ = algebraMap R K u * (a • θ) + p • θ := by
    rw [← Algebra.smul_def, smul_smul, ← add_smul, hup, one_smul]
  rw [this]
  exact add_mem (mul_mem ⟨u, rfl⟩ haθ) (hPθ p hp)

theorem inverseHalfDifferent_ne_zero (D : D7) : D.host.AA0 ≠ 0 := by
  have hb : D.host.𝔟 ≠ ⊥ := by
    intro h
    have h1 := D.host.𝔟_spec.1
    rw [h, Ideal.bot_mul] at h1
    exact differentIdeal_ne_bot h1
  unfold Formalism.BasicNotions.Host.AA0
  exact inv_ne_zero (FractionalIdeal.coeIdeal_ne_zero.2 hb)

theorem isFractional_Iid (D : D7) (cc : Ideal (𝓞 D.host.K)) : IsFractional (𝓞 D.host.E)⁰ (Iid D cc) := by
  obtain ⟨d, hd, hd'⟩ := D.host.AA0.isFractional
  refine (FractionalIdeal.isFractional_span_iff).2 ⟨d, hd, ?_⟩
  rintro _ ⟨c, -, a, ha, rfl⟩
  rw [← mul_smul_comm]
  refine IsLocalization.isInteger_mul ⟨algebraMap (𝓞 D.host.K) (𝓞 D.host.E) c, rfl⟩ (hd' a ha)

theorem Iid_ne_bot (D : D7) (cc : Ideal (𝓞 D.host.K)) (hc : cc ≠ ⊥) : Iid D cc ≠ ⊥ := by
  obtain ⟨c, hcc, hc0⟩ := (Submodule.ne_bot_iff _).1 hc
  have hA : (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) ≠ ⊥ := fun h =>
    inverseHalfDifferent_ne_zero D (FractionalIdeal.coeToSubmodule_eq_bot.1 h)
  obtain ⟨a, ha, ha0⟩ := (Submodule.ne_bot_iff _).1 hA
  refine (Submodule.ne_bot_iff _).2 ⟨_, Submodule.subset_span ⟨c, hcc, a, ha, rfl⟩, mul_ne_zero ?_ ha0⟩
  intro h
  apply hc0
  apply Subtype.ext
  apply Subtype.ext
  exact h

theorem exists_generator_Iid : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)), cc ≠ ⊥ → ∀ P : Ideal (𝓞 D.host.E), P.IsMaximal → ∃ t₀ ∈ Iid D cc, (∀ t ∈ Iid D cc, ∃ a : 𝓞 D.host.E, t - a • t₀ ∈ P • Iid D cc) ∧ ∀ θ : D.host.E, ¬ IntE D θ → (∀ p ∈ P, IntE D (p • θ)) → ∀ a : 𝓞 D.host.E, a • (t₀ * θ) ∈ Iid D cc → a ∈ P := by
  intro D cc hc P hP
  exact exists_gen_and P hP ⟨Iid D cc, isFractional_Iid D cc⟩
    (fun h => Iid_ne_bot D cc hc (FractionalIdeal.coeToSubmodule_eq_bot.2 h))

end GlobalTheory.IdealGenerator
