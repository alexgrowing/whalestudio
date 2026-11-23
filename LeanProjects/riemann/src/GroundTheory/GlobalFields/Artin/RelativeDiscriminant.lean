import Mathlib
import GroundTheory.GlobalFields.SemilocalAlgebras.ContinuousCompletionMap
set_option maxSynthPendingDepth 1

noncomputable section

open IsDedekindDomain NumberField Module

namespace GroundTheory.Global

section Def

variable (K M : Type*) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]

def relDiscr : Ideal (𝓞 K) :=
  Ideal.relNorm (𝓞 K) (differentIdeal (𝓞 K) (𝓞 M))

theorem relDiscr_ne_bot : relDiscr K M ≠ ⊥ := by
  rw [relDiscr, Ne, Ideal.relNorm_eq_bot_iff]
  exact differentIdeal_ne_bot

end Def

section Multiplicity

variable {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]

theorem prime_asIdeal {F : Type*} [Field F] [NumberField F] (u : HeightOneSpectrum (𝓞 F)) :
    Prime u.asIdeal :=
  Ideal.prime_of_isPrime u.ne_bot u.isPrime

theorem emultiplicity_asIdeal_of_isMaximal {F : Type*} [Field F] [NumberField F]
    (u : HeightOneSpectrum (𝓞 F)) (p : Ideal (𝓞 F)) [hp : p.IsMaximal] :
    emultiplicity u.asIdeal p = if u.asIdeal = p then 1 else 0 := by
  split_ifs with h
  · have h1 := emultiplicity_pow_self_of_prime (prime_asIdeal u) 1
    rw [pow_one] at h1
    rw [← h, h1]
    rfl
  · rw [emultiplicity_eq_zero, Ideal.dvd_iff_le]
    intro hle
    exact h (hp.eq_of_le u.isPrime.ne_top hle).symm

variable (v : HeightOneSpectrum (𝓞 K))

theorem emultiplicity_relNorm_of_prime (p : Ideal (𝓞 M)) (hp : Prime p) :
    emultiplicity v.asIdeal (Ideal.relNorm (𝓞 K) p) =
      ∑ w : SemiLocal.PlacesOver M v,
        (w.1.asIdeal.inertiaDeg (𝓞 K) : ℕ∞) * emultiplicity w.1.asIdeal p := by
  have hp0 : p ≠ ⊥ := hp.ne_zero
  have hpp : p.IsPrime := (Ideal.prime_iff_isPrime hp0).1 hp
  have hpm : p.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hp0 hpp
  have hqm : (p.under (𝓞 K)).IsMaximal := Ideal.IsMaximal.under (𝓞 K) p
  rw [Ideal.relNorm_eq_pow_of_isMaximal p (p.under (𝓞 K)),
    emultiplicity_pow (prime_asIdeal v), emultiplicity_asIdeal_of_isMaximal]
  simp only [emultiplicity_asIdeal_of_isMaximal, mul_ite, mul_one, mul_zero]
  by_cases hv : v.asIdeal = p.under (𝓞 K)
  · rw [if_pos hv]
    have hlies : p.LiesOver v.asIdeal := ⟨hv⟩
    let w0 : SemiLocal.PlacesOver M v := ⟨⟨p, hpp, hp0⟩, hlies⟩
    rw [Finset.sum_eq_single w0]
    · simp [w0]
    · intro w _ hw
      rw [if_neg]
      intro h
      apply hw
      apply Subtype.ext
      apply HeightOneSpectrum.ext
      exact h
    · simp
  · rw [if_neg hv]
    symm
    apply Finset.sum_eq_zero
    intro w _
    rw [if_neg]
    intro h
    apply hv
    rw [← h]
    exact Ideal.over_def w.1.asIdeal v.asIdeal

theorem emultiplicity_relNorm (I : Ideal (𝓞 M)) (hI : I ≠ ⊥) :
    emultiplicity v.asIdeal (Ideal.relNorm (𝓞 K) I) =
      ∑ w : SemiLocal.PlacesOver M v,
        (w.1.asIdeal.inertiaDeg (𝓞 K) : ℕ∞) * emultiplicity w.1.asIdeal I := by
  induction I using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact absurd rfl hI
  | h₂ x hx =>
    rw [Ideal.isUnit_iff.1 hx, Ideal.relNorm_top, ← Ideal.one_eq_top,
      emultiplicity_of_one_right (prime_asIdeal v).not_isUnit]
    symm
    apply Finset.sum_eq_zero
    intro w _
    rw [← Ideal.one_eq_top, emultiplicity_of_one_right (prime_asIdeal w.1).not_isUnit, mul_zero]
  | h₃ a p ha hp ih =>
    rw [map_mul, emultiplicity_mul (prime_asIdeal v), ih ha,
      emultiplicity_relNorm_of_prime v p hp, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro w _
    rw [emultiplicity_mul (prime_asIdeal w.1), mul_add]

theorem multiplicity_relNorm (I : Ideal (𝓞 M)) (hI : I ≠ ⊥) :
    multiplicity v.asIdeal (Ideal.relNorm (𝓞 K) I) =
      ∑ w : SemiLocal.PlacesOver M v,
        w.1.asIdeal.inertiaDeg (𝓞 K) * multiplicity w.1.asIdeal I := by
  have h := emultiplicity_relNorm v I hI
  rw [(FiniteMultiplicity.of_prime_left (prime_asIdeal v)
    ((Ideal.relNorm_eq_bot_iff (R := 𝓞 K)).not.2 hI)).emultiplicity_eq_multiplicity] at h
  simp only [fun w : SemiLocal.PlacesOver M v ↦
    (FiniteMultiplicity.of_prime_left (prime_asIdeal w.1) hI).emultiplicity_eq_multiplicity] at h
  exact_mod_cast h

theorem multiplicity_relDiscr_eq_sum :
    multiplicity v.asIdeal (relDiscr K M) =
      ∑ w : SemiLocal.PlacesOver M v,
        w.1.asIdeal.inertiaDeg (𝓞 K) * multiplicity w.1.asIdeal (differentIdeal (𝓞 K) (𝓞 M)) :=
  multiplicity_relNorm v _ differentIdeal_ne_bot

end Multiplicity

section Tower

variable (K M N : Type*) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
  [Field N] [NumberField N] [Algebra K N] [Algebra M N] [IsScalarTower K M N]

theorem relDiscr_tower :
    relDiscr K N = relDiscr K M ^ finrank M N * Ideal.relNorm (𝓞 K) (relDiscr M N) := by
  rw [relDiscr, differentIdeal_eq_differentIdeal_mul_differentIdeal (𝓞 K) (𝓞 M) (𝓞 N), map_mul,
    mul_comm, relDiscr, relDiscr, Ideal.relNorm_relNorm (𝓞 K) (𝓞 M),
    ← Ideal.relNorm_relNorm (𝓞 K) (𝓞 M) (Ideal.map _ _), Ideal.relNorm_algebraMap, map_pow,
    IsFractionRing.finrank_eq (𝓞 M) M (𝓞 N) N]

end Tower

section Rat

variable (M : Type*) [Field M] [NumberField M]

theorem differentIdeal_ringOfIntegers_rat :
    differentIdeal (𝓞 ℚ) (𝓞 M) = differentIdeal ℤ (𝓞 M) := by
  have h1 : differentIdeal ℤ (𝓞 ℚ) = ⊤ := by
    rw [← Ideal.absNorm_eq_one_iff, absNorm_differentIdeal ℚ, Rat.numberField_discr]
    rfl
  rw [differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 ℚ) (𝓞 M), h1, Ideal.map_top,
    Ideal.mul_top]

theorem absNorm_relDiscr_rat : Ideal.absNorm (relDiscr ℚ M) = (discr M).natAbs := by
  rw [relDiscr, Ideal.absNorm_relNorm, differentIdeal_ringOfIntegers_rat,
    absNorm_differentIdeal M]

end Rat

end GroundTheory.Global
