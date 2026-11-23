import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EmbeddingMemCoefficientField
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.FrobeniusOrbits Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC Formalism.L2.NC NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting

noncomputable section

namespace GlobalTheory.TameLift

theorem valuation_sub_lt_of_redThrough_eq {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {g : ℕ} [Fact g.Prime]
    (κ : IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar g) {x y : Ω} (hx : x ∈ A) (hy : y ∈ A)
    (h : redThrough A κ x = redThrough A κ y) : A.valuation (x - y) < 1 := by
  unfold redThrough at h
  rw [dif_pos hx, dif_pos hy] at h
  have h1 := κ.injective h
  have h2 : (⟨x, hx⟩ : A) - ⟨y, hy⟩ ∈ IsLocalRing.maximalIdeal A := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, h1, sub_self]
  have := (A.valuation_lt_one_iff _).1 h2
  simpa using this

theorem exists_lift : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 E)), IsPlaceOver (F := E) A v → ∀ (g : ℕ) [Fact g.Prime],
    ((g : ℕ) : 𝓞 E) ∈ v.asIdeal → ∀ (κ : IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar g) (m : ℕ), 0 < m → ¬ g ∣ m →
    ∀ c : Formalism.CyclotomicNorms.Fbar g, c ^ m = 1 → ∃ μ : Ω, μ ^ m = 1 ∧ redThrough A κ μ = c := by
  intro E Ω _ _ _ _ _ A v hA g hg hgv κ m hm hgm c hc
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  have : NeZero ((m : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr hm.ne'⟩
  have : NeZero m := ⟨hm.ne'⟩

  have hvg : A.valuation (g : Ω) < 1 := by
    have := (hA (g : 𝓞 E)).2 hgv
    simpa using this

  have hvm : ¬ A.valuation (m : Ω) < 1 := by
    intro hlt
    have hcop : Nat.Coprime m g :=
      Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hg.out).mpr hgm)
    obtain ⟨u, w, huw⟩ := Nat.isCoprime_iff_coprime.mpr hcop
    have e : ((u : Ω) * (m : Ω)) + (w : Ω) * (g : Ω) = 1 := by
      have := congrArg (fun z : ℤ => (z : Ω)) huw
      push_cast at this
      exact this
    have hu : A.valuation (u : Ω) ≤ 1 := (A.valuation_le_one_iff _).2 (intCast_mem A u)
    have hw : A.valuation (w : Ω) ≤ 1 := (A.valuation_le_one_iff _).2 (intCast_mem A w)
    have h1 : A.valuation ((u : Ω) * (m : Ω)) < 1 := by
      rw [Valuation.map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left zero_le' hu) hlt
    have h2 : A.valuation ((w : Ω) * (g : Ω)) < 1 := by
      rw [Valuation.map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left zero_le' hw) hvg
    have h3 := Valuation.map_add_lt A.valuation h1 h2
    rw [e, Valuation.map_one] at h3
    exact lt_irrefl _ h3
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω m
  have hζA : ζ ∈ A := mem_of_pow_eq_one A hm hζ.pow_eq_one
  have hr : IsPrimitiveRoot (redThrough A κ ζ) m := by
    refine IsPrimitiveRoot.mk_of_lt _ hm ?_ ?_
    · rw [← redThrough_pow A κ hζA, hζ.pow_eq_one, redThrough_one]
    · intro l hl hlm hrl
      rw [← redThrough_pow A κ hζA, ← redThrough_one A κ] at hrl
      have hv := valuation_sub_lt_of_redThrough_eq A κ (pow_mem hζA l) (one_mem A) hrl
      have heq : ζ ^ l = 1 := eq_of_pow_eq_one A hvm
        (by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]) (one_pow _) hv
      exact hζ.pow_ne_one_of_pos_of_lt hl.ne' hlm heq
  obtain ⟨i, -, hi⟩ := hr.eq_pow_of_pow_eq_one hc
  refine ⟨ζ ^ i, ?_, ?_⟩
  · rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  · rw [redThrough_pow A κ hζA, hi]

end GlobalTheory.TameLift
