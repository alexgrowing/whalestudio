import Mathlib
import ReciprocityTheory.GaloisValuations.Global
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicPrimePowAutomorphismInertialAtPrimeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteGaloisInertiaLiftsAbsoluteInertiaRatStatement

open Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField Polynomial

namespace GlobalTheory.CycInertia

theorem exists_aut_pow {K L : Type} [Field K] [Field L] [Algebra K L]
    {n : ℕ} [NeZero n] [IsCyclotomicExtension {n} K L] (hirr : Irreducible (cyclotomic n K))
    {a : ℕ} (ha : a.Coprime n) :
    ∃ (τ : L ≃ₐ[K] L) (z : L), IsPrimitiveRoot z n ∧ τ z = z ^ a := by
  have hz := IsCyclotomicExtension.zeta_spec n K L
  have hpow : IsPrimitiveRoot (IsCyclotomicExtension.zeta n K L ^ a) n := hz.pow_of_coprime a ha
  exact ⟨IsCyclotomicExtension.fromZetaAut hpow hirr, IsCyclotomicExtension.zeta n K L, hz,
    IsCyclotomicExtension.fromZetaAut_spec hpow hirr⟩

theorem exists_mem_Ine_toZModPow (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ)
    [Fact l.Prime] (A : ValuationSubring Ω) (hA : A.valuation (l : Ω) < 1) (v : ℤ_[l]ˣ) (k : ℕ) :
    ∃ σ ∈ Ine (F := ℚ) A, PadicInt.toZModPow k ((cycZ ℚ Ω l σ : ℤ_[l]ˣ) : ℤ_[l]) =
      PadicInt.toZModPow k (v : ℤ_[l]) := by
  have hl : l.Prime := Fact.out
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : NeZero (l ^ k) := ⟨pow_ne_zero k hl.ne_zero⟩
  haveI : NeZero ((l : ℕ) : Ω) := ⟨by
    have h := (algebraMap ℚ Ω).injective.ne (Nat.cast_ne_zero.mpr hl.ne_zero : (l : ℚ) ≠ 0)
    simpa using h⟩
  haveI : ∀ i, HasEnoughRootsOfUnity Ω (l ^ i) := fun i => inferInstance
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ k)

  have e : (IntermediateField.adjoin ℚ {ζ}).algebra' =
      (DivisionRing.toRatAlgebra : Algebra ℚ (IntermediateField.adjoin ℚ {ζ})) :=
    Subsingleton.elim _ _
  haveI : IsCyclotomicExtension {l ^ k} ℚ (IntermediateField.adjoin ℚ {ζ}) := by
    rw [← e]
    exact hζ.intermediateField_adjoin_isCyclotomicExtension ℚ
  haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {ζ}) :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral ζ)
  haveI : IsGalois ℚ (IntermediateField.adjoin ℚ {ζ}) :=
    IsCyclotomicExtension.isGalois {l ^ k} ℚ (IntermediateField.adjoin ℚ {ζ})

  let u : (ZMod (l ^ k))ˣ :=
    Units.map (PadicInt.toZModPow k : ℤ_[l] →+* ZMod (l ^ k)).toMonoidHom v
  have hu : (u : ZMod (l ^ k)) = PadicInt.toZModPow k (v : ℤ_[l]) := rfl
  obtain ⟨τ, z, hz, hτz⟩ := exists_aut_pow (K := ℚ) (L := IntermediateField.adjoin ℚ {ζ})
    (cyclotomic.irreducible_rat (Nat.pos_of_neZero (l ^ k))) (ZMod.val_coe_unit_coprime u)
  obtain ⟨hτ₁, hτ₂⟩ := GlobalTheory.T.cyclotomicPrimePow_automorphism_inertial_at_prime Ω l k A hA ζ hζ τ
  obtain ⟨σ, hσ, hστ⟩ := GlobalTheory.T.finiteGaloisInertia_lifts_absoluteInertia_rat Ω l A hA (IntermediateField.adjoin ℚ {ζ}) τ hτ₁ hτ₂
  refine ⟨σ, hσ, ?_⟩
  have hzΩ : IsPrimitiveRoot (z : Ω) (l ^ k) := IsPrimitiveRoot.coe_submonoidClass_iff.mpr hz

  have h₁ : σ (z : Ω) = (z : Ω) ^ (PadicInt.toZModPow k
      ((cycZ ℚ Ω l σ : ℤ_[l]ˣ) : ℤ_[l])).val :=
    cyclotomicCharacter.spec l (MulSemiringAction.toRingAut (G ℚ Ω) Ω σ) (z : Ω) hzΩ.pow_eq_one
  have h₂ : σ (z : Ω) = (z : Ω) ^ (u : ZMod (l ^ k)).val := by
    rw [hστ z, hτz]
    simp
  rw [← hu]
  apply ZMod.val_injective
  exact hzΩ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) (h₁.symm.trans h₂)

theorem cycZ_Ine_surjective : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ)
    [Fact l.Prime] (A : ValuationSubring Ω), A.valuation (l : Ω) < 1 → ∀ v : ℤ_[l]ˣ,
    ∃ σ ∈ Ine (F := ℚ) A, cycZ (F := ℚ) (Ω := Ω) l σ = v := by
  intro Ω _ _ _ l _ A hA v

  let f : G ℚ Ω → ℤ_[l] := fun σ => ((cycZ ℚ Ω l σ : ℤ_[l]ˣ) : ℤ_[l])
  have hf : Continuous f := Units.continuous_val.comp (continuous_cycZ ℚ Ω l)

  let t : ℕ → Set (G ℚ Ω) := fun k => (Ine (F := ℚ) A : Set (G ℚ Ω)) ∩
    {σ | PadicInt.toZModPow k (f σ) = PadicInt.toZModPow k (v : ℤ_[l])}
  have hcl : ∀ k, IsClosed (t k) := by
    intro k
    refine (isClosed_Ine (F := ℚ) A).inter ?_
    have hset : {σ | PadicInt.toZModPow k (f σ) = PadicInt.toZModPow k (v : ℤ_[l])} =
        {σ | ‖f σ - (v : ℤ_[l])‖ ≤ (l : ℝ) ^ (-(k : ℤ))} := by
      ext σ
      simp only [Set.mem_setOf_eq]
      rw [PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow, RingHom.mem_ker,
        map_sub, sub_eq_zero]
    rw [hset]
    exact isClosed_le (continuous_norm.comp (hf.sub continuous_const)) continuous_const
  have hdec : ∀ k, t (k + 1) ⊆ t k := by
    rintro k σ ⟨h₁, h₂⟩
    refine ⟨h₁, ?_⟩
    simp only [Set.mem_setOf_eq] at h₂ ⊢
    rw [← PadicInt.cast_toZModPow k (k + 1) (Nat.le_succ k) (f σ),
      ← PadicInt.cast_toZModPow k (k + 1) (Nat.le_succ k), h₂]
  have hne : ∀ k, (t k).Nonempty := fun k => by
    obtain ⟨σ, hσ, h⟩ := exists_mem_Ine_toZModPow Ω l A hA v k
    exact ⟨σ, hσ, h⟩
  obtain ⟨σ, hσ⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed t hdec hne
    (hcl 0).isCompact hcl
  rw [Set.mem_iInter] at hσ
  exact ⟨σ, (hσ 0).1, Units.ext (PadicInt.ext_of_toZModPow.mp fun k => (hσ k).2)⟩

end GlobalTheory.CycInertia
