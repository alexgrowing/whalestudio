import Mathlib
import GroundTheory.GlobalFields.GlobalReciprocity.NormSquare
import GroundTheory.GlobalFields.CyclotomicCharacters.DegreeDecomposition

namespace GroundTheory.Global

open IsDedekindDomain NumberField IntermediateField
open scoped Pointwise

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

namespace FiniteSubfield

variable (P : Ideal (𝓞 ℚ̄)) [P.IsPrime] (hP : P ≠ ⊥)

def placeBelow (F : FiniteSubfield) : HeightOneSpectrum (𝓞 F.1) where
  asIdeal := P.comap (algebraMap (𝓞 F.1) (𝓞 ℚ̄))
  isPrime := Ideal.comap_isPrime _ _
  ne_bot := fun h ↦ hP (Ideal.eq_bot_of_comap_eq_bot h)

theorem placeBelow_asIdeal (F : FiniteSubfield) :
    (placeBelow P hP F).asIdeal = P.comap (algebraMap (𝓞 F.1) (𝓞 ℚ̄)) :=
  rfl

instance liesOver_placeBelow {F E : FiniteSubfield} [Fact (F ≤ E)] :
    (placeBelow P hP E).asIdeal.LiesOver (placeBelow P hP F).asIdeal :=
  ⟨by
    rw [Ideal.under, placeBelow_asIdeal, placeBelow_asIdeal, Ideal.comap_comap]
    rfl⟩

variable {P}

omit [P.IsPrime] in

theorem comap_smul {F E : FiniteSubfield} [Fact (F ≤ E)]
    [(E.1.fixingSubgroup.subgroupOf F.1.fixingSubgroup).Normal] (g : F.1.fixingSubgroup) :
    ((g : ℚ̄ ≃ₐ[ℚ] ℚ̄) • P).comap (algebraMap (𝓞 E.1) (𝓞 ℚ̄)) =
      restrictHom (E := E) g • P.comap (algebraMap (𝓞 E.1) (𝓞 ℚ̄)) := by
  ext a
  rw [Ideal.mem_comap, Ideal.mem_pointwise_smul_iff_inv_smul_mem,
    Ideal.mem_pointwise_smul_iff_inv_smul_mem, Ideal.mem_comap]
  have : (g : ℚ̄ ≃ₐ[ℚ] ℚ̄)⁻¹ • algebraMap (𝓞 E.1) (𝓞 ℚ̄) a =
      algebraMap (𝓞 E.1) (𝓞 ℚ̄) ((restrictHom (E := E) g)⁻¹ • a) := by
    apply RingOfIntegers.ext
    rw [← map_inv]
    change ((g : ℚ̄ ≃ₐ[ℚ] ℚ̄)⁻¹) ((a : E.1) : ℚ̄) = ((restrictHom (E := E) g⁻¹ (a : E.1) : E.1) : ℚ̄)
    rw [coe_restrictHom_apply]
    rfl
  rw [this]

theorem restrictHom_mem_stabilizer {F E : FiniteSubfield} [Fact (F ≤ E)]
    [(E.1.fixingSubgroup.subgroupOf F.1.fixingSubgroup).Normal] (g : F.1.fixingSubgroup)
    (hg : (g : ℚ̄ ≃ₐ[ℚ] ℚ̄) ∈ MulAction.stabilizer (ℚ̄ ≃ₐ[ℚ] ℚ̄) P) :
    restrictHom (E := E) g ∈ MulAction.stabilizer (E.1 ≃ₐ[F.1] E.1) (placeBelow P hP E).asIdeal := by
  rw [MulAction.mem_stabilizer_iff, placeBelow_asIdeal, ← comap_smul, MulAction.mem_stabilizer_iff.1 hg]

theorem exists_mem_stabilizer_restrictHom_eq {F E : FiniteSubfield} [Fact (F ≤ E)]
    [(E.1.fixingSubgroup.subgroupOf F.1.fixingSubgroup).Normal] (τ : F.1.fixingSubgroup)
    (hτ : restrictHom (E := E) τ ∈ MulAction.stabilizer (E.1 ≃ₐ[F.1] E.1) (placeBelow P hP E).asIdeal) :
    ∃ σ : F.1.fixingSubgroup, (σ : ℚ̄ ≃ₐ[ℚ] ℚ̄) ∈ MulAction.stabilizer (ℚ̄ ≃ₐ[ℚ] ℚ̄) P ∧
      restrictHom (E := E) σ = restrictHom (E := E) τ := by
  have h : (((τ⁻¹ : F.1.fixingSubgroup) : ℚ̄ ≃ₐ[ℚ] ℚ̄) • P).comap (algebraMap (𝓞 E.1) (𝓞 ℚ̄)) =
      P.comap (algebraMap (𝓞 E.1) (𝓞 ℚ̄)) := by
    rw [comap_smul, map_inv]
    exact MulAction.mem_stabilizer_iff.1 (inv_mem hτ)
  obtain ⟨σ, hσP, hστ⟩ := Cyclotomic.exists_mem_stabilizer_of_comap_eq E.1 P τ h
  have hσF : σ ∈ F.1.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    rw [hστ x ((Fact.out : F ≤ E) hx)]
    exact (IntermediateField.mem_fixingSubgroup_iff F.1 _).1 τ.2 x hx
  refine ⟨⟨σ, hσF⟩, hσP, AlgEquiv.ext fun x ↦ Subtype.ext ?_⟩
  rw [coe_restrictHom_apply, coe_restrictHom_apply]
  exact hστ x x.2

variable (P)

theorem exists_placeBelow_eq (K : FiniteSubfield) (v : HeightOneSpectrum (𝓞 K.1)) :
    ∃ (P : Ideal (𝓞 ℚ̄)) (_ : P.IsPrime) (hP : P ≠ ⊥), placeBelow P hP K = v := by
  have hinj : Function.Injective (algebraMap (𝓞 K.1) (𝓞 ℚ̄)) := fun a b hab ↦
    RingOfIntegers.ext (Subtype.ext (congrArg (fun z : 𝓞 ℚ̄ ↦ (z : ℚ̄)) hab))
  obtain ⟨Q, -, hQ, hQv⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := 𝓞 ℚ̄) v.asIdeal ⊥
    (by rw [Ideal.comap_bot_of_injective _ hinj]; exact bot_le)
  have hQ0 : Q ≠ ⊥ := by
    rintro rfl
    apply v.ne_bot
    rw [← hQv, Ideal.comap_bot_of_injective _ hinj]
  exact ⟨Q, hQ, hQ0, HeightOneSpectrum.ext hQv⟩

include hP in

theorem exists_liesOver_prime : ∃ p : ℕ, p.Prime ∧ P.LiesOver (Ideal.span {(p : ℤ)}) := by
  have : Algebra.IsIntegral ℤ (𝓞 ℚ̄) := inferInstanceAs (Algebra.IsIntegral ℤ (integralClosure ℤ ℚ̄))
  have hI : (P.comap (algebraMap ℤ (𝓞 ℚ̄))).IsPrime := Ideal.comap_isPrime _ _
  rcases Ideal.isPrime_int_iff.1 hI with h | ⟨p, hp, h⟩
  · exact absurd (Ideal.eq_bot_of_comap_eq_bot h) hP
  · exact ⟨p, hp, ⟨h.symm⟩⟩

end FiniteSubfield

end

end GroundTheory.Global
