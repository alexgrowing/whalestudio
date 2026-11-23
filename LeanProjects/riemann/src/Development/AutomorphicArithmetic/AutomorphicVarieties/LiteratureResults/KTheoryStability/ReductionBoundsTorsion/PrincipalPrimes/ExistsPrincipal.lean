import Mathlib
import GroundTheory.GlobalFields.ClassFieldConsequences.HilbertClassField
import GroundTheory.GlobalFields.TateThesis.Chebotarev
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.ExistsPrimeAbsNormOfHasDirichletDensity

open NumberField IsDedekindDomain

noncomputable section

namespace PositivityTheory.KB.PrincipalPrimes

theorem exists_principal (L : Type) [Field L] [NumberField L] (T : Set (HeightOneSpectrum (𝓞 L)))
    (hT : T.Finite) : ∃ v : HeightOneSpectrum (𝓞 L), v ∉ T ∧ v.asIdeal.IsPrincipal := by
  let Ω := AlgebraicClosure L
  let H := GroundTheory.Global.hilbertClassField L Ω
  have : NumberField H := NumberField.of_module_finite L H
  have : IsGalois L H := inferInstance
  have hd := GroundTheory.Global.hasDirichletDensity_setOf_exists_arithFrobAt_mem (K := L) (L := H)
    ({1} : Set (H ≃ₐ[L] H)) (by
      intro σ hσ τ
      rw [Set.mem_singleton_iff] at hσ ⊢
      rw [hσ, mul_one, mul_inv_cancel])
  have hpos : (0 : ℝ) < (Nat.card ({1} : Set (H ≃ₐ[L] H)) : ℝ) / Nat.card (H ≃ₐ[L] H) :=
    div_pos (Nat.cast_pos.2 Nat.card_pos) (Nat.cast_pos.2 Nat.card_pos)
  obtain ⟨v, ⟨-, w, hw, hF⟩, hvT, -⟩ :=
    ReciprocityTheory.Neutral.Bridge.exists_prime_absNorm_of_hasDirichletDensity hd hpos hT
  refine ⟨v, hvT, ?_⟩
  have := hw
  have h1 := GroundTheory.Global.hilbertClassFieldArtinEquiv_mk0 L Ω v w
  rw [Set.mem_singleton_iff.1 hF, MulEquiv.map_eq_one_iff] at h1
  exact (ClassGroup.mk0_eq_one_iff _).1 h1

theorem finite_small (L : Type) [Field L] [NumberField L] (B : ℕ) :
    {v : HeightOneSpectrum (𝓞 L) | Ideal.absNorm v.asIdeal ≤ B}.Finite :=
  Set.Finite.preimage (f := fun v : HeightOneSpectrum (𝓞 L) => v.asIdeal)
    (fun _ _ _ _ h => HeightOneSpectrum.ext h) (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 L) B)

theorem exists_prime (L : Type) [Field L] [NumberField L] (B : ℕ) :
    ∃ π : 𝓞 L, Prime π ∧ B ≤ Ideal.absNorm (Ideal.span {π}) := by
  obtain ⟨v, hv, π, hπ⟩ := exists_principal L _ (finite_small L B)
  have hπ' : v.asIdeal = Ideal.span {π} := hπ
  have hne : π ≠ 0 := by
    rintro rfl
    exact v.ne_bot (by rw [hπ', Ideal.span_singleton_eq_bot])
  refine ⟨π, (Ideal.span_singleton_prime hne).1 (hπ' ▸ v.isPrime), ?_⟩
  rw [← hπ']
  simp only [Set.mem_ofPred_eq, not_le] at hv
  omega

end PositivityTheory.KB.PrincipalPrimes
