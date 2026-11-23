import Mathlib
import ReciprocityTheory.AnalyticForms.RegularLocalRings.BaseChangeCB

namespace ReciprocityTheory.AnForm.R

open MvPolynomial

variable {σ : Type} [Fintype σ]

noncomputable def extC (𝔭 : Ideal (MvPolynomial σ ℚ)) : Ideal (MvPolynomial σ ℂ) :=
  Ideal.map (MvPolynomial.map (algebraMap ℚ ℂ)) 𝔭

theorem extC_isRadical (𝔭 : Ideal (MvPolynomial σ ℚ)) [𝔭.IsPrime] : (extC 𝔭).IsRadical := by
  rw [Ideal.isRadical_iff_quotient_reduced]
  have hA : IsDomain (MvPolynomial σ ℚ ⧸ 𝔭) := Ideal.Quotient.isDomain 𝔭
  have hK : IsReduced (TensorProduct ℚ (FractionRing (MvPolynomial σ ℚ ⧸ 𝔭)) ℂ) :=
    BaseChangeC.isReduced_tensor_of_essFiniteType _ ℂ
  have hK' : IsReduced (TensorProduct ℚ ℂ (FractionRing (MvPolynomial σ ℚ ⧸ 𝔭))) :=
    isReduced_of_injective (Algebra.TensorProduct.comm ℚ ℂ _) (Algebra.TensorProduct.comm ℚ ℂ _).injective
  have hinj : Function.Injective (Algebra.TensorProduct.map (1 : ℂ →ₐ[ℚ] ℂ)
      (IsScalarTower.toAlgHom ℚ (MvPolynomial σ ℚ ⧸ 𝔭) (FractionRing (MvPolynomial σ ℚ ⧸ 𝔭)))) :=
    Module.Flat.lTensor_preserves_injective_linearMap _
      (IsFractionRing.injective (MvPolynomial σ ℚ ⧸ 𝔭) (FractionRing (MvPolynomial σ ℚ ⧸ 𝔭)))
  have hT : IsReduced (TensorProduct ℚ ℂ (MvPolynomial σ ℚ ⧸ 𝔭)) := isReduced_of_injective _ hinj
  exact isReduced_of_injective (BaseChangeC.quotExtEquiv 𝔭).symm (BaseChangeC.quotExtEquiv 𝔭).symm.injective

theorem comap_of_mem_minimalPrimes_extC (𝔭 : Ideal (MvPolynomial σ ℚ)) [𝔭.IsPrime]
    (Q : Ideal (MvPolynomial σ ℂ)) (hQ : Q ∈ (extC 𝔭).minimalPrimes) :
    Q.comap (MvPolynomial.map (algebraMap ℚ ℂ)) = 𝔭 := by
  let _ : Algebra (MvPolynomial σ ℚ) (MvPolynomial σ ℂ) := MvPolynomial.algebraMvPolynomial
  have hflat : Module.Flat (MvPolynomial σ ℚ) (MvPolynomial σ ℂ) :=
    BaseChangeC.flat_mvPolynomial_rat_complex
  have hQp : Q.IsPrime := hQ.1.1
  have hle : 𝔭 ≤ Q.comap (MvPolynomial.map (algebraMap ℚ ℂ)) := Ideal.map_le_iff_le_comap.mp hQ.1.2
  have hPp : (Q.comap (MvPolynomial.map (algebraMap ℚ ℂ))).IsPrime := Ideal.comap_isPrime _ Q
  have hlo : Q.LiesOver (Q.comap (MvPolynomial.map (algebraMap ℚ ℂ))) := ⟨rfl⟩
  obtain ⟨Q', hQ'le, hQ'p, hQ'lo⟩ := Ideal.exists_ideal_le_liesOver_of_le (p := 𝔭) Q hle
  have hQ'over : Q'.comap (MvPolynomial.map (algebraMap ℚ ℂ)) = 𝔭 := hQ'lo.over.symm
  have hmapQ' : extC 𝔭 ≤ Q' := by
    unfold extC
    rw [Ideal.map_le_iff_le_comap, hQ'over]
  have hEq : Q = Q' := le_antisymm (hQ.2 ⟨hQ'p, hmapQ'⟩ hQ'le) hQ'le
  subst hEq
  exact hQ'over

theorem ringKrullDim_of_mem_minimalPrimes_extC (𝔭 : Ideal (MvPolynomial σ ℚ)) [𝔭.IsPrime]
    (Q : Ideal (MvPolynomial σ ℂ)) (hQ : Q ∈ (extC 𝔭).minimalPrimes) :
    ringKrullDim (MvPolynomial σ ℂ ⧸ Q) = ringKrullDim (MvPolynomial σ ℚ ⧸ 𝔭) := by
  have hQp : Q.IsPrime := hQ.1.1
  have hh := BaseChangeC.height_eq_of_mem_minimalPrimes_map 𝔭 Q hQ
  have h1 := BaseChangeC.height_add_ringKrullDim_quotient_fintype ℂ Q
  have h2 := BaseChangeC.height_add_ringKrullDim_quotient_fintype ℚ 𝔭
  rw [hh] at h1
  exact BaseChangeC.withBot_enat_cancel h1 h2

end ReciprocityTheory.AnForm.R
