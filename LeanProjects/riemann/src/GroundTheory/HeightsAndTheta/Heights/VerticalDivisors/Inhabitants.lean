import Mathlib
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.IntToFracInjective
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain

noncomputable section

theorem NormLength.hypotheses_inhabited :
    Function.Injective (fun x : ℤ_[2] => (1 : ℤ_[2]) * x) := fun x y h => by
  simpa using h

theorem LengthDecomp.hypotheses_inhabited :
    Module.length ℤ_[2] (ℤ_[2] ⧸ Ideal.span {(2 : ℤ_[2])}) ≠ ⊤ :=
  Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero two_ne_zero)

theorem PrimitiveUnit.hypotheses_inhabited :
    (∃ m, IsUnit ((1 : MvPolynomial (Fin 1) ℤ_[2]).coeff m)) ∧
      (1 : MvPolynomial (Fin 1) ℤ_[2]).map (algebraMap ℤ_[2] ℚ_[2]) =
        C (1 : ℚ_[2]) * (1 : MvPolynomial (Fin 1) ℤ_[2]).map (algebraMap ℤ_[2] ℚ_[2]) :=
  ⟨⟨0, by simp⟩, by simp⟩

theorem NormFormEval.hypotheses_inhabited : Module.Free ℚ ℚ ∧ Module.Finite ℚ ℚ :=
  ⟨inferInstance, inferInstance⟩

theorem ChartTorsion.hypotheses_inhabited :
    (⊥ : Ideal (MvPolynomial (Fin 1) ℤ)).IsPrime ∧
      (∀ c : ℤ, C c ∈ (⊥ : Ideal (MvPolynomial (Fin 1) ℤ)) → c = 0) ∧
      C (1 : ℤ) * (0 : MvPolynomial (Fin 1 ⊕ (Fin 1 × Fin 1)) ℤ) ∈ incIdeal ⊥ 1 := by
  refine ⟨Ideal.isPrime_bot, fun c hc => ?_, by simp⟩
  rw [Ideal.mem_bot] at hc
  exact (C_eq_zero).mp hc

theorem IncidenceNull.hypotheses_inhabited :
    IsChowForm (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) 1 (X (0, 0)) :=
  isChowForm_point ℚ

abbrev pointPar : Par 0 1 → FractionRing (MvPolynomial (Par 0 1) ℚ) :=
  fun p => algebraMap (MvPolynomial (Par 0 1) ℚ) (FractionRing (MvPolynomial (Par 0 1) ℚ)) (X p)

theorem pointPar_algebraicIndependent : AlgebraicIndependent ℚ pointPar := by
  have h := MvPolynomial.algebraicIndependent_X (Par 0 1) ℚ
  have hinj : Function.Injective (IsScalarTower.toAlgHom ℚ (MvPolynomial (Par 0 1) ℚ)
      (FractionRing (MvPolynomial (Par 0 1) ℚ))) :=
    IsFractionRing.injective (MvPolynomial (Par 0 1) ℚ) (FractionRing (MvPolynomial (Par 0 1) ℚ))
  have h2 := h.map' hinj
  have e : (⇑(IsScalarTower.toAlgHom ℚ (MvPolynomial (Par 0 1) ℚ)
      (FractionRing (MvPolynomial (Par 0 1) ℚ))) ∘ X) = pointPar := by
    funext p
    simp only [Function.comp_apply, IsScalarTower.coe_toAlgHom', pointPar]
  rw [e] at h2
  exact h2

theorem ChowNormForm.hypotheses_inhabited :
    AlgebraicIndependent ℚ pointPar ∧ IsProjPrime (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) ∧
      IsChowForm (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) (0 + 1) (X (0, 0)) :=
  ⟨pointPar_algebraicIndependent, isProjPrime_point ℚ, isChowForm_point ℚ⟩

theorem SecLinNZD.hypotheses_inhabited :
    AlgebraicIndependent ℚ pointPar ∧ IsProjPrime (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) ∧
      IsChowForm (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) (0 + 1) (X (0, 0)) ∧
      linForm (fun _ => (1 : ℚ)) ∉ (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) :=
  ⟨pointPar_algebraicIndependent, isProjPrime_point ℚ, isChowForm_point ℚ, linForm_one_not_mem_point ℚ⟩

abbrev pointForm : MvPolynomial (Fin (0 + 1) × Fin 1) (𝓞 ℚ) := X (0, 0)

theorem pointForm_map : pointForm.map (algebraMap (𝓞 ℚ) ℚ) = X (0, 0) := by
  simp [pointForm]

theorem NormIdentity.hypotheses_inhabited (v : HeightOneSpectrum (𝓞 ℚ)) :
    IsProjPrime (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) ∧
      IsChowForm (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) (0 + 1) (pointForm.map (algebraMap (𝓞 ℚ) ℚ)) ∧
      linForm (fun j => (((fun _ => (1 : 𝓞 ℚ)) : Fin 1 → 𝓞 ℚ) j : ℚ)) ∉
        (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) ∧
      ∃ m, pointForm.coeff m ∉ v.asIdeal := by
  refine ⟨isProjPrime_point ℚ, by rw [pointForm_map]; exact isChowForm_point ℚ, ?_, ?_⟩
  · simpa using linForm_one_not_mem_point ℚ
  · refine ⟨Finsupp.single (0, 0) 1, ?_⟩
    have h1 : pointForm.coeff (Finsupp.single (0, 0) 1) = 1 := by simp [pointForm]
    rw [h1]
    exact fun h => v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h)

theorem SecBFinite.hypotheses_inhabited :
    IsProjPrime (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) ∧
      IsChowForm (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) (0 + 1) (X (0, 0)) :=
  ⟨isProjPrime_point ℚ, isChowForm_point ℚ⟩

theorem GaussDVR.hypotheses_inhabited : (1 : MvPolynomial (Par 0 1) (𝓞 ℚ)) ≠ 0 := one_ne_zero

theorem PrimitiveScale.hypotheses_inhabited : (X 0 : MvPolynomial (Fin 1) ℚ) ≠ 0 := X_ne_zero 0

end

end GroundTheory.Heights₂.Heights.Vertical
