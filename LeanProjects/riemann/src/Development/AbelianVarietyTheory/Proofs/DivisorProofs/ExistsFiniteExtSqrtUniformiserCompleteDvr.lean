import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
import Development.AbelianVarietyTheory.Definitions.Divisors.SpecializesGenericImage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralClosureCompleteNormalFiniteExtensi
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.USep

namespace GlobalTheory.USep

open Polynomial in

theorem exists_finite_ext_sq_eq_uniformiser : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → IsPrincipalIdealRing V → ∀ ϖ : V, Irreducible ϖ → ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsLocalRing V') (f : V →+* V') (t : V'), IsCN V' ∧ IsPrincipalIdealRing V' ∧ Function.Injective f ∧ IsLocalHom f ∧ f.Finite ∧ t ^ 2 = f ϖ := by
  intro V _ _ _ hV hP ϖ hϖ
  let K₀ := FractionRing V
  let p : K₀[X] := X ^ 2 - C (algebraMap V K₀ ϖ)
  let L := p.SplittingField
  have hdeg : (p.map (algebraMap K₀ L)).degree ≠ 0 := by
    rw [Polynomial.degree_map, Polynomial.degree_X_pow_sub_C (by norm_num)]
    norm_num
  obtain ⟨s, hs⟩ := (Polynomial.SplittingField.splits p).exists_eval_eq_zero hdeg
  have hs2 : s ^ 2 = algebraMap K₀ L (algebraMap V K₀ ϖ) := by
    simpa [p, sub_eq_zero] using hs
  obtain ⟨V₁, _, _, _, ρ, σ, hCN, hinj, hfin, hloc, hcomp⟩ :=
    GlobalTheory.Poinc.exists_integralClosure_isCN_finite_local V hV L
  obtain ⟨hN₁, hIC₁, _, _⟩ := hCN

  have hy2 : (σ s) ^ 2 = algebraMap V₁ (FractionRing V₁) (ρ ϖ) := by
    rw [← map_pow, hs2, hcomp]
  have hint : IsIntegral V₁ (σ s) := by
    refine ⟨X ^ 2 - C (ρ ϖ), monic_X_pow_sub_C _ two_ne_zero, ?_⟩
    simp [eval₂_sub, hy2, Algebra.algebraMap_eq_smul_one]
  obtain ⟨t, ht⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  have ht2 : t ^ 2 = ρ ϖ := by
    apply IsFractionRing.injective V₁ (FractionRing V₁)
    rw [map_pow, ht, hy2]

  letI : Algebra V V₁ := ρ.toAlgebra
  haveI : Module.Finite V V₁ := hfin
  haveI : Algebra.IsIntegral V V₁ := Algebra.IsIntegral.of_finite V V₁
  have hϖ0 : ρ ϖ ≠ 0 := by
    intro h; apply hϖ.ne_zero; apply hinj; simpa using h
  have hϖnu : ¬ IsUnit (ρ ϖ) := fun h => hϖ.not_isUnit ((isUnit_map_iff ρ ϖ).mp h)
  have hnf : ¬ IsField V₁ := by
    intro hF
    obtain ⟨b, hb⟩ := hF.mul_inv_cancel hϖ0
    exact hϖnu (IsUnit.of_mul_eq_one _ hb)
  have hdvr : IsDiscreteValuationRing V₁ := by
    have h03 := (IsDiscreteValuationRing.TFAE V₁ hnf).out 0 3
    refine h03.mpr ⟨hIC₁, ⟨maximalIdeal V₁, ⟨?_, inferInstance⟩, ?_⟩⟩
    · intro h
      apply hϖnu
      by_contra hu
      have : ρ ϖ ∈ maximalIdeal V₁ := hu
      rw [h] at this
      exact hϖ0 ((Submodule.mem_bot _).mp this)
    · rintro P ⟨hP0, hPp⟩
      obtain ⟨x, hxP, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP0
      have hc : P.comap (algebraMap V V₁) ≠ ⊥ :=
        Ideal.comap_ne_bot_of_integral_mem hx0 hxP (Algebra.IsIntegral.isIntegral x)
      haveI : (P.comap (algebraMap V V₁)).IsPrime := Ideal.IsPrime.comap _
      have hm : (P.comap (algebraMap V V₁)).IsMaximal := IsPrime.to_maximal_ideal hc
      have hPm : P.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap P hm
      exact IsLocalRing.eq_maximalIdeal hPm
  exact ⟨V₁, inferInstance, inferInstance, inferInstance, ρ, t, ⟨hN₁, hIC₁, by assumption, by assumption⟩,
    inferInstance, hinj, hloc, hfin, ht2⟩

end GlobalTheory.USep
