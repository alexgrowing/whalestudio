import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowNotMemMaximalIdealPowSucc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalFibreIsReducedOfField

open IsLocalRing GlobalTheory.Poinc.Eq8
open scoped TensorProduct

namespace GlobalTheory.TraitLift

theorem exists_lift_adicCompletion (A V : Type) [CommRing A] [IsLocalRing A] [Algebra.EssFiniteType ℤ A]
    [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Algebra A V] :
    ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsDiscreteValuationRing V') (h : V →+* V')
      (g : AdicCompletion (maximalIdeal A) A →+* V'), IsAdicComplete (maximalIdeal V') V' ∧
      g.comp (algebraMap A _) = h.comp (algebraMap A V) ∧ ∀ ϖ : V, Irreducible ϖ → Irreducible (h ϖ) := by
  haveI : IsNoetherianRing A := Algebra.EssFiniteType.isNoetherianRing ℤ A
  let R := AdicCompletion (maximalIdeal A) A
  haveI : Module.FaithfullyFlat A R := Module.FaithfullyFlat.of_flat_of_isLocalHom
  letI : Field (V ⧸ maximalIdeal V) := Ideal.Quotient.field _
  let C := V ⊗[A] R
  let e : (C ⧸ (maximalIdeal V).map (algebraMap V C)) ≃+* R ⊗[A] (V ⧸ maximalIdeal V) :=
    ((Algebra.TensorProduct.quotIdealMapEquivQuotTensor C (maximalIdeal V)).toRingEquiv.trans
      (Algebra.TensorProduct.cancelBaseChange A V V (V ⧸ maximalIdeal V) R).toRingEquiv).trans
      (Algebra.TensorProduct.comm A _ _).toRingEquiv
  haveI := formalFibre_isReduced_of_field A (V ⧸ maximalIdeal V)
  haveI : Nontrivial (R ⊗[A] (V ⧸ maximalIdeal V)) := inferInstance
  obtain ⟨V', i1, i2, i3, h₀, hc, hirr⟩ := GlobalTheory.ReducedFibre.exists_cdvr_of_flat_of_isReduced V C
    e.toEquiv.nontrivial (isReduced_of_injective e e.injective)
  refine ⟨V', i1, i2, i3, h₀.comp (algebraMap V C),
    h₀.comp (Algebra.TensorProduct.includeRight (R := A) (A := V) (B := R)).toRingHom, hc, ?_, hirr⟩
  ext a
  simp only [RingHom.comp_apply]
  congr 1
  rw [← IsScalarTower.algebraMap_apply]
  exact (Algebra.TensorProduct.includeRight (R := A) (A := V) (B := R)).commutes a

theorem isLocalHom_and_injective {V V' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [CommRing V'] [IsDomain V'] (h : V →+* V') (hh : ∀ ϖ : V, Irreducible ϖ → Irreducible (h ϖ)) :
    Function.Injective h ∧ IsLocalHom h := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  refine ⟨(injective_iff_map_eq_zero h).mpr fun x hx => ?_, ⟨fun x hx => ?_⟩⟩
  · by_contra h0
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h0 hϖ
    rw [map_mul, map_pow] at hx
    exact mul_ne_zero (u.isUnit.map h).ne_zero (pow_ne_zero n (hh ϖ hϖ).ne_zero) hx
  · by_contra hu
    have hm : x ∈ maximalIdeal V := hu
    rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at hm
    exact (hh ϖ hϖ).not_isUnit (isUnit_of_dvd_unit (map_dvd h hm) hx)

theorem exists_lift_of_isCpl : ∀ (A R V : Type) [CommRing A] [IsLocalRing A] [Algebra.EssFiniteType ℤ A] [CommRing R] (j : A →+* R), IsCpl j → ∀ [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (f : A →+* V), ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsDiscreteValuationRing V') (h : V →+* V') (g : R →+* V'), IsAdicComplete (maximalIdeal V') V' ∧ Function.Injective h ∧ IsLocalHom h ∧ g.comp j = h.comp f ∧ ∀ ϖ : V, Irreducible ϖ → Irreducible (h ϖ) := by
  intro A R V _ _ _ _ j hj _ _ _ f
  obtain ⟨e, he⟩ := hj
  letI : Algebra A V := f.toAlgebra
  obtain ⟨V', i1, i2, i3, h, g, hc, hcomp, hirr⟩ := exists_lift_adicCompletion A V
  obtain ⟨hinj, hloc⟩ := isLocalHom_and_injective h hirr
  refine ⟨V', i1, i2, i3, h, g.comp e.symm.toRingHom, hc, hinj, hloc, ?_, hirr⟩
  ext a
  have := RingHom.congr_fun hcomp a
  simp only [RingHom.comp_apply] at this ⊢
  rw [← he a]
  simpa [RingHom.algebraMap_toAlgebra] using this

end GlobalTheory.TraitLift
