import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpanFinrankMaximalIdealLeNcardOfLeSupSq
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.MemRangeOfIsAlgebraicRatFun

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped TensorProduct

namespace GlobalTheory.PureTransc

theorem isDomain_tensor (k : Type) [Field k] (σ : Type) (A : Type) [CommRing A] [IsDomain A]
    [Algebra k A] : IsDomain (FractionRing (MvPolynomial σ k) ⊗[k] A) := by
  let P := MvPolynomial σ k
  let K := FractionRing P
  letI : Algebra (P ⊗[k] A) (K ⊗[k] A) :=
    (Algebra.TensorProduct.map (IsScalarTower.toAlgHom k P K) (AlgHom.id k A)).toAlgebra
  haveI : IsScalarTower P (P ⊗[k] A) (K ⊗[k] A) :=
    .of_algebraMap_eq fun x => by simp [RingHom.algebraMap_toAlgebra]
  haveI := IsLocalization.tensorProduct_tensorProduct k A (nonZeroDivisors P) K
    (by ext; simp [RingHom.algebraMap_toAlgebra])
  let e : P ⊗[k] A ≃+* MvPolynomial σ A :=
    ((Algebra.TensorProduct.comm k P A).toRingEquiv.trans
      (MvPolynomial.scalarRTensorAlgEquiv).toRingEquiv)
  haveI : IsDomain (P ⊗[k] A) := e.toMulEquiv.isDomain
  have hinj : Function.Injective (algebraMap P (P ⊗[k] A)) :=
    Algebra.TensorProduct.includeLeft_injective (S := P) (algebraMap k A).injective
  refine IsLocalization.isDomain_of_le_nonZeroDivisors (K ⊗[k] A)
    (M := Algebra.algebraMapSubmonoid (P ⊗[k] A) (nonZeroDivisors P)) ?_
  rintro _ ⟨p, hp, rfl⟩
  exact mem_nonZeroDivisors_of_ne_zero fun h =>
    nonZeroDivisors.ne_zero hp (hinj (h.trans (map_zero _).symm))

theorem isIntegral_of_isPullback : ∀ (k : Type) [Field k] (N : ℕ) (X X' : Scheme.{0}) [IsIntegral X]
    (f : X ⟶ Sp k) (f' : X' ⟶ Sp (FractionRing (MvPolynomial (Fin N) k))) (π : X' ⟶ X),
    IsPullback π f' f (spMap (algebraMap k (FractionRing (MvPolynomial (Fin N) k)))) →
    IsIntegral X' := by
  intro k _ N X X' _ f f' π H

  have chart (x : X) : ∃ (A : Type) (_ : CommRing A) (_ : Algebra k A) (_ : IsDomain A)
      (j : Sp A ⟶ X) (_ : IsOpenImmersion j) (q : PrimeSpectrum A),
      j q = x ∧ j ≫ f = spMap (algebraMap k A) := by
    obtain ⟨A, _, _, j, _, q, hq, hj⟩ := exists_affine_chart_over f x
    have : Nonempty (Spec (.of A)) := ⟨q⟩
    have : IsIntegral (Spec (.of A)) := isIntegral_of_isOpenImmersion j
    have : IsDomain A := (affine_isIntegral_iff (.of A)).1 this
    exact ⟨A, _, _, this, j, inferInstance, q, hq, hj⟩
  have lift {A : Type} [CommRing A] [Algebra k A] [IsDomain A] (j : Sp A ⟶ X) [IsOpenImmersion j]
      (hj : j ≫ f = spMap (algebraMap k A)) (x' : X') (hx : π x' ∈ Set.range j) :
      ∃ (j₀ : Sp (FractionRing (MvPolynomial (Fin N) k) ⊗[k] A) ⟶ X') (_ : IsOpenImmersion j₀),
        x' ∈ Set.range j₀ := by
    obtain ⟨j₀, hj₀, H'⟩ := exists_affine_chart_of_isPullback H j hj
    refine ⟨j₀, hj₀, ?_⟩
    have hr : x' ∈ Set.range (Limits.pullback.fst π j) := by
      rw [Scheme.Pullback.range_fst]; exact hx
    obtain ⟨z, rfl⟩ := hr
    exact ⟨H'.isoPullback.inv z, by rw [← Scheme.Hom.comp_apply, H'.isoPullback_inv_fst]⟩
  have hflat : Flat π := by
    refine MorphismProperty.of_isPullback H.flip ?_
    refine (HasRingHomProperty.Spec_iff (P := @Flat)).2 ?_
    exact GlobalTheory.GeomIrr.flat_of_field _
  have : IsReduced X' := by
    have (x' : X') : _root_.IsReduced (X'.presheaf.stalk x') := by
      obtain ⟨A, _, _, _, j, _, q, hq, hj⟩ := chart (π x')
      obtain ⟨j₀, _, z, rfl⟩ := lift j hj x' ⟨q, hq⟩
      have := isDomain_tensor k (Fin N) A
      exact isReduced_of_injective
        (asIso (j₀.stalkMap z)).commRingCatIsoToRingEquiv.toRingHom
        (asIso (j₀.stalkMap z)).commRingCatIsoToRingEquiv.injective
    exact isReduced_of_isReduced_stalk X'
  have : IrreducibleSpace X' := by
    obtain ⟨A, _, _, _, j, _, q, hq, hj⟩ := chart (genericPoint X)
    obtain ⟨j₀, hj₀, H'⟩ := exists_affine_chart_of_isPullback H j hj
    have := isDomain_tensor k (Fin N) A
    have hirr : IsIrreducible (Set.range j₀) := by
      rw [← Set.image_univ]
      exact (IrreducibleSpace.isIrreducible_univ _).image _ j₀.continuous.continuousOn
    have hdense : closure (Set.range j₀) = Set.univ := by
      refine Set.eq_univ_of_forall fun x' => ?_
      obtain ⟨y, hy, e⟩ := Flat.generalizingMap π (genericPoint_specializes (π x'))
      have hr : y ∈ Set.range (Limits.pullback.fst π j) := by
        rw [Scheme.Pullback.range_fst, Set.mem_preimage, e]; exact ⟨q, hq⟩
      obtain ⟨z, hz⟩ := hr
      have hy' : y ∈ Set.range j₀ :=
        ⟨H'.isoPullback.inv z, by rw [← Scheme.Hom.comp_apply, H'.isoPullback_inv_fst, hz]⟩
      exact closure_mono (Set.singleton_subset_iff.2 hy') (specializes_iff_mem_closure.1 hy)
    refine (irreducibleSpace_def X').2 ?_
    rw [Set.top_eq_univ, ← hdense]
    exact hirr.closure
  exact isIntegral_of_irreducibleSpace_of_isReduced X'

end GlobalTheory.PureTransc
