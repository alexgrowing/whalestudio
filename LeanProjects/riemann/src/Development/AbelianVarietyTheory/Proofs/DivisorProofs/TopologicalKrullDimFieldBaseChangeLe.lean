import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpanFinrankMaximalIdealLeNcardOfLeSupSq
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic
open GlobalTheory.ThickeningDetermines (secIdeal)
open scoped TensorProduct

namespace GlobalTheory.FieldExtDim

theorem ringKrullDim_le_of_isIntegral (R S : Type) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.IsIntegral R S] : ringKrullDim S ≤ ringKrullDim R :=
  Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap R S))
    fun I J h => Ideal.IsIntegral.comap_lt_comap (I := I.asIdeal) (J := J.asIdeal) h

theorem ringKrullDim_tensor_le (k K A : Type) [Field k] [Field K] [Algebra k K] [CommRing A]
    [Algebra k A] [Algebra.FiniteType k A] : ringKrullDim (K ⊗[k] A) ≤ ringKrullDim A := by
  rcases subsingleton_or_nontrivial A with hA | hA
  · have : Subsingleton (K ⊗[k] A) := by
      refine ⟨fun x y => ?_⟩
      have h0 : (1 : K ⊗[k] A) = 0 := by
        rw [Algebra.TensorProduct.one_def, Subsingleton.elim (1 : A) 0, TensorProduct.tmul_zero]
      rw [← mul_one x, ← mul_one y, h0, mul_zero, mul_zero]
    rw [ringKrullDim_eq_bot_of_subsingleton]
    exact bot_le
  obtain ⟨s, g, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg k A
  let P := MvPolynomial (Fin s) k
  letI : Algebra P A := g.toRingHom.toAlgebra
  have hiA : Algebra.IsIntegral P A := ⟨hfin.to_isIntegral⟩
  have : FaithfulSMul P A := (faithfulSMul_iff_algebraMap_injective P A).2 hinj
  have hdA : ringKrullDim A = s := by
    rw [GlobalTheory.ringKrullDim_eq_of_isIntegral P A, MvPolynomial.ringKrullDim_of_isNoetherianRing,
      ringKrullDim_eq_zero_of_field, zero_add, Nat.card_eq_fintype_card, Fintype.card_fin]
  let B := K ⊗[k] P
  have hdB : ringKrullDim B = s := by
    rw [ringKrullDim_eq_of_ringEquiv (MvPolynomial.scalarRTensorAlgEquiv (R := k) (N := K)
      (σ := Fin s)).toRingEquiv, MvPolynomial.ringKrullDim_of_isNoetherianRing,
      ringKrullDim_eq_zero_of_field, zero_add, Nat.card_eq_fintype_card, Fintype.card_fin]
  let φ : B →ₐ[K] K ⊗[k] A := Algebra.TensorProduct.map (AlgHom.id K K) g
  letI : Algebra B (K ⊗[k] A) := φ.toRingHom.toAlgebra
  have hcomp : (algebraMap B (K ⊗[k] A)).comp
      (Algebra.TensorProduct.includeRight : P →ₐ[k] B).toRingHom =
      (Algebra.TensorProduct.includeRight : A →ₐ[k] K ⊗[k] A).toRingHom.comp (algebraMap P A) := by
    refine RingHom.ext fun p => ?_
    change φ ((1 : K) ⊗ₜ[k] p) = (1 : K) ⊗ₜ[k] g p
    rw [Algebra.TensorProduct.map_tmul]
    rfl
  have hint : Algebra.IsIntegral B (K ⊗[k] A) := ⟨fun x => by
    induction x using TensorProduct.induction_on with
    | zero => exact isIntegral_zero
    | tmul c a =>
      have h1 : IsIntegral B ((Algebra.TensorProduct.includeRight : A →ₐ[k] K ⊗[k] A) a) :=
        IsIntegral.map_of_comp_eq _ _ hcomp (Algebra.IsIntegral.isIntegral a)
      have h2 : IsIntegral B (algebraMap B (K ⊗[k] A) (c ⊗ₜ 1)) := isIntegral_algebraMap
      have he : c ⊗ₜ[k] a = algebraMap B (K ⊗[k] A) (c ⊗ₜ 1) *
          (Algebra.TensorProduct.includeRight : A →ₐ[k] K ⊗[k] A) a := by
        change c ⊗ₜ[k] a = φ (c ⊗ₜ[k] (1 : P)) * ((1 : K) ⊗ₜ[k] a)
        rw [Algebra.TensorProduct.map_tmul, map_one, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
          one_mul]
        rfl
      rw [he]
      exact h2.mul h1
    | add x y hx hy => exact hx.add hy⟩
  calc ringKrullDim (K ⊗[k] A) ≤ ringKrullDim B := ringKrullDim_le_of_isIntegral B _
    _ = ringKrullDim A := hdB.trans hdA.symm

theorem topologicalKrullDim_baseChange_le :
    ∀ (k K : Type) [Field k] [Field K] [Algebra k K] (X X' : Scheme.{0}) (f : X ⟶ Sp k)
      [LocallyOfFiniteType f] (f' : X' ⟶ Sp K) (π : X' ⟶ X),
      IsPullback π f' f (spMap (algebraMap k K)) → topologicalKrullDim X' ≤ topologicalKrullDim X := by
  intro k K _ _ _ X X' f _ f' π H
  refine topologicalKrullDim_le_of_forall_exists_isOpen fun x' => ?_
  obtain ⟨A, _, _, j, _, q, hq, hj⟩ := exists_affine_chart_over f (π x')
  obtain ⟨j₀, _, H₀⟩ := exists_affine_chart_of_isPullback H j hj
  have hft : Algebra.FiniteType k A := by
    have : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap k A))) := by
      rw [← hj]; infer_instance
    exact RingHom.finiteType_algebraMap.mp
      ((HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp this)
  have hs : Function.Surjective H₀.isoPullback.hom := H₀.isoPullback.hom.homeomorph.surjective
  have hrange : Set.range j₀ = π ⁻¹' Set.range j := by
    rw [← H₀.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      hs.range_eq, Set.image_univ, Scheme.Pullback.range_fst]
  refine ⟨Set.range j₀, j₀.isOpenEmbedding.isOpen_range, hrange ▸ ⟨q, hq⟩, ?_⟩
  rw [topologicalKrullDim_eq_of_isEmbedding j₀.isOpenEmbedding.isEmbedding rfl]
  calc topologicalKrullDim (Spec (.of (K ⊗[k] A))) = ringKrullDim (K ⊗[k] A) :=
        PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _
    _ ≤ ringKrullDim A := ringKrullDim_tensor_le k K A
    _ = topologicalKrullDim (Set.range j) :=
        ((topologicalKrullDim_eq_of_isEmbedding j.isOpenEmbedding.isEmbedding rfl).trans
          (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim A)).symm
    _ ≤ topologicalKrullDim X := topologicalKrullDim_subspace_le _ _

end GlobalTheory.FieldExtDim
