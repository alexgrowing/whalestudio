import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleCoordinates
namespace FunctorialResolution.EmbeddedResolution
namespace EtaleCoordinates

open MvPolynomial

section

variable (k : Type*) [CommRing k] (ι κ : Type*)

noncomputable def sumEvalIter :
    MvPolynomial (ι ⊕ κ) k →ₐ[k] MvPolynomial κ (MvPolynomial ι k) :=
  aeval (Sum.elim (fun i : ι => (C (X i) : MvPolynomial κ (MvPolynomial ι k)))
    (fun j : κ => (X j : MvPolynomial κ (MvPolynomial ι k))))

@[reducible] noncomputable def sumEvalIterAlgebra :
    Algebra (MvPolynomial (ι ⊕ κ) k) (MvPolynomial κ (MvPolynomial ι k)) :=
  (sumEvalIter k ι κ).toRingHom.toAlgebra

end

section

variable (k : Type*) [CommRing k] (ι κ : Type*)

private noncomputable def iterToSumRingHom :
    MvPolynomial κ (MvPolynomial ι k) →+* MvPolynomial (ι ⊕ κ) k :=
  eval₂Hom (eval₂Hom (C : k →+* MvPolynomial (ι ⊕ κ) k)
      (fun i : ι => (X (Sum.inl i) : MvPolynomial (ι ⊕ κ) k)))
    (fun j : κ => (X (Sum.inr j) : MvPolynomial (ι ⊕ κ) k))

private theorem iterToSumHom_C_C (a : k) :
    iterToSumRingHom k ι κ (C (C a)) = C a := by
  simp [iterToSumRingHom]

private theorem iterToSumHom_C_X (i : ι) :
    iterToSumRingHom k ι κ (C (X i)) = X (Sum.inl i) := by
  simp [iterToSumRingHom]

private theorem iterToSumHom_X (j : κ) :
    iterToSumRingHom k ι κ (X j) = X (Sum.inr j) := by
  simp [iterToSumRingHom]

private theorem sumEvalIter_C (a : k) :
    sumEvalIter k ι κ (C a) = C (C a) := by
  simp only [sumEvalIter, MvPolynomial.aeval_C]
  rfl

private theorem sumEvalIter_X_inl (i : ι) :
    sumEvalIter k ι κ (X (Sum.inl i)) = C (X i) := by
  simp [sumEvalIter]

private theorem sumEvalIter_X_inr (j : κ) :
    sumEvalIter k ι κ (X (Sum.inr j)) = X j := by
  simp [sumEvalIter]

private theorem iterToSumHom_sumEvalIter (p : MvPolynomial (ι ⊕ κ) k) :
    iterToSumRingHom k ι κ (sumEvalIter k ι κ p) = p := by
  induction p using MvPolynomial.induction_on
  next a => rw [sumEvalIter_C, iterToSumHom_C_C]
  next q r hq hr => simp only [map_add, hq, hr]
  next q v hq =>
    rcases v with i | j
    · simp only [map_mul, hq, sumEvalIter_X_inl, iterToSumHom_C_X]
    · simp only [map_mul, hq, sumEvalIter_X_inr, iterToSumHom_X]

private theorem sumEvalIter_iterToSumHom_C (r : MvPolynomial ι k) :
    sumEvalIter k ι κ (iterToSumRingHom k ι κ (C r)) = C r := by
  induction r using MvPolynomial.induction_on
  next a => rw [iterToSumHom_C_C, sumEvalIter_C]
  next p q hp hq => simp only [map_add, hp, hq]
  next p i hp => simp only [map_mul, hp, iterToSumHom_C_X, sumEvalIter_X_inl]

private theorem sumEvalIter_iterToSumHom (q : MvPolynomial κ (MvPolynomial ι k)) :
    sumEvalIter k ι κ (iterToSumRingHom k ι κ q) = q := by
  induction q using MvPolynomial.induction_on
  next r => exact sumEvalIter_iterToSumHom_C k ι κ r
  next p p' hp hp' => simp only [map_add, hp, hp']
  next p j hp => simp only [map_mul, hp, iterToSumHom_X, sumEvalIter_X_inr]

private theorem bijective_sumEvalIter :
    Function.Bijective (sumEvalIter k ι κ) := by
  constructor
  · exact Function.LeftInverse.injective (iterToSumHom_sumEvalIter k ι κ)
  · exact fun q => ⟨iterToSumRingHom k ι κ q, sumEvalIter_iterToSumHom k ι κ q⟩

attribute [local instance] sumEvalIterAlgebra

private theorem formallyEtale_sumEvalIter :
    Algebra.FormallyEtale (MvPolynomial (ι ⊕ κ) k) (MvPolynomial κ (MvPolynomial ι k)) := by
  have hb : Function.Bijective
      (algebraMap (MvPolynomial (ι ⊕ κ) k) (MvPolynomial κ (MvPolynomial ι k))) :=
    bijective_sumEvalIter k ι κ
  exact Algebra.FormallyEtale.of_equiv
    (AlgEquiv.ofBijective
      (Algebra.ofId (MvPolynomial (ι ⊕ κ) k) (MvPolynomial κ (MvPolynomial ι k))) hb)

end

section

variable (k : Type*) [CommRing k] (ι κ : Type*) (S : Type*) [CommRing S]
  [Algebra (MvPolynomial ι k) S]

@[reducible] noncomputable def mapCoeffAlgebra :
    Algebra (MvPolynomial κ (MvPolynomial ι k)) (MvPolynomial κ S) :=
  (MvPolynomial.map (algebraMap (MvPolynomial ι k) S)).toAlgebra

attribute [local instance] mapCoeffAlgebra

theorem algebraMap_eq_mvPolynomial_map (p : MvPolynomial κ (MvPolynomial ι k)) :
    algebraMap (MvPolynomial κ (MvPolynomial ι k)) (MvPolynomial κ S) p
      = MvPolynomial.map (algebraMap (MvPolynomial ι k) S) p := rfl

end

section

universe u v

private theorem formallyEtale_mvPolynomial_map (R : Type u) [CommRing R] (A : Type v) [CommRing A]
    [Algebra R A] [Algebra.FormallyEtale R A] (σ : Type*) :
    @Algebra.FormallyEtale (MvPolynomial σ R) (MvPolynomial σ A) _ _
      (RingHom.toAlgebra (MvPolynomial.map (algebraMap R A))) := by
  let : Algebra (MvPolynomial σ R) (MvPolynomial σ A) :=
    RingHom.toAlgebra (MvPolynomial.map (algebraMap R A))
  have : Algebra.FormallyEtale (MvPolynomial σ R)
      (TensorProduct R (MvPolynomial σ R) A) := inferInstance
  have e : TensorProduct R (MvPolynomial σ R) A ≃ₐ[MvPolynomial σ R] MvPolynomial σ A :=
    AlgEquiv.ofRingEquiv
      (f := (Algebra.TensorProduct.comm R (MvPolynomial σ R) A).toRingEquiv.trans
        (MvPolynomial.algebraTensorAlgEquiv R A).toRingEquiv)
      (fun p => by
        have hp : algebraMap (MvPolynomial σ R) (TensorProduct R (MvPolynomial σ R) A) p
            = p ⊗ₜ[R] (1 : A) := rfl
        have hq : algebraMap (MvPolynomial σ R) (MvPolynomial σ A) p
            = MvPolynomial.map (algebraMap R A) p := rfl
        rw [hp, hq]
        simp)
  exact Algebra.FormallyEtale.of_equiv e

end

section

variable (k : Type*) [CommRing k] (ι κ : Type*) (S : Type*) [CommRing S]
  [Algebra (MvPolynomial ι k) S] [Algebra k S]

noncomputable def sumEval : MvPolynomial (ι ⊕ κ) k →ₐ[k] MvPolynomial κ S :=
  aeval (Sum.elim (fun i : ι => (C (coord k ι S i) : MvPolynomial κ S))
    (fun j : κ => (X j : MvPolynomial κ S)))

@[reducible] noncomputable def sumEvalAlgebra :
    Algebra (MvPolynomial (ι ⊕ κ) k) (MvPolynomial κ S) :=
  (sumEval k ι κ S).toRingHom.toAlgebra

attribute [local instance] sumEvalAlgebra
attribute [local instance] sumEvalIterAlgebra
attribute [local instance] mapCoeffAlgebra

theorem sumEvalAlgebra_isScalarTower :
    IsScalarTower k (MvPolynomial (ι ⊕ κ) k) (MvPolynomial κ S) :=
  IsScalarTower.of_algebraMap_eq fun x => ((sumEval k ι κ S).commutes x).symm

theorem algebraMap_eq_sumEval (p : MvPolynomial (ι ⊕ κ) k) :
    algebraMap (MvPolynomial (ι ⊕ κ) k) (MvPolynomial κ S) p = sumEval k ι κ S p := rfl

@[simp] theorem algebraMap_X_inl (i : ι) :
    algebraMap (MvPolynomial (ι ⊕ κ) k) (MvPolynomial κ S) (X (Sum.inl i))
      = C (coord k ι S i) := by
  simp [algebraMap_eq_sumEval, sumEval]

@[simp] theorem algebraMap_X_inr (j : κ) :
    algebraMap (MvPolynomial (ι ⊕ κ) k) (MvPolynomial κ S) (X (Sum.inr j))
      = (X j : MvPolynomial κ S) := by
  simp [algebraMap_eq_sumEval, sumEval]

@[simp] theorem coord_inl (i : ι) :
    coord k (ι ⊕ κ) (MvPolynomial κ S) (Sum.inl i) = C (coord k ι S i) :=
  (coord_def k (ι ⊕ κ) (MvPolynomial κ S) (Sum.inl i)).trans (algebraMap_X_inl k ι κ S i)

@[simp] theorem coord_inr (j : κ) :
    coord k (ι ⊕ κ) (MvPolynomial κ S) (Sum.inr j) = (X j : MvPolynomial κ S) :=
  (coord_def k (ι ⊕ κ) (MvPolynomial κ S) (Sum.inr j)).trans (algebraMap_X_inr k ι κ S j)

private theorem algebraMap_eq_sumEvalIter (p : MvPolynomial (ι ⊕ κ) k) :
    algebraMap (MvPolynomial (ι ⊕ κ) k) (MvPolynomial κ (MvPolynomial ι k)) p
      = sumEvalIter k ι κ p := rfl

theorem mapCoeffAlgebra_isScalarTower_of_isScalarTower [IsScalarTower k (MvPolynomial ι k) S] :
    IsScalarTower k (MvPolynomial κ (MvPolynomial ι k)) (MvPolynomial κ S) :=
  IsScalarTower.of_algebraMap_eq fun x => by
    have h1 : algebraMap k (MvPolynomial κ (MvPolynomial ι k)) x
        = C (algebraMap k (MvPolynomial ι k) x) := rfl
    have h2 : algebraMap k (MvPolynomial κ S) x = C (algebraMap k S x) := rfl
    rw [h2, h1, algebraMap_eq_mvPolynomial_map, MvPolynomial.map_C,
      IsScalarTower.algebraMap_apply k (MvPolynomial ι k) S]

theorem mapCoeffAlgebra_isScalarTower [IsScalarTower k (MvPolynomial ι k) S] :
    IsScalarTower (MvPolynomial (ι ⊕ κ) k) (MvPolynomial κ (MvPolynomial ι k))
      (MvPolynomial κ S) := by
  have := mapCoeffAlgebra_isScalarTower_of_isScalarTower k ι κ S
  refine IsScalarTower.of_algebraMap_eq' ?_
  refine MvPolynomial.ringHom_ext (fun r => ?_) (fun v => ?_)
  · simp only [algebraMap_eq_sumEval, RingHom.comp_apply, algebraMap_eq_sumEvalIter,
      sumEval, sumEvalIter, MvPolynomial.aeval_C]
    exact IsScalarTower.algebraMap_apply k (MvPolynomial κ (MvPolynomial ι k)) (MvPolynomial κ S) r
  · rcases v with i | j <;>
      simp [RingHom.comp_apply, algebraMap_eq_sumEval, algebraMap_eq_sumEvalIter,
        sumEval, sumEvalIter, algebraMap_eq_mvPolynomial_map, coord_def]

theorem formallyEtale_mvPolynomial_sum [IsScalarTower k (MvPolynomial ι k) S]
    [Algebra.FormallyEtale (MvPolynomial ι k) S] :
    Algebra.FormallyEtale (MvPolynomial (ι ⊕ κ) k) (MvPolynomial κ S) := by
  have := mapCoeffAlgebra_isScalarTower_of_isScalarTower k ι κ S
  have := mapCoeffAlgebra_isScalarTower k ι κ S
  have h1 : Algebra.FormallyEtale (MvPolynomial (ι ⊕ κ) k)
      (MvPolynomial κ (MvPolynomial ι k)) := formallyEtale_sumEvalIter k ι κ
  have h2 : Algebra.FormallyEtale (MvPolynomial κ (MvPolynomial ι k)) (MvPolynomial κ S) :=
    formallyEtale_mvPolynomial_map (MvPolynomial ι k) S κ
  exact Algebra.FormallyEtale.comp (MvPolynomial (ι ⊕ κ) k) (MvPolynomial κ (MvPolynomial ι k))
    (MvPolynomial κ S)

variable (T : Type*) [CommRing T]

theorem formallyEtale_trans [IsScalarTower k (MvPolynomial ι k) S]
    [Algebra (MvPolynomial κ S) T] [Algebra (MvPolynomial (ι ⊕ κ) k) T]
    [IsScalarTower (MvPolynomial (ι ⊕ κ) k) (MvPolynomial κ S) T]
    [Algebra.FormallyEtale (MvPolynomial ι k) S]
    [Algebra.FormallyEtale (MvPolynomial κ S) T] :
    Algebra.FormallyEtale (MvPolynomial (ι ⊕ κ) k) T := by
  have := formallyEtale_mvPolynomial_sum k ι κ S
  exact Algebra.FormallyEtale.comp (MvPolynomial (ι ⊕ κ) k) (MvPolynomial κ S) T

end

end EtaleCoordinates
end FunctorialResolution.EmbeddedResolution
