import Mathlib

universe u

namespace FunctorialResolution.EmbeddedResolution

variable {R : Type u} [CommRing R] {σ τ : Type u}

noncomputable section

def GraphAlgebra (_f : τ → MvPolynomial σ R) : Type u := MvPolynomial σ R

instance instCommRingGraphAlgebra (f : τ → MvPolynomial σ R) : CommRing (GraphAlgebra f) :=
  inferInstanceAs (CommRing (MvPolynomial σ R))

instance instAlgebraGraphAlgebra (f : τ → MvPolynomial σ R) : Algebra R (GraphAlgebra f) :=
  inferInstanceAs (Algebra R (MvPolynomial σ R))

def graphAlgebraEquiv (f : τ → MvPolynomial σ R) : MvPolynomial σ R ≃ₐ[R] GraphAlgebra f :=
  AlgEquiv.refl

def aevalGraphAlgebra (f : τ → MvPolynomial σ R) : MvPolynomial τ R →ₐ[R] GraphAlgebra f :=
  (graphAlgebraEquiv f).toAlgHom.comp (MvPolynomial.aeval f)

instance instAlgebraBaseGraphAlgebra (f : τ → MvPolynomial σ R) :
    Algebra (MvPolynomial τ R) (GraphAlgebra f) :=
  (aevalGraphAlgebra f).toRingHom.toAlgebra

theorem algebraMap_graphAlgebra (f : τ → MvPolynomial σ R) (p : MvPolynomial τ R) :
    algebraMap (MvPolynomial τ R) (GraphAlgebra f) p = graphAlgebraEquiv f (MvPolynomial.aeval f p) :=
  rfl

private theorem algebraMap_graphAlgebra_eq_algebraMap_mvPolynomial (f : τ → MvPolynomial σ R) (r : R) :
    algebraMap R (GraphAlgebra f) r
      = algebraMap (MvPolynomial τ R) (GraphAlgebra f) (algebraMap R (MvPolynomial τ R) r) := by
  rw [algebraMap_graphAlgebra, AlgHom.commutes, AlgEquiv.commutes]

instance instIsScalarTowerGraphAlgebra (f : τ → MvPolynomial σ R) :
    IsScalarTower R (MvPolynomial τ R) (GraphAlgebra f) :=
  IsScalarTower.of_algebraMap_eq (algebraMap_graphAlgebra_eq_algebraMap_mvPolynomial f)

def graphRelation (f : τ → MvPolynomial σ R) (i : τ) : MvPolynomial σ (MvPolynomial τ R) :=
  MvPolynomial.C (MvPolynomial.X i)
    - MvPolynomial.map (MvPolynomial.C : R →+* MvPolynomial τ R) (f i)

abbrev graphRelationIdeal (f : τ → MvPolynomial σ R) : Ideal (MvPolynomial σ (MvPolynomial τ R)) :=
  Ideal.span (Set.range (graphRelation f))

def graphAlgebraAeval (f : τ → MvPolynomial σ R) :
    MvPolynomial σ (MvPolynomial τ R) →ₐ[MvPolynomial τ R] GraphAlgebra f :=
  MvPolynomial.aeval (fun i : σ => graphAlgebraEquiv f (MvPolynomial.X i))

theorem graphAlgebraAeval_X (f : τ → MvPolynomial σ R) (i : σ) :
    graphAlgebraAeval f (MvPolynomial.X i) = graphAlgebraEquiv f (MvPolynomial.X i) :=
  MvPolynomial.aeval_X _ i

private theorem graphAlgebraAeval_C (f : τ → MvPolynomial σ R) (a : MvPolynomial τ R) :
    graphAlgebraAeval f (MvPolynomial.C a) = graphAlgebraEquiv f (MvPolynomial.aeval f a) := by
  have h : graphAlgebraAeval f (MvPolynomial.C a)
      = algebraMap (MvPolynomial τ R) (GraphAlgebra f) a := by
    simp [graphAlgebraAeval]
  rw [h, algebraMap_graphAlgebra]

private theorem graphAlgebraAeval_map_C (f : τ → MvPolynomial σ R) (p : MvPolynomial σ R) :
    graphAlgebraAeval f (MvPolynomial.map (MvPolynomial.C : R →+* MvPolynomial τ R) p)
      = graphAlgebraEquiv f p := by
  induction p using MvPolynomial.induction_on with
  | C r =>
      simp only [MvPolynomial.map_C, graphAlgebraAeval_C, MvPolynomial.aeval_C,
        MvPolynomial.algebraMap_eq]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp => simp only [map_mul, MvPolynomial.map_X, hp, graphAlgebraAeval_X]

theorem graphAlgebraAeval_graphRelation (f : τ → MvPolynomial σ R) (i : τ) :
    graphAlgebraAeval f (graphRelation f i) = 0 := by
  simp only [graphRelation, map_sub, graphAlgebraAeval_C, graphAlgebraAeval_map_C, MvPolynomial.aeval_X, sub_self]

private theorem graphAlgebraAeval_map_C_graphAlgebraEquiv_symm (f : τ → MvPolynomial σ R) (x : GraphAlgebra f) :
    graphAlgebraAeval f (MvPolynomial.map (MvPolynomial.C : R →+* MvPolynomial τ R)
      ((graphAlgebraEquiv f).symm x)) = x := by
  rw [graphAlgebraAeval_map_C, AlgEquiv.apply_symm_apply]

private def graphSubstitutionHom (f : τ → MvPolynomial σ R) :
    MvPolynomial σ (MvPolynomial τ R) →+* MvPolynomial σ R :=
  MvPolynomial.eval₂Hom
    ((MvPolynomial.aeval f : MvPolynomial τ R →ₐ[R] MvPolynomial σ R).toRingHom)
    MvPolynomial.X

private theorem graphSubstitutionHom_C (f : τ → MvPolynomial σ R) (a : MvPolynomial τ R) :
    graphSubstitutionHom f (MvPolynomial.C a) = MvPolynomial.aeval f a := by
  simp [graphSubstitutionHom]

private theorem graphSubstitutionHom_X (f : τ → MvPolynomial σ R) (i : σ) :
    graphSubstitutionHom f (MvPolynomial.X i) = MvPolynomial.X i := by
  simp [graphSubstitutionHom]

private theorem graphAlgebraAeval_eq_graphAlgebraEquiv_graphSubstitutionHom (f : τ → MvPolynomial σ R)
    (p : MvPolynomial σ (MvPolynomial τ R)) :
    graphAlgebraAeval f p = graphAlgebraEquiv f (graphSubstitutionHom f p) := by
  induction p using MvPolynomial.induction_on with
  | C a => rw [graphAlgebraAeval_C, graphSubstitutionHom_C]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X q i hq => simp only [map_mul, hq, graphAlgebraAeval_X, graphSubstitutionHom_X]

private theorem C_sub_map_C_aeval_mem_graphRelationIdeal (f : τ → MvPolynomial σ R) (a : MvPolynomial τ R) :
    MvPolynomial.C a - MvPolynomial.map (MvPolynomial.C : R →+* MvPolynomial τ R)
      (MvPolynomial.aeval f a) ∈ graphRelationIdeal f := by
  induction a using MvPolynomial.induction_on with
  | C r =>
      have key : (MvPolynomial.C (MvPolynomial.C r : MvPolynomial τ R) :
            MvPolynomial σ (MvPolynomial τ R))
          - MvPolynomial.map (MvPolynomial.C : R →+* MvPolynomial τ R)
            (MvPolynomial.aeval f (MvPolynomial.C r : MvPolynomial τ R)) = 0 := by
        simp [MvPolynomial.algebraMap_eq]
      rw [key]
      exact Ideal.zero_mem _
  | add p q hp hq =>
      have key : (MvPolynomial.C (p + q) : MvPolynomial σ (MvPolynomial τ R))
          - MvPolynomial.map (MvPolynomial.C : R →+* MvPolynomial τ R)
            (MvPolynomial.aeval f (p + q))
          = (MvPolynomial.C p - MvPolynomial.map (MvPolynomial.C : R →+* MvPolynomial τ R)
              (MvPolynomial.aeval f p))
            + (MvPolynomial.C q - MvPolynomial.map (MvPolynomial.C : R →+* MvPolynomial τ R)
              (MvPolynomial.aeval f q)) := by
        simp only [map_add]
        ring
      rw [key]
      exact Ideal.add_mem _ hp hq
  | mul_X p j hp =>
      have hrel : graphRelation f j ∈ graphRelationIdeal f := Ideal.subset_span ⟨j, rfl⟩
      have key : (MvPolynomial.C (p * MvPolynomial.X j) : MvPolynomial σ (MvPolynomial τ R))
          - MvPolynomial.map (MvPolynomial.C : R →+* MvPolynomial τ R)
            (MvPolynomial.aeval f (p * MvPolynomial.X j))
          = MvPolynomial.C p * graphRelation f j
            + (MvPolynomial.C p - MvPolynomial.map (MvPolynomial.C : R →+* MvPolynomial τ R)
                (MvPolynomial.aeval f p))
              * MvPolynomial.map (MvPolynomial.C : R →+* MvPolynomial τ R) (f j) := by
        simp only [graphRelation, map_mul, MvPolynomial.aeval_X]
        ring
      rw [key]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hrel) (Ideal.mul_mem_right _ _ hp)

private theorem sub_map_C_mem_graphRelationIdeal (f : τ → MvPolynomial σ R)
    (p : MvPolynomial σ (MvPolynomial τ R)) :
    p - MvPolynomial.map (MvPolynomial.C : R →+* MvPolynomial τ R) (graphSubstitutionHom f p)
      ∈ graphRelationIdeal f := by
  induction p using MvPolynomial.induction_on with
  | C a =>
      rw [graphSubstitutionHom_C]
      exact C_sub_map_C_aeval_mem_graphRelationIdeal f a
  | add p q hp hq =>
      have key : p + q
          - MvPolynomial.map (MvPolynomial.C : R →+* MvPolynomial τ R) (graphSubstitutionHom f (p + q))
          = (p - MvPolynomial.map (MvPolynomial.C : R →+* MvPolynomial τ R) (graphSubstitutionHom f p))
            + (q - MvPolynomial.map (MvPolynomial.C : R →+* MvPolynomial τ R)
                (graphSubstitutionHom f q)) := by
        simp only [map_add]
        ring
      rw [key]
      exact Ideal.add_mem _ hp hq
  | mul_X q i hq =>
      have key : q * MvPolynomial.X i
          - MvPolynomial.map (MvPolynomial.C : R →+* MvPolynomial τ R)
              (graphSubstitutionHom f (q * MvPolynomial.X i))
          = (q - MvPolynomial.map (MvPolynomial.C : R →+* MvPolynomial τ R) (graphSubstitutionHom f q))
            * MvPolynomial.X i := by
        simp only [map_mul, graphSubstitutionHom_X, MvPolynomial.map_X]
        ring
      rw [key]
      exact Ideal.mul_mem_right _ _ hq

def graphAlgebraGenerators (f : τ → MvPolynomial σ R) :
    Algebra.Generators (MvPolynomial τ R) (GraphAlgebra f) σ where
  val := fun i => graphAlgebraEquiv f (MvPolynomial.X i)
  σ' := fun x =>
    MvPolynomial.map (MvPolynomial.C : R →+* MvPolynomial τ R) ((graphAlgebraEquiv f).symm x)
  aeval_val_σ' := graphAlgebraAeval_map_C_graphAlgebraEquiv_symm f

private theorem mem_ker_graphAlgebraGenerators_iff (f : τ → MvPolynomial σ R)
    (p : MvPolynomial σ (MvPolynomial τ R)) :
    p ∈ (graphAlgebraGenerators f).ker ↔ graphAlgebraAeval f p = 0 := Iff.rfl

private theorem span_range_graphRelation_eq_ker (f : τ → MvPolynomial σ R) :
    Ideal.span (Set.range (graphRelation f)) = (graphAlgebraGenerators f).ker := by
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro x ⟨i, rfl⟩
    simp only [SetLike.mem_coe]
    exact (mem_ker_graphAlgebraGenerators_iff f _).2 (graphAlgebraAeval_graphRelation f i)
  · intro p hp
    have hp' : graphAlgebraAeval f p = 0 := (mem_ker_graphAlgebraGenerators_iff f p).1 hp
    have h0 : graphSubstitutionHom f p = 0 := by
      have h1 := graphAlgebraAeval_eq_graphAlgebraEquiv_graphSubstitutionHom f p
      rw [hp'] at h1
      have h2 : graphAlgebraEquiv f (graphSubstitutionHom f p) = graphAlgebraEquiv f 0 := by
        rw [← h1, map_zero]
      exact (graphAlgebraEquiv f).injective h2
    have hmem := sub_map_C_mem_graphRelationIdeal f p
    rwa [h0, map_zero, sub_zero] at hmem

def graphPresentation (f : τ → MvPolynomial σ R) :
    Algebra.Presentation (MvPolynomial τ R) (GraphAlgebra f) σ τ where
  toGenerators := graphAlgebraGenerators f
  relation := graphRelation f
  span_range_relation_eq_ker := span_range_graphRelation_eq_ker f

def graphPreSubmersivePresentation (f : τ → MvPolynomial σ R) (v : τ → σ)
    (hv : Function.Injective v) :
    Algebra.PreSubmersivePresentation (MvPolynomial τ R) (GraphAlgebra f) σ τ where
  toPresentation := graphPresentation f
  map := v
  map_inj := hv

@[simp] theorem graphPreSubmersivePresentation_relation (f : τ → MvPolynomial σ R) (v : τ → σ)
    (hv : Function.Injective v) :
    (graphPreSubmersivePresentation f v hv).relation = graphRelation f :=
  rfl

@[simp] theorem graphPreSubmersivePresentation_map (f : τ → MvPolynomial σ R) (v : τ → σ)
    (hv : Function.Injective v) :
    (graphPreSubmersivePresentation f v hv).map = v :=
  rfl

def graphJacobianMinorMatrix (f : τ → MvPolynomial σ R) (v : τ → σ) : Matrix τ τ (MvPolynomial σ R) :=
  Matrix.of fun i j => MvPolynomial.pderiv (v i) (f j)

theorem graphJacobianMinorMatrix_apply (f : τ → MvPolynomial σ R) (v : τ → σ) (i j : τ) :
    graphJacobianMinorMatrix f v i j = MvPolynomial.pderiv (v i) (f j) :=
  rfl

theorem graphPreSubmersivePresentation_jacobiMatrix [Fintype τ] [DecidableEq τ]
    (f : τ → MvPolynomial σ R) (v : τ → σ) (hv : Function.Injective v) :
    (graphPreSubmersivePresentation f v hv).jacobiMatrix
      = -((graphJacobianMinorMatrix f v).map
          (fun p => MvPolynomial.map (MvPolynomial.C : R →+* MvPolynomial τ R) p)) := by
  ext i j
  rw [Algebra.PreSubmersivePresentation.jacobiMatrix_apply]
  simp only [graphPreSubmersivePresentation_relation, graphPreSubmersivePresentation_map,
    graphRelation, map_sub, MvPolynomial.pderiv_C, MvPolynomial.pderiv_map, zero_sub,
    Matrix.neg_apply, Matrix.map_apply, graphJacobianMinorMatrix_apply]

theorem graphPreSubmersivePresentation_jacobian [Fintype τ] [DecidableEq τ]
    (f : τ → MvPolynomial σ R) (v : τ → σ) (hv : Function.Injective v) :
    (graphPreSubmersivePresentation f v hv).jacobian
      = (-1 : GraphAlgebra f) ^ Fintype.card τ * graphAlgebraEquiv f (graphJacobianMinorMatrix f v).det := by
  have hmap : ((graphJacobianMinorMatrix f v).map
      (fun p => MvPolynomial.map (MvPolynomial.C : R →+* MvPolynomial τ R) p)).det
      = MvPolynomial.map (MvPolynomial.C : R →+* MvPolynomial τ R) (graphJacobianMinorMatrix f v).det :=
    (RingHom.map_det (MvPolynomial.map (MvPolynomial.C : R →+* MvPolynomial τ R))
      (graphJacobianMinorMatrix f v)).symm
  rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det,
    graphPreSubmersivePresentation_jacobiMatrix, Matrix.det_neg, hmap, map_mul, map_pow,
    map_neg, map_one]
  congr 1
  exact graphAlgebraAeval_map_C f _

end

end FunctorialResolution.EmbeddedResolution
