import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.HolEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.IsAlgIsoRefl
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualInfinitesimalCharacterRegular
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.InfinitesimalCharacterPullback.HasInfCharPullSub
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

private theorem scalarDecomp {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {N : Type} [AddCommGroup N]
    [Module ℂ N] [Module ℝ N] [IsScalarTower ℝ ℂ N] (l : Cinf E →ₗ[ℝ] N) (x : Cinf E) :
    l x = ∑ τ : E →+* ℂ, coord τ x • ((1 / 2 : ℂ) • (l (atEmb τ 1) - Complex.I • l (atEmb τ Complex.I))) := by
  classical
  have e : x = ∑ w : InfinitePlace E, atEmb w.embedding (x w) := by
    conv_lhs => rw [← Finset.univ_sum_single x]
    refine Finset.sum_congr rfl fun w _ => ?_
    unfold atEmb
    rw [if_pos (by rw [InfinitePlace.mk_embedding])]
    congr 1 <;> simp
  rw [← Finset.sum_fiberwise Finset.univ InfinitePlace.mk]
  conv_lhs => rw [e, map_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  have hne : w.embedding ≠ ComplexEmbedding.conjugate w.embedding := fun h =>
    InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w)
      (InfinitePlace.isReal_iff.2 (ComplexEmbedding.isReal_iff.2 h.symm))
  have hf : (Finset.univ.filter fun τ : E →+* ℂ => InfinitePlace.mk τ = w) =
      {w.embedding, ComplexEmbedding.conjugate w.embedding} := by
    ext τ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro h
      have h' : InfinitePlace.mk w.embedding = InfinitePlace.mk τ := by rw [InfinitePlace.mk_embedding, h]
      exact (InfinitePlace.mk_eq_iff.1 h').imp Eq.symm Eq.symm
    · rintro (rfl | rfl)
      · exact InfinitePlace.mk_embedding w
      · rw [InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding]
  have e' : atEmb w.embedding (-Complex.I) = -atEmb w.embedding Complex.I := by
    rw [atEmb_eq]; simp
  rw [hf, Finset.sum_pair hne, UpperTheory.V.FieldIso.coord_conj, UpperTheory.V.FieldIso.coord_embedding, atEmb_eq _ (x w),
    map_add, map_smul, map_smul, ← algebraMap_smul ℂ (x w).re, ← algebraMap_smul ℂ (x w).im]
  simp only [atEmb_conj, map_one, Complex.conj_I, e', map_neg]
  have h1 : algebraMap ℝ ℂ (x w).re = (x w + starRingEnd ℂ (x w)) / 2 := by
    rw [Complex.add_conj]; simp
  have h2 : algebraMap ℝ ℂ (x w).im = -(x w - starRingEnd ℂ (x w)) * Complex.I / 2 := by
    rw [Complex.sub_conj]; push_cast
    change ((x w).im : ℂ) = _
    linear_combination ((x w).im : ℂ) * Complex.I_mul_I
  rw [h1, h2]
  match_scalars <;> ring

theorem UpperTheory.V.AlgRepEndIrreducible.lieDecomp :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (N : Type) [AddCommGroup N] [Module ℂ N] [Module ℝ N] [IsScalarTower ℝ ℂ N] (L : Lie E a →ₗ[ℝ] N) (X : Matrix (Fin a) (Fin a) (Cinf E)),
      L (toL X) = ∑ τ : E →+* ℂ, hol τ L (X.map (coord τ)) := by
  intro E _ _ _ a N _ _ _ _ L X
  let L' : Matrix (Fin a) (Fin a) (Cinf E) →ₗ[ℝ] N := L
  change L' X = _
  conv_lhs => rw [Matrix.matrix_eq_sum_single X]
  simp only [map_sum, hol_apply, Matrix.map_apply]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact scalarDecomp (L' ∘ₗ Matrix.singleLinearMap ℝ i j) (X i j)
