import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.UnfoldedThetaIntegralConvergesSimilitudeOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.InfinitesimalCharacterPullback.HasInfCharPullSub

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

namespace UpperTheory.ConvolutionTheory.R2.Ff

section SlopeTestRemainingChoices

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E]

private theorem fiber_eq (w : InfinitePlace E) :
    (Finset.univ.filter fun τ : E →+* ℂ => InfinitePlace.mk τ = w) =
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

private theorem emb_ne (w : InfinitePlace E) : w.embedding ≠ ComplexEmbedding.conjugate w.embedding := fun h =>
  InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w)
    (InfinitePlace.isReal_iff.2 (ComplexEmbedding.isReal_iff.2 h.symm))

private theorem pl_eq (τ : E →+* ℂ) : Fo.pl F τ = (InfinitePlace.mk τ).comap (algebraMap F E) := by
  rw [InfinitePlace.comap_mk]; rfl

private theorem sum_coord_pl {M : Type*} [AddCommGroup M] [Module ℂ M] (s : Cinf E) (G : InfinitePlace F → M) :
    ∑ τ : E →+* ℂ, coord τ s • G (Fo.pl F τ) = ∑ v, ((trI F s v : ℝ) : ℂ) • G v := by
  have hr : ∀ v, ((trI F s v : ℝ) : ℂ) • G v =
      ∑ w : InfinitePlace E, (if w.comap (algebraMap F E) = v then ((2 * (s w).re : ℝ) : ℂ) • G v else 0) := by
    intro v
    simp only [trI]
    rw [Complex.ofReal_sum, Finset.sum_smul]
    refine Finset.sum_congr rfl fun w _ => ?_
    split_ifs <;> simp
  simp only [hr]
  rw [Finset.sum_comm, ← Finset.sum_fiberwise Finset.univ InfinitePlace.mk]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _), fiber_eq, Finset.sum_pair (emb_ne w), pl_eq, pl_eq,
    InfinitePlace.mk_embedding, InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding,
    UpperTheory.V.FieldIso.coord_conj, UpperTheory.V.FieldIso.coord_embedding, ← add_smul, Complex.add_conj]

private theorem theta_ne (D : Dat F E) : D.θ ≠ 0 := by
  rw [← D.b1]; exact D.b.ne_zero 1

private theorem dE_sum (D : Dat F E) (O : Fo.Ops F) (τ : E →+* ℂ) :
    O.dE D τ 0 0 + O.dE D τ 1 1 = -O.h (Fo.pl F τ) := by
  have ht : τ D.θ ≠ 0 := fun h => theta_ne D ((map_eq_zero τ).1 h)
  have h2 : (2 : Module.End ℂ (S4 F)) = 1 + 1 := one_add_one_eq_two.symm
  simp only [Fo.Ops.dE, Fo.Ops.X, Fo.Ops.DX, Fo.Ops.h, Fin.sum_univ_two, Fin.sum_univ_four, h2]
  simp only [Fin.isValue, if_true, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val]
  generalize τ D.θ = t at ht
  simp only [mul_add, add_mul, mul_sub, sub_mul, smul_add, smul_sub, smul_mul_assoc, mul_smul_comm, smul_smul]
  match_scalars <;> field_simp <;> ring

end SlopeTestRemainingChoices

end UpperTheory.ConvolutionTheory.R2.Ff

theorem UpperTheory.ConvolutionTheory.R2.Ff.dLCen :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (O : Fo.Ops F), DLCen D O := by
  intro F E _ _ _ _ _ _ _ D O
  refine ⟨fun s => ?_, fun Y Y' => ?_, fun c Y => ?_, fun s => ?_⟩
  · have hz : ∀ i j, zE s i j = if i = j then s else 0 := by
      intro i j
      fin_cases i <;> fin_cases j <;> simp [zE, GlobalTheory.CuspRep.toL, Matrix.scalar_apply]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun τ _ => ?_
    simp only [Fin.sum_univ_two, hz]
    simp only [Fin.isValue, if_true, one_ne_zero, zero_ne_one, if_false, map_zero, zero_smul, add_zero, zero_add]
    rw [← smul_add, dE_sum, smul_neg]
  · simp only [Fo.Ops.dL, ← Finset.sum_add_distrib, ← add_smul]
    refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [show (Y + Y') i j = Y i j + Y' i j from rfl, map_add]
  · simp only [Fo.Ops.dL, Finset.smul_sum]
    refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [show (c • Y) i j = c • Y i j from rfl, UpperTheory.V.FieldIso.coord_smul, Complex.real_smul, mul_smul]
  · rw [sum_coord_pl s (fun v => TR.Eop v 0 0 + TR.Eop v 1 1)]
    have hz : zF (trI F s) = ∑ v, trI F s v • (TR.toL (Matrix.single 0 0 (Pi.single v 1)) + TR.toL (Matrix.single 1 1 (Pi.single v 1)) : TR.Lie F 2) := by
      ext i j w
      fin_cases i <;> fin_cases j <;> simp [zF, TR.toL, Matrix.scalar_apply, Finset.sum_apply, Pi.single_apply, Matrix.single_apply]
    rw [hz, map_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [map_smul, map_add]
    first
      | rfl
      | exact (Complex.coe_smul _ _).symm
      | (ext φ g; rfl)
