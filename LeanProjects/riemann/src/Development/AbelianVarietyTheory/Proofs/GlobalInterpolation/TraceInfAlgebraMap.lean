import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.LocalDualIndex

namespace GlobalTheory.TraceSumRealEmbeddings

open NumberField NumberField.InfinitePlace

theorem re_embedding_mk {F : Type} [Field F] (φ : F →+* ℂ) (x : F) :
    ((InfinitePlace.mk φ).embedding x).re = (φ x).re := by
  rcases InfinitePlace.embedding_mk_eq φ with h | h <;> rw [h]
  rw [ComplexEmbedding.conjugate_coe_eq, Complex.conj_re]

theorem sum_re_embeddings (F : Type) [Field F] [NumberField F] (x : F) :
    ∑ φ : F →+* ℂ, (φ x).re = ∑ w : InfinitePlace F, (w.mult : ℝ) * (w.embedding x).re := by
  classical
  rw [← Finset.univ.sum_fiberwise (fun φ => InfinitePlace.mk φ)]
  refine Finset.sum_congr rfl fun w _ => ?_
  have hw : ∀ φ ∈ ({φ | InfinitePlace.mk φ = w} : Finset (F →+* ℂ)), (φ x).re = (w.embedding x).re :=
    fun φ hφ => by rw [← (Finset.mem_filter.mp hφ).2, re_embedding_mk]
  rw [Finset.sum_congr rfl hw, Finset.sum_const, InfinitePlace.card_filter_mk_eq, nsmul_eq_mul]

theorem trace_eq_sum_re (F : Type) [Field F] [NumberField F] (x : F) :
    ((Algebra.trace ℚ F x : ℚ) : ℝ) = ∑ φ : F →+* ℂ, (φ x).re := by
  have h2 : ((Algebra.trace ℚ F x : ℚ) : ℂ) = ∑ φ : F →+* ℂ, φ x := by
    rw [Fintype.sum_equiv (RingHom.equivRatAlgHom F ℂ) (fun φ => φ x) (fun σ => σ x) (fun φ => rfl),
      ← trace_eq_sum_embeddings]
    exact (eq_ratCast (algebraMap ℚ ℂ) _).symm
  rw [← Complex.re_sum, ← h2, Complex.ratCast_re]

theorem traceInf_algebraMap (F : Type) [Field F] [NumberField F] (x : F) :
    GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex.traceInf F (algebraMap F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf F) x) =
      ((Algebra.trace ℚ F x : ℚ) : ℝ) := by
  rw [trace_eq_sum_re, sum_re_embeddings]
  unfold GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex.traceInf
  refine Finset.sum_congr rfl fun w _ => ?_
  congr 2
  exact InfinitePlace.Completion.extensionEmbedding_coe w ((WithAbs.equiv w.1).symm x)

end GlobalTheory.TraceSumRealEmbeddings
