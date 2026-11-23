import Formalism.PeriodIntegrals.EtaInfGen

noncomputable section

open NumberField Formalism.L2.Host

namespace PI.EtaInfGenW

variable {L : Type} [Field L] [NumberField L] {F : Type} [Field F] [NumberField F] [Algebra F L]

theorem comp_eq_embedding (φ : L →+* ℂ) (w : InfinitePlace F) (hw : w.IsReal)
    (h : (InfinitePlace.mk φ).comap (algebraMap F L) = w) :
    φ.comp (algebraMap F L) = w.embedding := by
  rw [InfinitePlace.comap_mk] at h
  have hr : ComplexEmbedding.IsReal (φ.comp (algebraMap F L)) := by
    rw [← InfinitePlace.isReal_mk_iff, h]; exact hw
  rw [← h, InfinitePlace.embedding_mk_eq_of_isReal hr]

theorem div_norm_real (r : ℝ) (hr : r ≠ 0) :
    ((r : ℂ) / ((‖(r : ℂ)‖ : ℝ) : ℂ)) = if (r : ℂ).re < 0 then -1 else 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_re]
  split_ifs with h
  · rw [abs_of_neg h, Complex.ofReal_neg, div_neg, div_self (Complex.ofReal_ne_zero.mpr hr)]
  · rw [abs_of_nonneg (not_lt.mp h), div_self (Complex.ofReal_ne_zero.mpr hr)]

theorem single (φ : L →+* ℂ) (w : InfinitePlace F) (hw : w.IsReal)
    (h : (InfinitePlace.mk φ).comap (algebraMap F L) = w) (k : Fˣ) :
    φ ((upF F k : Lˣ) : L) / ((‖φ ((upF F k : Lˣ) : L)‖ : ℝ) : ℂ) = ((etaInf F w k : ℂˣ) : ℂ) := by
  have hφ : φ ((upF F k : Lˣ) : L) = ((InfinitePlace.embedding_of_isReal hw (k : F) : ℝ) : ℂ) := by
    rw [InfinitePlace.embedding_of_isReal_apply, ← comp_eq_embedding φ w hw h]
    rfl
  have hne : (InfinitePlace.embedding_of_isReal hw (k : F) : ℝ) ≠ 0 :=
    (map_ne_zero _).mpr k.ne_zero
  rw [hφ, div_norm_real _ hne, etaInf, InfinitePlace.embedding_of_isReal_apply]
  split_ifs <;> simp

end PI.EtaInfGenW
