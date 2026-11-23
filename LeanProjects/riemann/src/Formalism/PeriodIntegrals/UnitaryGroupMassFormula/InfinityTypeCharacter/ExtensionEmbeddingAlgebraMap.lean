import Mathlib
import Formalism.PeriodIntegrals.InfTypeChar

noncomputable section

open NumberField

namespace PI.InfTypeCharW

def normalize : ℂˣ →* ℂˣ where
  toFun z := Units.mk0 ((z : ℂ) / ((‖(z : ℂ)‖ : ℝ) : ℂ))
    (div_ne_zero z.ne_zero (by exact_mod_cast (norm_ne_zero_iff.mpr z.ne_zero)))
  map_one' := by ext; simp
  map_mul' a b := by
    ext
    simp only [Units.val_mul, Units.val_mk0, norm_mul, Complex.ofReal_mul]
    rw [mul_div_mul_comm]

variable {L : Type} [Field L] [NumberField L]

theorem extensionEmbedding_algebraMap (w : InfinitePlace L) (k : L) :
    InfinitePlace.Completion.extensionEmbedding w (algebraMap L w.Completion k) = w.embedding k := by
  rw [InfinitePlace.Completion.algebraMap_apply]
  exact InfinitePlace.Completion.extensionEmbedding_coe w _

theorem exists_ext (φ : L →+* ℂ) : ∃ ι : (InfinitePlace.mk φ).Completion →+* ℂ,
    Continuous ι ∧ ∀ k : L, ι (algebraMap L _ k) = φ k := by
  rcases InfinitePlace.embedding_mk_eq φ with h | h
  · refine ⟨InfinitePlace.Completion.extensionEmbedding _,
      (InfinitePlace.Completion.isometry_extensionEmbedding _).continuous, fun k => ?_⟩
    rw [extensionEmbedding_algebraMap, h]
  · refine ⟨(starRingEnd ℂ).comp (InfinitePlace.Completion.extensionEmbedding _),
      Complex.continuous_conj.comp (InfinitePlace.Completion.isometry_extensionEmbedding _).continuous,
      fun k => ?_⟩
    rw [RingHom.comp_apply, extensionEmbedding_algebraMap, h, ComplexEmbedding.conjugate_coe_eq]
    simp

end PI.InfTypeCharW
