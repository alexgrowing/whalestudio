import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartanInvolutionConjOfPosDef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasisAdaptedToCartanInvolution

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.RealLift

theorem exists_atInf_piInf_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (emb : ∀ w : InfinitePlace F, EmbOver E w) (f : InfinitePlace F → ℂ),
    ∃ z : AE F E, At (evI F) z ∧ ∀ w, piInf (emb w) z = f w := by
  intro F E _ _ _ _ _ σ h emb f
  have := h.1

  have him : ∀ (τ : E →+* ℂ) (e : E), σ e ≠ e → (τ e).im ≠ 0 := fun τ e he him => by
    apply he
    apply τ.injective
    rw [h.2.2.2 τ e]
    exact Complex.conj_eq_iff_im.2 him
  by_cases hσ : ∃ e : E, σ e ≠ e
  swap
  · push_neg at hσ
    refine ⟨0, fun u _ => smul_zero u, fun w => ?_⟩
    exfalso
    have := h.2.1
    refine (InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex (InfinitePlace.mk (emb w).1)))
      (InfinitePlace.isReal_mk_iff.2 (ComplexEmbedding.isReal_iff.2 (RingHom.ext fun x => ?_)))
    exact (h.2.2.2 (emb w).1 x).symm.trans (congrArg _ (hσ x))
  obtain ⟨e, he⟩ := hσ
  let lift : ∀ w : InfinitePlace F, ℝ → w.Completion := fun w t =>
    (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).symm t
  have hlift : ∀ w t, InfinitePlace.Completion.extensionEmbedding w (lift w t) = (t : ℂ) := fun w t => by
    rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply (IsTotallyReal.isReal w)]
    exact congrArg _ ((InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).apply_symm_apply t)
  let c : InfinitePlace F → ℝ := fun w => (f w).im / ((emb w).1 e).im
  let a : InfinitePlace F → ℝ := fun w => (f w).re - c w * ((emb w).1 e).re
  let A : AF F := ((fun w => lift w (a w) : Ainf F), 0)
  let C : AF F := ((fun w => lift w (c w) : Ainf F), 0)
  refine ⟨A ⊗ₜ[F] (1 : E) + C ⊗ₜ[F] e, fun u hu => ?_, fun w => ?_⟩
  · have hu1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (hu.trans (map_zero _).symm)
    have hA : u * A = 0 := by
      show ((u.1 * A.1, u.2 * (0 : Af F)) : Ainf F × Af F) = ((0, 0) : Ainf F × Af F)
      rw [hu1, zero_mul, mul_zero]
    have hC : u * C = 0 := by
      show ((u.1 * C.1, u.2 * (0 : Af F)) : Ainf F × Af F) = ((0, 0) : Ainf F × Af F)
      rw [hu1, zero_mul, mul_zero]
    rw [smul_add, TensorProduct.smul_tmul', TensorProduct.smul_tmul', smul_eq_mul, smul_eq_mul, hA, hC,
      TensorProduct.zero_tmul, TensorProduct.zero_tmul, add_zero]
  · change infEmb (emb w) (compInf F E w (A ⊗ₜ[F] (1 : E) + C ⊗ₜ[F] e)) = f w
    rw [map_add]
    change infEmb (emb w) (evInf F w A ⊗ₜ[F] (1 : E) + evInf F w C ⊗ₜ[F] e) = f w
    rw [map_add, infEmb_tmul, infEmb_tmul, map_one, mul_one]
    change InfinitePlace.Completion.extensionEmbedding w (lift w (a w)) +
      InfinitePlace.Completion.extensionEmbedding w (lift w (c w)) * (emb w).1 e = f w
    rw [hlift, hlift]
    have hne := him (emb w).1 e he
    apply Complex.ext
    · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, zero_mul, sub_zero, a]
      ring
    · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, zero_mul, add_zero, zero_add, c]
      field_simp

end GlobalTheory.RealLift
