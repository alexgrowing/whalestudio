import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.ThK

theorem exists_at_evI_piInf_eq (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (c : InfinitePlace F → ℂ) :
    ∃ z : AE F E, At (evI F) z ∧ ∀ w, piInf (τ w) z = c w := by
  classical
  have := h.1
  have := h.2.1

  have hloc : ∀ w : InfinitePlace F, ∃ (α : E) (a b : w.Completion),
      InfinitePlace.Completion.extensionEmbedding w a +
        InfinitePlace.Completion.extensionEmbedding w b * (τ w).1 α = c w := by
    intro w
    have hα : ∃ α : E, ((τ w).1 α).im ≠ 0 := by
      by_contra hn
      push Not at hn
      refine (InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex (InfinitePlace.mk (τ w).1)))
        (InfinitePlace.isReal_mk_iff.2 (ComplexEmbedding.isReal_iff.2 (RingHom.ext fun x => ?_)))
      exact Complex.conj_eq_iff_im.2 (hn x)
    obtain ⟨α, hα⟩ := hα
    have hs := InfinitePlace.Completion.surjective_extensionEmbeddingOfIsReal (IsTotallyReal.isReal w)
    obtain ⟨a, ha⟩ := hs ((c w).re - (c w).im / ((τ w).1 α).im * ((τ w).1 α).re)
    obtain ⟨b, hb⟩ := hs ((c w).im / ((τ w).1 α).im)
    refine ⟨α, a, b, ?_⟩
    rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply (IsTotallyReal.isReal w),
      ← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply (IsTotallyReal.isReal w), ha, hb]
    apply Complex.ext
    · simp only [Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul]; ring
    · simp only [Complex.add_im, Complex.ofReal_im, Complex.im_ofReal_mul]; field_simp; ring
  choose α a b hab using hloc
  let δ : ∀ w : InfinitePlace F, w.Completion → AF F := fun w x =>
    ((Pi.single w x : ∀ v : InfinitePlace F, v.Completion), 0)
  have hδ : ∀ (u : AF F), evI F u = 0 → ∀ w x, u * δ w x = 0 := by
    intro u hu w x
    have h1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).map_eq_zero_iff.1 hu
    refine Prod.ext ?_ ?_
    · change u.1 * _ = 0
      rw [h1, zero_mul]
    · change u.2 * 0 = 0
      rw [mul_zero]
  have hp : ∀ w v x (e : E), piInf (τ w) (δ v x ⊗ₜ[F] e) =
      InfinitePlace.Completion.extensionEmbedding w ((Pi.single v x : ∀ v : InfinitePlace F, v.Completion) w)
        * (τ w).1 e := fun _ _ _ _ => rfl
  refine ⟨∑ w, (δ w (a w) ⊗ₜ[F] (1 : E) + δ w (b w) ⊗ₜ[F] α w), fun u hu => ?_, fun w => ?_⟩
  · rw [Finset.smul_sum]
    refine Finset.sum_eq_zero fun w _ => ?_
    rw [smul_add, TensorProduct.smul_tmul', TensorProduct.smul_tmul', smul_eq_mul, smul_eq_mul, hδ u hu, hδ u hu,
      TensorProduct.zero_tmul, TensorProduct.zero_tmul, add_zero]
  · rw [map_sum, Finset.sum_eq_single w]
    · rw [map_add, hp, hp, Pi.single_eq_same, Pi.single_eq_same, map_one, mul_one, hab]
    · intro v _ hv
      rw [map_add, hp, hp, Pi.single_eq_of_ne hv.symm, Pi.single_eq_of_ne hv.symm, map_zero, zero_mul, zero_mul, add_zero]
    · simp

end GlobalTheory.ThK
