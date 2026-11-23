import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

noncomputable section

namespace GlobalTheory.CompanionTheory.RealPlaceAdele

open scoped TensorProduct
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def ofInf (c : ∀ w : InfinitePlace F, w.Completion) : AF F := ((c : Ainf F), (0 : Af F))

theorem mul_ofInf (u : AF F) (hu : evI F u = 0) (c : ∀ w : InfinitePlace F, w.Completion) : u * ofInf c = 0 := by
  have h1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact hu)
  refine Prod.ext ?_ ?_
  · change u.1 * _ = 0
    rw [h1, zero_mul]
  · change u.2 * 0 = 0
    rw [mul_zero]

theorem exists_adele_piInf : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (emb : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w)
    (z : InfinitePlace F → ℂ), ∃ x : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) x ∧
      ∀ w, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (emb w) x = z w := by
  intro F E _ _ _ _ _ σ h emb z
  have hF := h.1
  have hE := h.2.1
  have hconj := h.2.2.2
  obtain ⟨β, hβ⟩ : ∃ β : E, σ β ≠ β := by
    by_contra hcon
    push Not at hcon
    obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
    refine IsTotallyComplex.complexEmbedding_not_isReal φ (ComplexEmbedding.isReal_iff.2 (RingHom.ext fun x => ?_))
    rw [ComplexEmbedding.conjugate_coe_eq]
    have := hconj φ x
    rw [hcon x] at this
    exact this.symm
  have him : ∀ w, ((emb w).1 β).im ≠ 0 := fun w hw => hβ ((emb w).1.injective (by
    rw [hconj]
    exact Complex.conj_eq_iff_im.2 hw))
  let e : ∀ w : InfinitePlace F, w.Completion ≃+* ℝ := fun w =>
    InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)
  have he : ∀ w a, InfinitePlace.Completion.extensionEmbedding w a = ((e w a : ℝ) : ℂ) := fun w a =>
    (InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply (IsTotallyReal.isReal w) a).symm
  let s : InfinitePlace F → ℝ := fun w => (z w).im / ((emb w).1 β).im
  let r : InfinitePlace F → ℝ := fun w => (z w).re - s w * ((emb w).1 β).re
  refine ⟨ofInf (fun w => (e w).symm (r w)) ⊗ₜ[F] 1 + ofInf (fun w => (e w).symm (s w)) ⊗ₜ[F] β, ?_, fun w => ?_⟩
  · intro u hu
    rw [smul_add, TensorProduct.smul_tmul', TensorProduct.smul_tmul', smul_eq_mul, smul_eq_mul, mul_ofInf u hu,
      mul_ofInf u hu, TensorProduct.zero_tmul, TensorProduct.zero_tmul, add_zero]
  · have hc : ∀ (c : ∀ w : InfinitePlace F, w.Completion) (y : E),
        piInf (emb w) (ofInf c ⊗ₜ[F] y) = ((e w (c w) : ℝ) : ℂ) * (emb w).1 y := fun c y => by
      rw [← he]
      rfl
    rw [map_add, hc, hc]
    simp only [(e w).apply_symm_apply, map_one, mul_one]
    apply Complex.ext
    · simp only [Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul, r]; ring
    · simp only [Complex.add_im, Complex.ofReal_im, Complex.im_ofReal_mul, s]
      have := him w
      field_simp
      ring

end GlobalTheory.CompanionTheory.RealPlaceAdele

end
