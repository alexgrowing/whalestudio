import Mathlib
import GroundTheory.GlobalFields.Adele.IntegersLattice

namespace GroundTheory.Global

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Module MeasureTheory
open scoped Classical ComplexConjugate RealInnerProductSpace FourierTransform Real

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

def mixedTrace : mixedSpace K →ₗ[ℝ] ℝ where
  toFun x := ∑ w, x.1 w + ∑ w, 2 * (x.2 w).re
  map_add' x y := by
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, Complex.add_re, mul_add,
      Finset.sum_add_distrib]
    ring
  map_smul' c x := by
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, Complex.real_smul,
      Complex.re_ofReal_mul, RingHom.id_apply, Finset.mul_sum, mul_add]
    congr 1
    exact Finset.sum_congr rfl fun _ _ => by ring

theorem mixedTrace_apply (x : mixedSpace K) :
    mixedTrace K x = ∑ w, x.1 w + ∑ w, 2 * (x.2 w).re := rfl

theorem mixedTrace_mixedEmbedding (x : K) :
    mixedTrace K (mixedEmbedding K x) = (Algebra.trace ℚ K x : ℝ) := by
  have h1 : ((Algebra.trace ℚ K x : ℚ) : ℝ) = ∑ φ : K →+* ℂ, (φ x).re := by
    have h := congrArg Complex.re (trace_eq_sum_embeddings ℂ (K := ℚ) (L := K) (x := x))
    rw [Complex.re_sum] at h
    rw [Fintype.sum_equiv (RingHom.equivRatAlgHom K ℂ) (fun φ => (φ x).re)
      (fun σ => (σ x).re) (fun _ => rfl)]
    simpa using h
  have h2 : ∀ φ : K →+* ℂ, (φ x).re = ((mk φ).embedding x).re := by
    intro φ
    rcases embedding_mk_eq φ with h | h <;> rw [h]
    simp [ComplexEmbedding.conjugate_coe_eq]
  have h3 : ∀ w : InfinitePlace K,
      ∑ φ ∈ Finset.univ.filter (fun φ : K →+* ℂ => mk φ = w), (φ x).re =
        mult w * (w.embedding x).re := by
    intro w
    rw [Finset.sum_congr rfl (fun φ hφ => by rw [h2, (Finset.mem_filter.mp hφ).2]),
      Finset.sum_const, card_filter_mk_eq, nsmul_eq_mul]
  rw [h1, ← Finset.sum_fiberwise Finset.univ (fun φ : K →+* ℂ => mk φ) (fun φ => (φ x).re)]
  simp_rw [h3]
  rw [sum_eq_sum_add_sum, mixedTrace_apply]
  congr 1
  · refine Finset.sum_congr rfl fun w _ => ?_
    rw [mult_isReal, Nat.cast_one, one_mul, mixedEmbedding_apply_isReal,
      ← embedding_of_isReal_apply w.2, Complex.ofReal_re]
  · refine Finset.sum_congr rfl fun w _ => ?_
    rw [mult_isComplex, mixedEmbedding_apply_isComplex]
    norm_num

def mixedTraceForm : LinearMap.BilinForm ℝ (mixedSpace K) :=
  (LinearMap.mul ℝ (mixedSpace K)).compr₂ (mixedTrace K)

theorem mixedTraceForm_apply (x y : mixedSpace K) :
    mixedTraceForm K x y = mixedTrace K (x * y) := rfl

theorem mixedTraceForm_apply' (x y : mixedSpace K) :
    mixedTraceForm K x y = ∑ w, x.1 w * y.1 w + ∑ w, 2 * (x.2 w * y.2 w).re := rfl

theorem mixedTraceForm_comm (x y : mixedSpace K) :
    mixedTraceForm K x y = mixedTraceForm K y x := by
  rw [mixedTraceForm_apply, mixedTraceForm_apply, mul_comm]

theorem mixedTraceForm_mixedEmbedding (a b : K) :
    mixedTraceForm K (mixedEmbedding K a) (mixedEmbedding K b) = (Algebra.trace ℚ K (a * b) : ℝ) := by
  rw [mixedTraceForm_apply, ← map_mul, mixedTrace_mixedEmbedding]

theorem mixedTraceForm_separatingLeft : (mixedTraceForm K).SeparatingLeft := by
  intro x hx
  have h := hx (x.1, fun w => conj (x.2 w))
  rw [mixedTraceForm_apply'] at h
  simp only [Complex.mul_conj, Complex.ofReal_re] at h
  have h1 : 0 ≤ ∑ w, x.1 w * x.1 w := Finset.sum_nonneg fun w _ => mul_self_nonneg _
  have h2 : 0 ≤ ∑ w, 2 * Complex.normSq (x.2 w) :=
    Finset.sum_nonneg fun w _ => mul_nonneg zero_le_two (Complex.normSq_nonneg _)
  have e1 : ∑ w, x.1 w * x.1 w = 0 := by linarith
  have e2 : ∑ w, 2 * Complex.normSq (x.2 w) = 0 := by linarith
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun w _ => mul_self_nonneg _)] at e1
  rw [Finset.sum_eq_zero_iff_of_nonneg
    (fun w _ => mul_nonneg zero_le_two (Complex.normSq_nonneg _))] at e2
  refine Prod.ext (funext fun w => ?_) (funext fun w => ?_)
  · simpa using e1 w (Finset.mem_univ _)
  · simpa using e2 w (Finset.mem_univ _)

theorem mixedTraceForm_nondegenerate : (mixedTraceForm K).Nondegenerate :=
  ⟨mixedTraceForm_separatingLeft K, fun y hy =>
    mixedTraceForm_separatingLeft K y fun x => by rw [mixedTraceForm_comm]; exact hy x⟩

def infiniteTraceForm (x y : InfiniteAdeleRing K) : ℝ :=
  mixedTraceForm K (homeomorphMixedSpace K x) (homeomorphMixedSpace K y)

end

end GroundTheory.Global
