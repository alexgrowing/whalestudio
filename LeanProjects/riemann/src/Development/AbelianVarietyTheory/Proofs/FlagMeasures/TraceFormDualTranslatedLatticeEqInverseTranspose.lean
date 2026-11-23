import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsLatMeasurableConst
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetDetNormPos
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CoeSmulMem
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.MeanDual

namespace GlobalTheory.MeanDual.LatticeDual

variable {E : Type} [Field E] [NumberField E]

theorem sum_embeddings_pairs (hE : IsTotallyComplex E) (f : (E →+* ℂ) → ℂ) :
    ∑ φ : E →+* ℂ, f φ =
      ∑ w : InfinitePlace E, (f w.embedding + f (ComplexEmbedding.conjugate w.embedding)) := by
  classical
  rw [← Finset.sum_fiberwise (s := univ) (g := fun φ : E →+* ℂ => InfinitePlace.mk φ)]
  refine Finset.sum_congr rfl fun w _ => ?_
  have hne : w.embedding ≠ ComplexEmbedding.conjugate w.embedding := by
    intro h
    have hc := IsTotallyComplex.isComplex (K := E) w
    rw [InfinitePlace.isComplex_iff, ComplexEmbedding.isReal_iff] at hc
    exact hc h.symm
  rw [← Finset.sum_pair hne]
  congr 1
  ext φ
  simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
  conv_lhs => rw [← InfinitePlace.mk_embedding w, InfinitePlace.mk_eq_iff]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · right
      rw [← h]; ext x; simp
  · rintro (h | h)
    · exact Or.inl h
    · right
      rw [h]; ext x; simp

theorem sum_re_embedding (hE : IsTotallyComplex E) (e : E) :
    ∑ w : InfinitePlace E, (w.embedding e).re = ((Algebra.trace ℚ E e : ℚ) : ℝ) / 2 := by
  have h1 := trace_eq_sum_embeddings (K := ℚ) (L := E) ℂ (x := e)
  have h2 : ∑ σ : E →ₐ[ℚ] ℂ, σ e = ∑ φ : E →+* ℂ, φ e :=
    (Fintype.sum_equiv (RingHom.equivRatAlgHom E ℂ) _ _ (fun φ => rfl)).symm
  rw [h2, sum_embeddings_pairs hE] at h1
  have h3 := congrArg Complex.re h1
  simp only [eq_ratCast, Complex.ratCast_re, Complex.re_sum, Complex.add_re,
    ComplexEmbedding.conjugate_coe_eq, Complex.conj_re] at h3
  rw [h3, Finset.sum_add_distrib]; ring

theorem eq_zero_of_sum_re (hE : IsTotallyComplex E) (c : InfinitePlace E → ℂ)
    (h : ∀ e : E, ∑ w : InfinitePlace E, (w.embedding e * c w).re = 0) : c = 0 := by
  classical
  have hli : LinearIndependent ℂ (fun φ : E →+* ℂ => (φ : E → ℂ)) :=
    (linearIndependent_monoidHom E ℂ).comp (fun φ : E →+* ℂ => φ.toMonoidHom)
      (fun a b hab => by ext x; exact DFunLike.congr_fun hab x)
  let d : (E →+* ℂ) → ℂ := fun φ =>
    if φ = (InfinitePlace.mk φ).embedding then c (InfinitePlace.mk φ)
    else (starRingEnd ℂ) (c (InfinitePlace.mk φ))
  have hd1 : ∀ w : InfinitePlace E, d w.embedding = c w := by
    intro w; simp [d]
  have hd2 : ∀ w : InfinitePlace E,
      d (ComplexEmbedding.conjugate w.embedding) = (starRingEnd ℂ) (c w) := by
    intro w
    have hc := IsTotallyComplex.isComplex (K := E) w
    rw [InfinitePlace.isComplex_iff, ComplexEmbedding.isReal_iff] at hc
    simp [d, InfinitePlace.mk_conjugate_eq, hc]
  have hz := Fintype.linearIndependent_iff.1 hli d (by
    funext e
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    rw [sum_embeddings_pairs hE (fun φ => d φ * φ e)]
    have : ∀ w : InfinitePlace E, d w.embedding * w.embedding e +
        d (ComplexEmbedding.conjugate w.embedding) * ComplexEmbedding.conjugate w.embedding e
        = ((2 * (w.embedding e * c w).re : ℝ) : ℂ) := by
      intro w
      rw [hd1, hd2, ComplexEmbedding.conjugate_coe_eq, ← map_mul, Complex.add_conj, mul_comm (c w)]
    simp only [this]
    rw [← Complex.ofReal_sum, ← Finset.mul_sum, h e]; simp)
  funext w
  rw [← hd1 w]; exact hz _

theorem exists_int_smul_mem {j : ℕ} (Λ : Submodule (𝓞 E) (Fin j → E))
    (hΛ : Submodule.IsLattice E Λ) (x : Fin j → E) : ∃ n : ℤ, n ≠ 0 ∧ (n : E) • x ∈ Λ := by
  first
  | exact @_root_.GlobalTheory.IntegralMultiple.main
  | exact _root_.GlobalTheory.IntegralMultiple.main
  | (apply _root_.GlobalTheory.IntegralMultiple.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntegralMultiple.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntegralMultiple.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntegralMultiple.main ..)

theorem pairing_rational (hE : IsTotallyComplex E) {j : ℕ} (x y : Fin j → E) :
    ∑ w : InfinitePlace E,
      ((fun a => w.embedding (x a)) ⬝ᵥ (fun a => w.embedding (y a))).re =
      ((Algebra.trace ℚ E (x ⬝ᵥ y) : ℚ) : ℝ) / 2 := by
  rw [← sum_re_embedding hE]
  refine Finset.sum_congr rfl fun w _ => ?_
  simp only [dotProduct, map_sum, map_mul]

theorem exists_trDual (hE : IsTotallyComplex E) {j : ℕ} (Λ : Submodule (𝓞 E) (Fin j → E))
    (hΛ : Submodule.IsLattice E Λ) (u : InfinitePlace E → Fin j → ℂ)
    (hu : ∀ x ∈ Λ, ∃ z : ℤ, ∑ w : InfinitePlace E, ((fun a => w.embedding (x a)) ⬝ᵥ u w).re = z) :
    ∃ y ∈ trDual E j Λ, ∀ w a, u w a = w.embedding (y a) := by
  classical
  let φ : (Fin j → E) →+ ℝ :=
    { toFun := fun x => ∑ w : InfinitePlace E, ((fun a => w.embedding (x a)) ⬝ᵥ u w).re
      map_zero' := by simp [dotProduct]
      map_add' := by
        intro x y
        simp [dotProduct, add_mul, Finset.sum_add_distrib] }
  have hq : ∀ x, ∃ q : ℚ, φ x = q := by
    intro x
    obtain ⟨n, hn, hx⟩ := exists_int_smul_mem Λ hΛ x
    obtain ⟨z, hz⟩ := hu _ hx
    have h1 : φ (n • x) = z := by
      rw [← Int.cast_smul_eq_zsmul E]; exact hz
    rw [map_zsmul, zsmul_eq_mul] at h1
    refine ⟨z / n, ?_⟩
    have : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    push_cast
    field_simp
    linarith
  choose q hq using hq
  let ψ : (Fin j → E) →+ ℚ :=
    { toFun := q
      map_zero' := by
        apply Rat.cast_injective (α := ℝ)
        rw [← hq]; simp
      map_add' := by
        intro x y
        apply Rat.cast_injective (α := ℝ)
        rw [Rat.cast_add, ← hq, ← hq, ← hq, map_add] }
  have hy : ∀ a : Fin j, ∃ y : E, ∀ e : E,
      Algebra.trace ℚ E (y * e) = 2 * q (Pi.single a e) := by
    intro a
    obtain ⟨y, hy⟩ := ((Algebra.traceForm ℚ E).toDual (traceForm_nondegenerate ℚ E)).surjective
      ((2 : ℚ) • (ψ.toRatLinearMap ∘ₗ LinearMap.single ℚ (fun _ => E) a))
    refine ⟨y, fun e => ?_⟩
    have := LinearMap.congr_fun hy e
    rw [LinearMap.BilinForm.toDual_def] at this
    simpa [ψ] using this
  choose y hy using hy
  have key : ∀ w a, u w a = w.embedding (y a) := by
    intro w a
    have := eq_zero_of_sum_re hE (fun w => u w a - w.embedding (y a)) (by
      intro e
      have h1 : φ (Pi.single a e) = ∑ w : InfinitePlace E, (w.embedding e * u w a).re := by
        refine Finset.sum_congr rfl fun w _ => ?_
        congr 1
        simp only [dotProduct]
        rw [Finset.sum_eq_single a]
        · simp
        · intro b _ hb; simp [hb]
        · simp
      have h2 := sum_re_embedding hE (y a * e)
      rw [hy] at h2
      simp only [mul_sub, Complex.sub_re, Finset.sum_sub_distrib, ← map_mul]
      rw [← h1, hq, mul_comm e, h2]; push_cast; ring)
    exact sub_eq_zero.1 (congrFun this w)
  refine ⟨y, ?_, key⟩
  intro x hx
  obtain ⟨z, hz⟩ := hu x hx
  refine ⟨z, ?_⟩
  have h1 := pairing_rational hE x y
  have h2 : ∀ w, u w = fun a => w.embedding (y a) := fun w => funext (key w)
  simp only [h2] at hz
  rw [hz] at h1
  apply Rat.cast_injective (α := ℝ)
  push_cast
  linarith

end GlobalTheory.MeanDual.LatticeDual

namespace GlobalTheory.MeanDual
open LatticeDual

theorem dualAt_latAt_eq_latAt_trDual : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E → ∀ (j : ℕ) (Λ : Submodule (𝓞 E) (Fin j → E)), Submodule.IsLattice E Λ → ∀ g : MatInf E j, 0 < detNorm E j g → dualAt E j (latAt E j Λ g) = latAt E j (trDual E j Λ) (invT E j g) := by
  intro E _ _ hE j Λ hΛ g hg
  have hdet : ∀ w, IsUnit (of (g w)).det := fun w =>
    isUnit_iff_ne_zero.2 ((detNorm_pos_iff E j g).1 hg w)
  have hinv : ∀ w, (of (invT E j g w))⁻¹ = (of (g w))ᵀ := by
    intro w
    rw [of_invT, ← Matrix.transpose_nonsing_inv, Matrix.nonsing_inv_nonsing_inv _ (hdet w)]
  have hadj : ∀ (w : InfinitePlace E) (v v' : Fin j → ℂ),
      ((of (g w))⁻¹ *ᵥ v) ⬝ᵥ v' = v ⬝ᵥ ((of (g w))⁻¹ᵀ *ᵥ v') := by
    intro w v v'
    rw [Matrix.mulVec_transpose, dotProduct_comm v, ← Matrix.dotProduct_mulVec, dotProduct_comm]
  have hc1 : ∀ (w : InfinitePlace E) (v : Fin j → ℂ),
      (of (g w))⁻¹ᵀ *ᵥ ((of (g w))ᵀ *ᵥ v) = v := by
    intro w v
    rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ (hdet w)]; simp
  have hc2 : ∀ (w : InfinitePlace E) (v : Fin j → ℂ),
      (of (g w))ᵀ *ᵥ ((of (g w))⁻¹ᵀ *ᵥ v) = v := by
    intro w v
    rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, Matrix.nonsing_inv_mul _ (hdet w)]; simp
  apply le_antisymm
  · refine Submodule.span_le.2 fun v hv => ?_
    obtain ⟨y, hy, hyv⟩ := exists_trDual hE Λ hΛ (fun w => (of (g w))⁻¹ᵀ *ᵥ v w) (by
      intro x hx
      obtain ⟨z, hz⟩ := hv _ (Submodule.subset_span ⟨x, hx, rfl⟩)
      refine ⟨z, ?_⟩
      rw [← hz]
      exact Finset.sum_congr rfl fun w _ => by rw [← hadj])
    refine Submodule.subset_span ⟨y, hy, ?_⟩
    funext w
    have : (fun a => w.embedding (y a)) = (of (g w))⁻¹ᵀ *ᵥ v w := funext fun a => (hyv w a).symm
    simp only [hinv, this, hc2]
  · refine Submodule.span_mono ?_
    rintro _ ⟨y, hy, rfl⟩ v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨x, hx, rfl⟩ := hv
      obtain ⟨z, hz⟩ := hy x hx
      refine ⟨z, ?_⟩
      simp only [hinv, hadj, hc1]
      rw [pairing_rational hE, hz]; push_cast; ring
    | zero => exact ⟨0, by simp⟩
    | add v v' _ _ h h' =>
      obtain ⟨z, hz⟩ := h
      obtain ⟨z', hz'⟩ := h'
      refine ⟨z + z', ?_⟩
      push_cast
      rw [← hz, ← hz', ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [← Complex.add_re, ← add_dotProduct]; rfl
    | smul n v _ h =>
      obtain ⟨z, hz⟩ := h
      refine ⟨n * z, ?_⟩
      push_cast
      rw [← hz, Finset.mul_sum]
      refine Finset.sum_congr rfl fun w _ => ?_
      have : (n • v) w = n • v w := rfl
      rw [this, smul_dotProduct]; simp

end GlobalTheory.MeanDual
