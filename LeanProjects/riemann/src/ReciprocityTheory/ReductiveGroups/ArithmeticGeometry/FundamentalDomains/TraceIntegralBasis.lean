import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound

namespace ReciprocityTheory.ChartRestriction.G.FD.TraceIntegralBasis

open NumberField InfinitePlace Module Submodule
open scoped ComplexConjugate Classical

variable (E : Type) [Field E] [NumberField E] [IsCMField E]

abbrev CP := {w : InfinitePlace E // IsComplex w}

abbrev VS := EuclideanSpace ℂ (CP E)

instance isEmpty_real : IsEmpty {w : InfinitePlace E // IsReal w} :=
  ⟨fun w => (not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex w.1)) w.2⟩

noncomputable def iota : E →+ VS E where
  toFun x := WithLp.toLp 2 (fun w : CP E => w.1.embedding x)
  map_zero' := by ext w; simp
  map_add' x y := by ext w; simp

variable {E}

lemma iota_apply (x : E) (w : CP E) : iota E x w = w.1.embedding x := rfl

lemma emb_cc (φ : E →+* ℂ) (y : E) : φ (cc y) = conj (φ y) := by
  unfold cc
  first
    | exact (IsCMField.isConj_complexConj E φ).eq y
    | exact ComplexEmbedding.IsConj.eq (IsCMField.isConj_complexConj φ) y
    | exact IsCMField.complexEmbedding_complexConj E φ y
    | simp

lemma conj_conj (φ : E →+* ℂ) :
    ComplexEmbedding.conjugate (ComplexEmbedding.conjugate φ) = φ := by
  first
    | exact ComplexEmbedding.conjugate_conjugate φ
    | (ext x; simp [ComplexEmbedding.conjugate_coe_eq])

lemma inner_iota (x y : E) :
    inner ℝ (iota E x) (iota E y) = ∑ w : CP E, (w.1.embedding x * conj (w.1.embedding y)).re := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [iota_apply, iota_apply, Complex.inner]
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

lemma norm_sq_iota (x : E) : ‖iota E x‖ ^ 2 = ∑ w : CP E, ‖w.1.embedding x‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [iota_apply]

lemma sum_re_eq_trace (u : E) :
    ∑ w : CP E, (w.1.embedding u).re = (1 / 2 : ℝ) * (Algebra.trace ℚ E u : ℝ) := by
  have hall : ∀ w : InfinitePlace E, IsComplex w := fun w =>
    InfinitePlace.not_isReal_iff_isComplex.mp fun hw =>
      IsEmpty.false (⟨w, hw⟩ : {w : InfinitePlace E // IsReal w})
  have hfib : ∀ w : InfinitePlace E,
      ∑ φ ∈ Finset.univ.filter (fun φ : E →+* ℂ => InfinitePlace.mk φ = w), φ u =
        w.embedding u + conj (w.embedding u) := by
    intro w
    have hne : ComplexEmbedding.conjugate w.embedding ≠ w.embedding := by
      intro h
      exact (InfinitePlace.not_isReal_iff_isComplex.mpr (hall w))
        (InfinitePlace.isReal_iff.mpr (ComplexEmbedding.isReal_iff.mpr h))
    have hset : Finset.univ.filter (fun φ : E →+* ℂ => InfinitePlace.mk φ = w) =
        {w.embedding, ComplexEmbedding.conjugate w.embedding} := by
      ext φ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      constructor
      · intro h
        have h' : InfinitePlace.mk φ = InfinitePlace.mk w.embedding := by
          rw [h, InfinitePlace.mk_embedding]
        rcases InfinitePlace.mk_eq_iff.mp h' with h1 | h1
        · exact Or.inl h1
        · right
          rw [← h1, conj_conj]
      · rintro (rfl | rfl)
        · exact InfinitePlace.mk_embedding w
        · rw [InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding]
    rw [hset, Finset.sum_pair hne.symm, ComplexEmbedding.conjugate_coe_eq]
  have h0 : algebraMap ℚ ℂ (Algebra.trace ℚ E u) = ∑ σ : E →ₐ[ℚ] ℂ, σ u := by
    first
      | exact trace_eq_sum_embeddings ℂ
      | exact trace_eq_sum_embeddings ℂ (x := u)
      | exact trace_eq_sum_embeddings (E := ℂ) (x := u)
      | exact Algebra.trace_eq_sum_embeddings ℂ
  have h1 : ∑ σ : E →ₐ[ℚ] ℂ, σ u = ∑ φ : E →+* ℂ, φ u :=
    (Fintype.sum_equiv (RingHom.equivRatAlgHom E ℂ) (fun φ : E →+* ℂ => φ u)
      (fun σ : E →ₐ[ℚ] ℂ => σ u)
      (fun _ => rfl)).symm
  have h2 : ∑ φ : E →+* ℂ, φ u =
      ∑ w : InfinitePlace E, (w.embedding u + conj (w.embedding u)) := by
    rw [← Finset.sum_fiberwise Finset.univ (fun φ : E →+* ℂ => InfinitePlace.mk φ) (fun φ => φ u)]
    refine Finset.sum_congr rfl fun w _ => ?_
    first
      | exact hfib w
      | convert hfib w
  have h3 : ((Algebra.trace ℚ E u : ℚ) : ℂ) =
      ∑ w : CP E, (w.1.embedding u + conj (w.1.embedding u)) := by
    rw [← eq_ratCast (algebraMap ℚ ℂ), h0, h1, h2]
    exact (Fintype.sum_equiv (Equiv.subtypeUnivEquiv hall) _ _ (fun _ => rfl)).symm
  have h4 := congrArg Complex.re h3
  rw [Complex.re_sum] at h4
  simp only [Complex.add_re, Complex.conj_re, Complex.ratCast_re] at h4
  rw [h4, Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  ring

variable (E)

noncomputable def toVS : mixedEmbedding.mixedSpace E ≃ₗ[ℝ] VS E :=
  LinearEquiv.ofLinearMap
    (f := (WithLp.linearEquiv 2 ℝ (CP E → ℂ)).symm.toLinearMap ∘ₗ LinearMap.snd ℝ _ _)
    (g := LinearMap.inr ℝ _ _ ∘ₗ (WithLp.linearEquiv 2 ℝ (CP E → ℂ)).toLinearMap)
    (by ext z w; simp)
    (by
      apply LinearMap.ext
      intro z
      refine Prod.ext (funext fun w => (IsEmpty.false w).elim) ?_
      simp)

noncomputable def bas : Basis (Free.ChooseBasisIndex ℤ (𝓞 E)) ℝ (VS E) :=
  (mixedEmbedding.latticeBasis E).map (toVS E)

variable {E}

lemma bas_apply (i : Free.ChooseBasisIndex ℤ (𝓞 E)) : bas E i = iota E (integralBasis E i) := by
  rw [bas, Basis.map_apply, mixedEmbedding.latticeBasis_apply]
  first
    | rfl
    | (ext w; simp [toVS, iota, mixedEmbedding])

lemma mem_span_bas {x : VS E} (hx : x ∈ span ℤ (Set.range (bas E))) :
    ∃ α : 𝓞 E, x = iota E (α : E) := by
  obtain ⟨c, rfl⟩ := (mem_span_range_iff_exists_fun ℤ).1 hx
  refine ⟨∑ i, c i • RingOfIntegers.basis E i, ?_⟩
  simp only [bas_apply, integralBasis_apply, ← map_zsmul, ← map_sum]

lemma card_CP : Fintype.card (CP E) = fdeg E ∧ finrank ℚ E = 2 * Fintype.card (CP E) := by
  have h := InfinitePlace.card_add_two_mul_card_eq_rank E
  have h0 : nrRealPlaces E = 0 := by
    first
      | exact Fintype.card_eq_zero
      | simp [nrRealPlaces]
  have h1 : nrComplexPlaces E = Fintype.card (CP E) := rfl
  rw [h0, zero_add, h1] at h
  refine ⟨?_, h.symm⟩
  unfold fdeg
  rw [← h]
  omega

lemma finrank_VS : finrank ℝ (VS E) = finrank ℚ E := by
  rw [← (toVS E).finrank_eq]
  first
    | exact mixedEmbedding.finrank E
    | exact mixedEmbedding.finrank

end ReciprocityTheory.ChartRestriction.G.FD.TraceIntegralBasis
