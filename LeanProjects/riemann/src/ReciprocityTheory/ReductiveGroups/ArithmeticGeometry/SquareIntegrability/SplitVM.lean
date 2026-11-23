import Mathlib

namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField Complex Module

noncomputable section

variable {E : Type} [Field E] [NumberField E]

theorem emb_indep (g : (E →+* ℂ) → ℂ) (h : ∀ β : 𝓞 E, ∑ σ, σ (β : E) * g σ = 0) : g = 0 := by
  have hb : ∀ i, ∑ σ : E →+* ℂ, σ (integralBasis E i) * g σ = 0 := fun i => by
    rw [integralBasis_apply]
    exact h _
  have hE : ∀ x : E, ∑ σ : E →+* ℂ, σ x * g σ = 0 := by
    intro x
    rw [← (integralBasis E).sum_repr x]
    simp only [map_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun i _ => ?_
    have e : ∀ σ : E →+* ℂ, σ ((integralBasis E).repr x i • integralBasis E i) * g σ =
        ((integralBasis E).repr x i : ℂ) * (σ (integralBasis E i) * g σ) := fun σ => by
      rw [map_rat_smul, Rat.smul_def, mul_assoc]
    rw [Finset.sum_congr rfl fun σ _ => e σ, ← Finset.mul_sum, hb i, mul_zero]
  have hli : LinearIndependent ℂ (fun σ : E →+* ℂ => ((σ : E →* ℂ) : E → ℂ)) :=
    (linearIndependent_monoidHom E ℂ).comp (fun σ : E →+* ℂ => (σ : E →* ℂ))
      (fun a b hab => RingHom.ext fun x => DFunLike.congr_fun hab x)
  rw [Fintype.linearIndependent_iff] at hli
  funext σ
  refine hli g ?_ σ
  funext x
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
  rw [← hE x]
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp [mul_comm]

def ConjSymm (t : (E →+* ℂ) → ℂ) : Prop :=
  ∀ σ, t (ComplexEmbedding.conjugate σ) = (starRingEnd ℂ) (t σ)

theorem conjSymm_canonical (x : E) : ConjSymm (canonicalEmbedding E x) := fun σ => by
  simp only [canonicalEmbedding.apply_at, ComplexEmbedding.conjugate_coe_eq]

theorem conjSymm_sum {ι : Type} (s : Finset ι) (c : ι → ℝ) (v : ι → (E →+* ℂ) → ℂ)
    (hv : ∀ i, ConjSymm (v i)) : ConjSymm (∑ i ∈ s, c i • v i) := fun σ => by
  rw [Finset.sum_apply, Finset.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.smul_apply, Pi.smul_apply, hv i σ, Complex.real_smul, Complex.real_smul, map_mul,
    Complex.conj_ofReal]

theorem eq_of_commMap (t t' : (E →+* ℂ) → ℂ) (ht : ConjSymm t) (ht' : ConjSymm t')
    (h : mixedEmbedding.commMap E t = mixedEmbedding.commMap E t') : t = t' := by
  funext σ
  obtain ⟨w, hwdef⟩ : ∃ w, w = InfinitePlace.mk σ := ⟨_, rfl⟩
  have hcases := InfinitePlace.embedding_mk_eq σ
  rw [← hwdef] at hcases
  have key : t w.embedding = t' w.embedding := by
    by_cases hw : w.IsReal
    · have h1 := congrArg (fun m => m.1 ⟨w, hw⟩) h
      simp only [mixedEmbedding.commMap_apply_of_isReal] at h1
      have hr : ComplexEmbedding.conjugate w.embedding = w.embedding :=
        ComplexEmbedding.isReal_iff.mp (InfinitePlace.isReal_iff.mp hw)
      have a1 : starRingEnd ℂ (t w.embedding) = t w.embedding := by rw [← ht, hr]
      have a2 : starRingEnd ℂ (t' w.embedding) = t' w.embedding := by rw [← ht', hr]
      apply Complex.ext h1
      rw [Complex.conj_eq_iff_im.mp a1, Complex.conj_eq_iff_im.mp a2]
    · have hw' : w.IsComplex := InfinitePlace.not_isReal_iff_isComplex.mp hw
      have h1 := congrArg (fun m => m.2 ⟨w, hw'⟩) h
      simpa only [mixedEmbedding.commMap_apply_of_isComplex] using h1
  rcases hcases with he | he
  · rw [he] at key
    exact key
  · rw [he, ht, ht'] at key
    simpa using congrArg (starRingEnd ℂ) key

theorem real_span (t : (E →+* ℂ) → ℂ) (ht : ConjSymm t) :
    ∃ c : Free.ChooseBasisIndex ℤ (𝓞 E) → ℝ,
      t = ∑ k, c k • canonicalEmbedding E (integralBasis E k) := by
  refine ⟨fun k => (mixedEmbedding.latticeBasis E).repr (mixedEmbedding.commMap E t) k, ?_⟩
  apply eq_of_commMap t _ ht (conjSymm_sum Finset.univ
    (fun k => (mixedEmbedding.latticeBasis E).repr (mixedEmbedding.commMap E t) k)
    (fun k => canonicalEmbedding E (integralBasis E k)) fun k => conjSymm_canonical _)
  rw [map_sum]
  simp only [map_smul]
  conv_lhs => rw [← (mixedEmbedding.latticeBasis E).sum_repr (mixedEmbedding.commMap E t)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mixedEmbedding.latticeBasis_apply, mixedEmbedding.commMap_canonical_eq_mixed]

theorem conjugate_ne [IsTotallyComplex E] (σ : E →+* ℂ) : ComplexEmbedding.conjugate σ ≠ σ := by
  intro h
  have hr : ComplexEmbedding.IsReal σ := ComplexEmbedding.isReal_iff.mpr h
  exact InfinitePlace.not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex (InfinitePlace.mk σ))
    ⟨σ, hr, rfl⟩

end

end ReciprocityTheory.ChartRestriction.G.I2
