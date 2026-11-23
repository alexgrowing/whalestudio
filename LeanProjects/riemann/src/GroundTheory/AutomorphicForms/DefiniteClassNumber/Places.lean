import Mathlib
import GroundTheory.AutomorphicForms.DefiniteClassNumber.HermTraceSelfOfHermValue

noncomputable section

namespace GroundTheory.Automorphic

open Module Matrix TensorProduct NumberField NumberField.InfinitePlace

variable {K : Type*} [Field K] [NumberField K]

section TotallyReal

abbrev realEmb (hreal : ∀ w : InfinitePlace K, w.IsReal) (w : InfinitePlace K) : K →+* ℝ :=
  embedding_of_isReal (hreal w)

omit [NumberField K] in
theorem realEmb_eq_extension (hreal : ∀ w : InfinitePlace K, w.IsReal) (w : InfinitePlace K)
    (k : K) : Completion.extensionEmbeddingOfIsReal (hreal w) (algebraMap K w.Completion k) =
      realEmb hreal w k := by
  rw [Completion.algebraMap_apply]
  exact Completion.extensionEmbeddingOfIsReal_coe (hreal w) _

def embeddingsEquivPlaces (hreal : ∀ w : InfinitePlace K, w.IsReal) :
    (K →+* ℂ) ≃ InfinitePlace K where
  toFun := InfinitePlace.mk
  invFun w := w.embedding
  left_inv φ := by
    show (InfinitePlace.mk φ).embedding = φ
    rcases embedding_mk_eq φ with h | h
    · exact h
    · have hr := isReal_iff.1 (hreal (InfinitePlace.mk φ))
      rw [ComplexEmbedding.isReal_iff, h] at hr
      have hφ : ComplexEmbedding.conjugate (ComplexEmbedding.conjugate φ) = φ := star_star φ
      rw [h]
      exact hr.symm.trans hφ
  right_inv w := mk_embedding w

theorem trace_eq_sum_realEmb (hreal : ∀ w : InfinitePlace K, w.IsReal) (t : K) :
    (Algebra.trace ℚ K t : ℝ) = ∑ w, realEmb hreal w t := by
  have h1 := trace_eq_sum_embeddings ℂ (K := ℚ) (L := K) (x := t)
  have h2 : ∑ σ : K →ₐ[ℚ] ℂ, σ t = ∑ φ : K →+* ℂ, φ t :=
    (Fintype.sum_equiv (RingHom.equivRatAlgHom K ℂ) _ _ fun φ => rfl).symm
  have h3 : ∑ φ : K →+* ℂ, φ t = ∑ w : InfinitePlace K, w.embedding t :=
    Fintype.sum_equiv (embeddingsEquivPlaces hreal) _ _ fun φ => by
      have := (embeddingsEquivPlaces hreal).left_inv φ
      exact (congrFun (congrArg DFunLike.coe this) t).symm
  apply Complex.ofReal_injective
  rw [Complex.ofReal_ratCast, ← eq_ratCast (algebraMap ℚ ℂ), h1, h2, h3, Complex.ofReal_sum]
  exact Finset.sum_congr rfl fun w _ => (embedding_of_isReal_apply (hreal w) t).symm

theorem exists_forall_pos_mul_realEmb (hreal : ∀ w : InfinitePlace K, w.IsReal)
    (ε : InfinitePlace K → ℝ) (hε : ∀ w, ε w ≠ 0) :
    ∃ θ : K, ∀ w, 0 < ε w * realEmb hreal w θ := by
  let ψ := fun w : InfinitePlace K => Completion.ringEquivRealOfIsReal (hreal w)
  have hψc : ∀ w, Continuous (Completion.extensionEmbeddingOfIsReal (hreal w)) := fun w =>
    (Completion.isometry_extensionEmbeddingOfIsReal (hreal w)).continuous
  let U : Set (InfiniteAdeleRing K) :=
    ⋂ w, {q | 0 < ε w * Completion.extensionEmbeddingOfIsReal (hreal w) (q w)}
  have hU : IsOpen U := isOpen_iInter_of_finite fun w =>
    isOpen_lt continuous_const (continuous_const.mul ((hψc w).comp (continuous_apply w)))
  let p : InfiniteAdeleRing K := fun w => (ψ w).symm (ε w)
  have hp : p ∈ U := by
    simp only [U, Set.mem_iInter, Set.mem_ofPred_eq]
    intro w
    have : Completion.extensionEmbeddingOfIsReal (hreal w) (p w) = ε w :=
      (ψ w).apply_symm_apply (ε w)
    rw [this]
    exact mul_self_pos.2 (hε w)
  obtain ⟨θ, hθ⟩ := (InfiniteAdeleRing.denseRange_algebraMap (K := K)).exists_mem_open hU ⟨p, hp⟩
  refine ⟨θ, fun w => ?_⟩
  have := Set.mem_iInter.1 hθ w
  simp only [Set.mem_ofPred_eq] at this
  rwa [show (algebraMap K (InfiniteAdeleRing K) θ) w = algebraMap K w.Completion θ from rfl,
    realEmb_eq_extension] at this

end TotallyReal

section Form

variable {E : Type*} [CommRing E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι E)
variable {κ : Type*} [Fintype κ] (b : Basis κ K E)

def traceGram : Matrix (ι × κ) (ι × κ) K :=
  fun a c => hermTrace K H K (stdVec K b a) (stdVec K b c)

variable (R : Type*) [CommRing R] [Algebra K R]

def vecOfCoords (c : ι × κ → R) : ι → R ⊗[K] E :=
  fun i => (Algebra.TensorProduct.basis R b).equivFun.symm fun k => c (i, k)

omit [NumberField K] [Algebra.IsQuadraticExtension K E] [Fintype ι] [DecidableEq ι] in
theorem vecCoords_vecOfCoords (c : ι × κ → R) : vecCoords R b (vecOfCoords b R c) = c := by
  funext a
  simp only [vecCoords, vecOfCoords]
  rw [← Basis.equivFun_apply, LinearEquiv.apply_symm_apply]

omit [NumberField K] [Algebra.IsQuadraticExtension K E] [Fintype ι] [DecidableEq ι] in
theorem vecOfCoords_vecCoords (x : ι → R ⊗[K] E) : vecOfCoords b R (vecCoords R b x) = x := by
  funext i
  simp only [vecCoords, vecOfCoords]
  conv_rhs => rw [← (Algebra.TensorProduct.basis R b).equivFun.symm_apply_apply (x i)]
  rfl

variable {H b}

omit [NumberField K] in

theorem hermTrace_eq_sum_traceGram (x y : ι → R ⊗[K] E) :
    hermTrace K H R x y = ∑ a : ι × κ, ∑ c : ι × κ, vecCoords R b x a * vecCoords R b y c *
      algebraMap K R (traceGram H b a c) :=
  hermTrace_eq_sum H b x y

omit [NumberField K] in

theorem exists_sign_traceGram {w : InfinitePlace K} (hw : w.IsReal)
    (hdef : IsHermDefiniteAt H w hw) :
    ∃ ε : ℝ, ε ≠ 0 ∧ ∀ v : ι × κ → ℝ, v ≠ 0 →
      0 < ε * ∑ a, ∑ c, v a * v c * embedding_of_isReal hw (traceGram H b a c) := by
  let ψ := Completion.ringEquivRealOfIsReal hw
  have key : ∀ v : ι × κ → ℝ, ψ (hermTrace K H w.Completion (vecOfCoords b w.Completion
      (fun a => ψ.symm (v a))) (vecOfCoords b w.Completion (fun a => ψ.symm (v a)))) =
      ∑ a, ∑ c, v a * v c * embedding_of_isReal hw (traceGram H b a c) := by
    intro v
    rw [hermTrace_eq_sum_traceGram (H := H) (b := b) w.Completion,
      vecCoords_vecOfCoords b w.Completion (fun a => ψ.symm (v a)), map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [map_mul, map_mul, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
    congr 1
    rw [Completion.ringEquivRealOfIsReal_apply, Completion.algebraMap_apply]
    exact Completion.extensionEmbeddingOfIsReal_coe hw _
  have hne : ∀ v : ι × κ → ℝ, v ≠ 0 →
      vecOfCoords b w.Completion (fun a => ψ.symm (v a)) ≠ 0 := by
    intro v hv h
    apply hv
    funext a
    have := congrFun (vecCoords_vecOfCoords b w.Completion (fun a => ψ.symm (v a))) a
    rw [h] at this
    have h0 : vecCoords w.Completion b (0 : ι → w.Completion ⊗[K] E) a = 0 := by
      simp [vecCoords]
    rw [h0] at this
    have := congrArg ψ this
    rw [RingEquiv.apply_symm_apply, map_zero] at this
    exact this.symm
  rcases hdef with hpos | hneg
  · refine ⟨1, one_ne_zero, fun v hv => ?_⟩
    obtain ⟨t, ht, htpos⟩ := hpos _ (hne v hv)
    rw [one_mul, ← key, hermTrace_self_of_hermValue ht, map_mul, map_ofNat]
    have : ψ t = Completion.extensionEmbeddingOfIsReal hw t := rfl
    rw [this]
    positivity
  · refine ⟨-1, by norm_num, fun v hv => ?_⟩
    obtain ⟨t, ht, htneg⟩ := hneg _ (hne v hv)
    rw [← key, hermTrace_self_of_hermValue ht, map_mul, map_ofNat]
    have : ψ t = Completion.extensionEmbeddingOfIsReal hw t := rfl
    rw [this]
    linarith

theorem exists_theta_posDef (hdef : ∀ w : InfinitePlace K, ∃ hw : w.IsReal, IsHermDefiniteAt H w hw) :
    ∃ θ : K, ∀ (w : InfinitePlace K) (hw : w.IsReal) (v : ι × κ → ℝ), v ≠ 0 →
      0 < ∑ a, ∑ c, v a * v c * embedding_of_isReal hw (θ * traceGram H b a c) := by
  have hreal : ∀ w : InfinitePlace K, w.IsReal := fun w => (hdef w).1
  choose ε hε hεpos using fun w => exists_sign_traceGram (b := b) (hdef w).1 (hdef w).2
  obtain ⟨θ, hθ⟩ := exists_forall_pos_mul_realEmb hreal ε hε
  refine ⟨θ, fun w hw v hv => ?_⟩
  have h1 := hεpos w v hv
  have h2 := hθ w
  have : ∑ a, ∑ c, v a * v c * embedding_of_isReal hw (θ * traceGram H b a c) =
      realEmb hreal w θ * ∑ a, ∑ c, v a * v c * embedding_of_isReal (hdef w).1 (traceGram H b a c) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [map_mul]
    ring
  rw [this]
  have := mul_pos h1 h2
  nlinarith [sq_nonneg (ε w)]

omit [NumberField K] [Fintype κ] in

theorem traceGram_transpose (hH : IsHermitianFor (conjHom K E) H) :
    (traceGram H b)ᵀ = traceGram H b := by
  ext a c
  exact hermTrace_comm hH _ _

theorem realEmb_mul_hermTrace_pos {θ : K}
    (hθ : ∀ (w : InfinitePlace K) (hw : w.IsReal) (v : ι × κ → ℝ), v ≠ 0 →
      0 < ∑ a, ∑ c, v a * v c * embedding_of_isReal hw (θ * traceGram H b a c))
    {w : InfinitePlace K} (hw : w.IsReal) {x : ι → K ⊗[K] E} (hx : x ≠ 0) :
    0 < embedding_of_isReal hw (θ * hermTrace K H K x x) := by
  have hv : (fun a => embedding_of_isReal hw (vecCoords K b x a)) ≠ 0 := by
    intro h
    apply hx
    rw [← vecOfCoords_vecCoords b K x]
    have : vecCoords K b x = 0 := by
      funext a
      have := congrFun h a
      simpa using this
    rw [this]
    funext i
    simp [vecOfCoords]
  have := hθ w hw _ hv
  convert this using 1
  rw [hermTrace_eq_sum_traceGram (H := H) (b := b) K, Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Algebra.algebraMap_self, RingHom.id_apply]
  simp only [map_mul]
  ring

theorem realEmb_mul_hermTrace_nonneg {θ : K}
    (hθ : ∀ (w : InfinitePlace K) (hw : w.IsReal) (v : ι × κ → ℝ), v ≠ 0 →
      0 < ∑ a, ∑ c, v a * v c * embedding_of_isReal hw (θ * traceGram H b a c))
    {w : InfinitePlace K} (hw : w.IsReal) (x : ι → K ⊗[K] E) :
    0 ≤ embedding_of_isReal hw (θ * hermTrace K H K x x) := by
  by_cases hx : x = 0
  · subst hx
    have : hermTrace K H K (0 : ι → K ⊗[K] E) 0 = 0 := by
      rw [← hermTraceBilin_apply, map_zero]
    rw [this, mul_zero, map_zero]
  · exact (realEmb_mul_hermTrace_pos hθ hw hx).le

variable (H b) in

def ratGram (θ : K) :
    Matrix ((ι × κ) × Free.ChooseBasisIndex ℤ (𝓞 K)) ((ι × κ) × Free.ChooseBasisIndex ℤ (𝓞 K)) ℚ :=
  fun j j' => Algebra.trace ℚ K (θ * integralBasis K j.2 * integralBasis K j'.2 * traceGram H b j.1 j'.1)

omit [Fintype κ] in
theorem ratGram_transpose (hH : IsHermitianFor (conjHom K E) H) (θ : K) :
    (ratGram H b θ)ᵀ = ratGram H b θ := by
  ext j j'
  simp only [transpose_apply, ratGram]
  have := congrFun (congrFun (traceGram_transpose (b := b) hH) j.1) j'.1
  rw [transpose_apply] at this
  rw [this]
  ring_nf

theorem linearIndependent_realEmb_integralBasis (hreal : ∀ w : InfinitePlace K, w.IsReal) :
    LinearIndependent ℝ fun t : Free.ChooseBasisIndex ℤ (𝓞 K) =>
      fun w : {w : InfinitePlace K // w.IsReal} => embedding_of_isReal w.2 (integralBasis K t) := by
  have hli := (mixedEmbedding.latticeBasis K).linearIndependent
  have hker : LinearMap.ker (LinearMap.fst ℝ ({w : InfinitePlace K // w.IsReal} → ℝ)
      ({w : InfinitePlace K // w.IsComplex} → ℂ)) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    rintro ⟨x, y⟩ h
    simp only [LinearMap.fst_apply] at h
    subst h
    have : y = 0 := funext fun w => absurd (hreal w.1) (not_isReal_iff_isComplex.2 w.2)
    rw [this]; rfl
  have := hli.map' _ hker
  have heq : (fun t : Free.ChooseBasisIndex ℤ (𝓞 K) =>
      fun w : {w : InfinitePlace K // w.IsReal} => embedding_of_isReal w.2 (integralBasis K t)) =
      (LinearMap.fst ℝ ({w : InfinitePlace K // w.IsReal} → ℝ)
        ({w : InfinitePlace K // w.IsComplex} → ℂ)) ∘ (mixedEmbedding.latticeBasis K) := by
    funext t w
    simp only [Function.comp_apply, mixedEmbedding.latticeBasis_apply, LinearMap.fst_apply]
    rw [mixedEmbedding.mixedEmbedding_apply_isReal]
  rw [heq]
  exact this

theorem ratGram_posDef (hreal : ∀ w : InfinitePlace K, w.IsReal) {θ : K}
    (hθ : ∀ (w : InfinitePlace K) (hw : w.IsReal) (v : ι × κ → ℝ), v ≠ 0 →
      0 < ∑ a, ∑ c, v a * v c * embedding_of_isReal hw (θ * traceGram H b a c))
    (v : (ι × κ) × Free.ChooseBasisIndex ℤ (𝓞 K) → ℝ) (hv : v ≠ 0) :
    0 < v ⬝ᵥ ((ratGram H b θ).map (Rat.cast : ℚ → ℝ) *ᵥ v) := by
  set ω := integralBasis K
  let u : InfinitePlace K → ι × κ → ℝ := fun w a => ∑ t, v (a, t) * realEmb hreal w (ω t)
  have hexp : v ⬝ᵥ ((ratGram H b θ).map (Rat.cast : ℚ → ℝ) *ᵥ v) =
      ∑ w, ∑ a, ∑ c, u w a * u w c * realEmb hreal w (θ * traceGram H b a c) := by
    simp only [dotProduct, mulVec, Matrix.map_apply, ratGram, trace_eq_sum_realEmb hreal,
      Finset.mul_sum, Finset.sum_mul]
    have step : ∀ f : (ι × κ) × Free.ChooseBasisIndex ℤ (𝓞 K) →
        (ι × κ) × Free.ChooseBasisIndex ℤ (𝓞 K) → InfinitePlace K → ℝ,
        ∑ x, ∑ y, ∑ i, f x y i = ∑ i, ∑ x, ∑ y, f x y i := by
      intro f
      calc ∑ x, ∑ y, ∑ i, f x y i = ∑ x, ∑ i, ∑ y, f x y i :=
            Finset.sum_congr rfl fun x _ => Finset.sum_comm
        _ = ∑ i, ∑ x, ∑ y, f x y i := Finset.sum_comm
    have swap4 : ∀ F : ι × κ → Free.ChooseBasisIndex ℤ (𝓞 K) → ι × κ →
        Free.ChooseBasisIndex ℤ (𝓞 K) → ℝ,
        ∑ a, ∑ t, ∑ c, ∑ t', F a t c t' = ∑ a, ∑ c, ∑ t, ∑ t', F a t c t' :=
      fun F => Finset.sum_congr rfl fun a _ => Finset.sum_comm
    rw [step]
    refine Finset.sum_congr rfl fun w _ => ?_
    simp only [u, Finset.sum_mul, Finset.mul_sum]
    simp only [Fintype.sum_prod_type (α₁ := ι × κ) (α₂ := Free.ChooseBasisIndex ℤ (𝓞 K))]
    have swap2 : ∀ F : Free.ChooseBasisIndex ℤ (𝓞 K) → Free.ChooseBasisIndex ℤ (𝓞 K) → ℝ,
        ∑ t, ∑ t', F t t' = ∑ t', ∑ t, F t t' := fun F => Finset.sum_comm
    rw [swap4]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
    rw [swap2]
    refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun t' _ => ?_
    simp only [map_mul]
    ring
  rw [hexp]
  have hnonneg : ∀ w, 0 ≤ ∑ a, ∑ c, u w a * u w c * realEmb hreal w (θ * traceGram H b a c) := by
    intro w
    by_cases hu : u w = 0
    · simp [hu]
    · exact (hθ w (hreal w) (u w) hu).le
  obtain ⟨w, hw⟩ : ∃ w, u w ≠ 0 := by
    by_contra h
    push Not at h
    apply hv
    funext ⟨a, t⟩
    have hli := linearIndependent_realEmb_integralBasis hreal
    have hsum : (∑ t, v (a, t) • (fun w : {w : InfinitePlace K // w.IsReal} =>
        embedding_of_isReal w.2 (ω t)) : {w : InfinitePlace K // w.IsReal} → ℝ) = 0 := by
      funext w'
      have := congrFun (h w'.1) a
      simpa [u, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using this
    exact Fintype.linearIndependent_iff.1 hli (fun t => v (a, t)) hsum t
  calc 0 < ∑ a, ∑ c, u w a * u w c * realEmb hreal w (θ * traceGram H b a c) := hθ w (hreal w) (u w) hw
    _ ≤ _ := Finset.single_le_sum (fun w _ => hnonneg w) (Finset.mem_univ w)

end Form

end GroundTheory.Automorphic
