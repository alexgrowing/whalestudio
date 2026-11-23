import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1

open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors

namespace GlobalTheory.AdLat

section

variable (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem adele_mul_integral {a b : FiniteAdeleRing (𝓞 F) F} {v : HeightOneSpectrum (𝓞 F)}
    (ha : a v ∈ v.adicCompletionIntegers F) (hb : b v ∈ v.adicCompletionIntegers F) :
    (a * b) v ∈ v.adicCompletionIntegers F := by
  have : (a * b) v = a v * b v := RestrictedProduct.mul_apply _ a b v
  rw [this]; exact mul_mem ha hb

theorem adele_add_integral {a b : FiniteAdeleRing (𝓞 F) F} {v : HeightOneSpectrum (𝓞 F)}
    (ha : a v ∈ v.adicCompletionIntegers F) (hb : b v ∈ v.adicCompletionIntegers F) :
    (a + b) v ∈ v.adicCompletionIntegers F := by
  have : (a + b) v = a v + b v := RestrictedProduct.add_apply _ a b v
  rw [this]; exact add_mem ha hb

theorem adele_neg_integral {a : FiniteAdeleRing (𝓞 F) F} {v : HeightOneSpectrum (𝓞 F)}
    (ha : a v ∈ v.adicCompletionIntegers F) :
    (-a) v ∈ v.adicCompletionIntegers F := by
  have : (-a) v = -a v := RestrictedProduct.neg_apply _ a v
  rw [this]; exact neg_mem ha

theorem adele_one_integral (v : HeightOneSpectrum (𝓞 F)) :
    (1 : FiniteAdeleRing (𝓞 F) F) v ∈ v.adicCompletionIntegers F := by
  have : (1 : FiniteAdeleRing (𝓞 F) F) v = 1 := RestrictedProduct.one_apply _ _
  rw [this]; exact one_mem _

theorem adele_zero_integral (v : HeightOneSpectrum (𝓞 F)) :
    (0 : FiniteAdeleRing (𝓞 F) F) v ∈ v.adicCompletionIntegers F := by
  have : (0 : FiniteAdeleRing (𝓞 F) F) v = 0 := RestrictedProduct.zero_apply _ _
  rw [this]; exact zero_mem _

theorem tmul_mem_adelicCompletion_of_integral {J : Set E} {a : FiniteAdeleRing (𝓞 F) F}
    (ha : ∀ v, a v ∈ v.adicCompletionIntegers F) {x : E} (hx : x ∈ J) :
    a ⊗ₜ[F] x ∈ hat1 F J :=
  AddSubgroup.subset_closure ⟨a, ha, x, hx, rfl⟩

theorem one_tmul_mem_adelicCompletionOfElementSet {J : Set E} {x : E} (hx : x ∈ J) :
    (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x ∈ hat1 F J :=
  tmul_mem_adelicCompletion_of_integral F (adele_one_integral F) hx

theorem mul_mem_adelicCompletionOfElementSet_of_mul_mem {I J K : Set E} (h : ∀ x ∈ I, ∀ y ∈ J, x * y ∈ K)
    {x y : RA F E} (hx : x ∈ hat1 F I) (hy : y ∈ hat1 F J) : x * y ∈ hat1 F K := by
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hx
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨b, hb, y, hy, rfl⟩ := hy
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      exact tmul_mem_adelicCompletion_of_integral F (fun v => adele_mul_integral F (ha v) (hb v))
        (h x hx y hy)
    | zero => rw [mul_zero]; exact zero_mem _
    | add y z _ _ h1 h2 => rw [mul_add]; exact add_mem h1 h2
    | neg y _ h1 => rw [mul_neg]; exact neg_mem h1
  | zero => rw [zero_mul]; exact zero_mem _
  | add y z _ _ h1 h2 => rw [add_mul]; exact add_mem h1 h2
  | neg y _ h1 => rw [neg_mul]; exact neg_mem h1

theorem galoisAut_mem_adelicCompletionOfElementSet (c : E ≃ₐ[F] E) {I J : Set E} (h : ∀ x ∈ I, c x ∈ J)
    {z : RA F E} (hz : z ∈ hat1 F I) : sg (FiniteAdeleRing (𝓞 F) F) c z ∈ hat1 F J := by
  induction hz using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hx
    exact tmul_mem_adelicCompletion_of_integral F ha (h x hx)
  | zero => rw [map_zero]; exact zero_mem _
  | add y z _ _ h1 h2 => rw [map_add]; exact add_mem h1 h2
  | neg y _ h1 => rw [map_neg]; exact neg_mem h1

theorem mem_range_iff_adele_integral (x : F) :
    x ∈ (algebraMap (𝓞 F) F).range ↔
      ∀ v, algebraMap F (FiniteAdeleRing (𝓞 F) F) x v ∈ v.adicCompletionIntegers F := by
  simp only [FiniteAdeleRing.algebraMap_apply, HeightOneSpectrum.mem_adicCompletionIntegers,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  constructor
  · rintro ⟨a, rfl⟩ v
    exact v.valuation_le_one a
  · exact HeightOneSpectrum.mem_integers_of_valuation_le_one F x

theorem linearForm_integral_of_one_tmul_mem_adelicCompletion {I : Set E} (t : E →ₗ[F] F)
    (ht : ∀ y ∈ I, t y ∈ (algebraMap (𝓞 F) F).range) {x : E}
    (hx : (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x ∈ hat1 F I) :
    t x ∈ (algebraMap (𝓞 F) F).range := by
  let T : RA F E →ₗ[F] FiniteAdeleRing (𝓞 F) F :=
    (TensorProduct.rid F _).toLinearMap ∘ₗ LinearMap.lTensor _ t
  have hT : ∀ a y, T (a ⊗ₜ[F] y) = algebraMap F _ (t y) * a := by
    intro a y
    simp [T, Algebra.smul_def]
  have key : ∀ z ∈ hat1 F I, ∀ v, T z v ∈ v.adicCompletionIntegers F := by
    intro z hz v
    induction hz using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨a, ha, y, hy, rfl⟩ := hx
      rw [hT]
      exact adele_mul_integral F
        ((mem_range_iff_adele_integral F _).1 (ht y hy) v) (ha v)
    | zero => rw [map_zero]; exact adele_zero_integral F v
    | add y z _ _ h1 h2 => rw [map_add]; exact adele_add_integral F h1 h2
    | neg y _ h1 => rw [map_neg]; exact adele_neg_integral F h1
  rw [mem_range_iff_adele_integral]
  have := key _ hx
  rwa [hT, mul_one] at this

variable [NumberField E]

theorem one_tmul_mem_adelicCompletion_fractionalIdeal_iff (I : FractionalIdeal (𝓞 E)⁰ E) (x : E) :
    (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x ∈ hat1 F (I : Set E) ↔ x ∈ I := by
  refine ⟨fun hx => ?_, fun hx => one_tmul_mem_adelicCompletionOfElementSet F hx⟩
  by_cases hI : I = 0
  · subst hI
    rw [FractionalIdeal.mem_zero_iff]
    by_contra h0
    obtain ⟨t, ht⟩ := Module.Projective.exists_dual_eq_one F h0
    apply RingOfIntegers.not_isField F
    rw [← IsFractionRing.surjective_iff_isField (K := F)]
    intro c
    have := linearForm_integral_of_one_tmul_mem_adelicCompletion F (c • t) (fun y hy => by
      have hy' : y = 0 := (FractionalIdeal.mem_zero_iff _).1 hy
      rw [hy', map_zero]; exact zero_mem _) hx
    simpa [ht] using this
  · rw [← FractionalIdeal.dual_dual (𝓞 F) F I,
      FractionalIdeal.mem_dual (FractionalIdeal.dual_ne_zero _ _ hI)]
    intro y hy
    rw [FractionalIdeal.mem_dual hI] at hy
    have := linearForm_integral_of_one_tmul_mem_adelicCompletion F (Algebra.traceForm F E y) hy hx
    rwa [Algebra.traceForm_apply, mul_comm] at this

theorem mem_adelicCompletion_mul_inv_fractionalIdeal (I J : FractionalIdeal (𝓞 E)⁰ E) (z : RA F E) (hI : I ≠ 0)
    (h : ∀ x ∈ I, z * ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x) ∈ hat1 F (J : Set E)) :
    z ∈ hat1 F ((J * I⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Set E) := by
  have h1 : (1 : E) ∈ I * I⁻¹ := by
    rw [mul_inv_cancel₀ hI]; exact FractionalIdeal.one_mem_one _
  have key : ∀ w ∈ I * I⁻¹, z * ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] w) ∈
      hat1 F ((J * I⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Set E) := by
    intro w hw
    refine FractionalIdeal.mul_induction_on hw (fun x hx y hy => ?_) (fun x y hx hy => ?_)
    · have := mul_mem_adelicCompletionOfElementSet_of_mul_mem F (K := ((J * I⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Set E))
        (fun a ha b hb => FractionalIdeal.mul_mem_mul ha hb) (h x hx) (one_tmul_mem_adelicCompletionOfElementSet F hy)
      rwa [mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, mul_one] at this
    · rw [TensorProduct.tmul_add, mul_add]; exact add_mem hx hy
  have := key 1 h1
  rwa [← Algebra.TensorProduct.one_def, mul_one] at this

end

theorem adelicCompletion_fractionalIdeal_properties : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], (∀ I J : FractionalIdeal (𝓞 E)⁰ E, ∀ x ∈ hat1 F (I : Set E), ∀ y ∈ hat1 F (J : Set E), x * y ∈ hat1 F ((I * J : FractionalIdeal (𝓞 E)⁰ E) : Set E)) ∧ (∀ (I : FractionalIdeal (𝓞 E)⁰ E) (x : E), (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x ∈ hat1 F (I : Set E) ↔ x ∈ I) ∧ (∀ (I J : FractionalIdeal (𝓞 E)⁰ E) (z : RA F E), I ≠ 0 → (∀ x ∈ I, z * ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x) ∈ hat1 F (J : Set E)) → z ∈ hat1 F ((J * I⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Set E)) ∧ ∀ (c : E ≃ₐ[F] E) (I I' : FractionalIdeal (𝓞 E)⁰ E), (∀ x ∈ I, c x ∈ I') → ∀ z ∈ hat1 F (I : Set E), sg (FiniteAdeleRing (𝓞 F) F) c z ∈ hat1 F (I' : Set E) := by
  intro F E _ _ _ _ _
  exact ⟨fun I J x hx y hy => mul_mem_adelicCompletionOfElementSet_of_mul_mem F
      (fun a ha b hb => FractionalIdeal.mul_mem_mul ha hb) hx hy,
    one_tmul_mem_adelicCompletion_fractionalIdeal_iff F, mem_adelicCompletion_mul_inv_fractionalIdeal F, fun c I I' h z hz => galoisAut_mem_adelicCompletionOfElementSet F c h hz⟩

end GlobalTheory.AdLat
