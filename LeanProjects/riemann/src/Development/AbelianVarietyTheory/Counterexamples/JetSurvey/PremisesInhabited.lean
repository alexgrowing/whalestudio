import Mathlib

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.LatticeBoundTests
open NumberField

theorem integral_of_sum (Y : Type) [AddCommGroup Y] (S : Submodule ℝ (Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ))
    (l : S →ₗ[ℝ] ℝ) (m : ℕ) (x x' : Fin m → Y)
    (h : ∀ β : S, l β = ∑ i, (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (x i) (x' i)) (β : S)
    (hβ : ∀ a c, ∃ z : ℤ, (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) a c = z) : ∃ z : ℤ, l β = z := by
  choose f hf using hβ
  refine ⟨∑ i, f (x i) (x' i), ?_⟩
  rw [h]; push_cast
  exact Finset.sum_congr rfl fun i _ => hf _ _

section Trace
variable (E : Type) [Field E] [NumberField E] [IsCMField E]

def trBil : 𝓞 E →ₗ[ℤ] 𝓞 E →ₗ[ℤ] ℝ :=
  LinearMap.mk₂ ℤ (fun x y => ∑ σ : E →+* ℂ, (σ (x : E) * starRingEnd ℂ (σ (y : E))).re)
    (fun x x' y => by simp [add_mul, Finset.sum_add_distrib])
    (fun k x y => by simp [Finset.mul_sum, mul_assoc, mul_add])
    (fun x y y' => by simp [mul_add, Finset.sum_add_distrib])
    (fun k x y => by simp [Finset.mul_sum, mul_add, mul_left_comm])

omit [IsCMField E] in
theorem trBil_apply (x y : 𝓞 E) :
    trBil E x y = ∑ σ : E →+* ℂ, (σ (x : E) * starRingEnd ℂ (σ (y : E))).re := rfl

omit [IsCMField E] in
theorem trBil_symm (x y : 𝓞 E) : trBil E x y = trBil E y x := by
  rw [trBil_apply, trBil_apply]
  exact Finset.sum_congr rfl fun σ _ => by simp [mul_comm]

theorem trBil_balanced (c c' : 𝓞 E) (hc : (c' : E) = IsCMField.complexConj E c) (x y : 𝓞 E) :
    trBil E (c • x) y = trBil E x (c' • y) := by
  rw [trBil_apply, trBil_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have h : σ (c' : E) = starRingEnd ℂ (σ (c : E)) := by
    rw [hc]; exact IsCMField.complexEmbedding_complexConj E σ _
  rw [smul_eq_mul, smul_eq_mul]
  push_cast
  rw [map_mul, map_mul, h, map_mul, Complex.conj_conj]
  congr 1; ring

omit [IsCMField E] in
theorem trBil_posDef :
    (Matrix.of fun i j => trBil E (RingOfIntegers.basis E i) (RingOfIntegers.basis E j)).PosDef := by
  classical
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ fun t ht => ?_
  · ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.of_apply, star_trivial, trBil_apply]
    exact Finset.sum_congr rfl fun σ _ => by simp [mul_comm]
  · set u : (E →+* ℂ) → ℂ := fun σ => ∑ i, (t i : ℂ) * σ (RingOfIntegers.basis E i : E) with hu
    have key : star t ⬝ᵥ (Matrix.of fun i j => trBil E (RingOfIntegers.basis E i)
        (RingOfIntegers.basis E j)).mulVec t = ∑ σ, Complex.normSq (u σ) := by
      have : ∀ σ, Complex.normSq (u σ) = ∑ i, ∑ j, t i * ((σ (RingOfIntegers.basis E i : E) *
          starRingEnd ℂ (σ (RingOfIntegers.basis E j : E))).re * t j) := by
        intro σ
        rw [← Complex.ofReal_re (Complex.normSq (u σ)), ← Complex.mul_conj, hu]
        simp only [map_sum, Finset.sum_mul_sum, Complex.re_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        simp; ring
      simp only [this, dotProduct, Matrix.mulVec, Matrix.of_apply, trBil_apply, star_trivial,
        Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm (γ := E →+* ℂ)]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_comm (γ := E →+* ℂ)]
    rw [key]
    refine lt_of_le_of_ne (Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _) fun h0 => ht ?_
    have hz : ∀ σ, u σ = 0 := fun σ => Complex.normSq_eq_zero.1
      ((Finset.sum_eq_zero_iff_of_nonneg fun _ _ => Complex.normSq_nonneg _).1 h0.symm σ
        (Finset.mem_univ _))
    have li := Fintype.linearIndependent_iff.1 (canonicalEmbedding.latticeBasis E).linearIndependent
      (fun i => (t i : ℂ)) (by
        funext σ
        have := hz σ
        simpa [hu, canonicalEmbedding.latticeBasis_apply, integralBasis_apply] using this)
    funext i
    exact_mod_cast li i

end Trace

abbrev K₃ := CyclotomicField 3 ℚ

instance isCyc_K₃ : IsCyclotomicExtension {3} ℚ K₃ := CyclotomicField.isCyclotomicExtension 3 ℚ

instance isCMField_K₃ : IsCMField K₃ := IsCyclotomicExtension.Rat.isCMField K₃ (S := {3}) ⟨3, rfl, by norm_num⟩

theorem exists_half : ∃ w : 𝓞 K₃, (w : K₃) + IsCMField.complexConj K₃ w = 1 := by
  have hζ := IsCyclotomicExtension.zeta_spec 3 ℚ K₃
  set ζ := IsCyclotomicExtension.zeta 3 ℚ K₃
  refine ⟨-hζ.toInteger, ?_⟩
  have h3 : ζ ^ 3 = 1 := hζ.pow_eq_one
  have hs : 1 + ζ + ζ ^ 2 = 0 := by
    have := hζ.geom_sum_eq_zero (by norm_num)
    simpa [Finset.sum_range_succ] using this
  obtain ⟨σ⟩ : Nonempty (K₃ →+* ℂ) := inferInstance
  have hc : IsCMField.complexConj K₃ ζ = ζ ^ 2 := by
    apply σ.injective
    rw [IsCMField.complexEmbedding_complexConj, map_pow]
    have h1 : σ ζ ^ 3 = 1 := by rw [← map_pow, h3, map_one]
    have hn : ‖σ ζ‖ = 1 := Complex.norm_eq_one_of_pow_eq_one h1 (by norm_num)
    have hne : σ ζ ≠ 0 := by intro h; simp [h] at hn
    apply mul_left_cancel₀ hne
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hn]
    push_cast
    linear_combination -h1
  have e : ((-hζ.toInteger : 𝓞 K₃) : K₃) = -ζ := by push_cast; rfl
  rw [e, map_neg, hc]
  linear_combination -hs

theorem premises_inhabited :
    ∃ (E : Type) (_ : Field E) (_ : NumberField E) (cj : E → E) (w : 𝓞 E) (Y : Type)
      (_ : AddCommGroup Y) (_ : Module (𝓞 E) Y) (_ : Module.Free ℤ Y) (_ : Module.Finite ℤ Y)
      (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ),
      (∀ (φ : E →+* ℂ) (z : E), φ (cj z) = star (φ z)) ∧ (∃ z, cj z ≠ z) ∧
      (∀ c : 𝓞 E, ∃ c' : 𝓞 E, (c' : E) = cj c) ∧ (w : E) + cj w = 1 ∧
      0 < Module.finrank ℤ Y ∧ (∀ x y, β x y = β y x) ∧
      (∀ c c' : 𝓞 E, (c' : E) = cj c → ∀ x y, β (c • x) y = β x (c' • y)) ∧
      ∃ (ι : Type) (_ : Fintype ι) (b : Module.Basis ι ℤ Y),
        (Matrix.of fun i j => β (b i) (b j)).PosDef := by
  obtain ⟨w, hw⟩ := exists_half
  refine ⟨K₃, inferInstance, inferInstance, fun z => IsCMField.complexConj K₃ z, w, 𝓞 K₃,
    inferInstance, inferInstance, inferInstance, inferInstance, trBil K₃,
    fun φ z => IsCMField.complexEmbedding_complexConj K₃ φ z, ?_,
    fun c => ⟨IsCMField.ringOfIntegersComplexConj K₃ c,
      IsCMField.coe_ringOfIntegersComplexConj K₃ c⟩, hw, Module.finrank_pos, trBil_symm K₃,
    trBil_balanced K₃, _, inferInstance, RingOfIntegers.basis K₃, trBil_posDef K₃⟩
  by_contra h
  push_neg at h
  exact IsCMField.complexConj_ne_one K₃ (AlgEquiv.ext h)

end GlobalTheory.LatticeBoundTests
