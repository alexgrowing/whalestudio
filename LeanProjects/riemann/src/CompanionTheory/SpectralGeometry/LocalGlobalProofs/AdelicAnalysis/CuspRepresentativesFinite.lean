import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

namespace GlobalTheory.CompanionTheory.SW.Core.RowCompletion

open nonZeroDivisors

variable {F : Type} [Field F] [NumberField F]

def Adapted (A : FractionalIdeal (𝓞 F)⁰ F) (g : SL(2, F)) : Prop :=
  g 0 0 ∈ A⁻¹ ∧ g 0 1 ∈ A⁻¹ ∧ g 1 0 ∈ A ∧ g 1 1 ∈ A

theorem integral_of_mem {A : FractionalIdeal (𝓞 F)⁰ F} (hA : A ≠ 0) {x y : F} (hx : x ∈ A)
    (hy : y ∈ A⁻¹) : ∃ z : 𝓞 F, (z : F) = x * y := by
  have h : x * y ∈ A * A⁻¹ := FractionalIdeal.mul_mem_mul hx hy
  rw [mul_inv_cancel₀ hA, FractionalIdeal.mem_one_iff] at h
  exact h

theorem exists_bezout {A : FractionalIdeal (𝓞 F)⁰ F} (hA : A ≠ 0) {p q : F}
    (h : A = FractionalIdeal.spanSingleton _ p + FractionalIdeal.spanSingleton _ q) :
    ∃ a ∈ A⁻¹, ∃ b ∈ A⁻¹, a * q - b * p = 1 := by
  have h1 : (1 : F) ∈ A * A⁻¹ := by
    rw [mul_inv_cancel₀ hA]
    exact (FractionalIdeal.mem_one_iff _).2 ⟨1, by simp⟩
  have h2 : A * A⁻¹ = FractionalIdeal.spanSingleton _ p * A⁻¹ +
      FractionalIdeal.spanSingleton _ q * A⁻¹ := by
    calc A * A⁻¹ = (FractionalIdeal.spanSingleton _ p + FractionalIdeal.spanSingleton _ q) * A⁻¹ := by
          rw [← h]
      _ = _ := add_mul _ _ _
  rw [h2, ← FractionalIdeal.mem_coe, FractionalIdeal.coe_add, Submodule.add_eq_sup,
    Submodule.mem_sup] at h1
  obtain ⟨s, hs, t, ht, hst⟩ := h1
  obtain ⟨s', hs', rfl⟩ := FractionalIdeal.mem_singleton_mul.1 (FractionalIdeal.mem_coe.1 hs)
  obtain ⟨t', ht', rfl⟩ := FractionalIdeal.mem_singleton_mul.1 (FractionalIdeal.mem_coe.1 ht)
  refine ⟨t', ht', -s', ?_, ?_⟩
  · exact FractionalIdeal.mem_coe.1 (neg_mem (FractionalIdeal.mem_coe.2 hs'))
  · linear_combination hst

theorem exists_adapted {A : FractionalIdeal (𝓞 F)⁰ F} (hA : A ≠ 0) {p q : F}
    (h : A = FractionalIdeal.spanSingleton _ p + FractionalIdeal.spanSingleton _ q) :
    ∃ g : SL(2, F), Adapted A g ∧ g 1 0 = p ∧ g 1 1 = q := by
  obtain ⟨a, ha, b, hb, hab⟩ := exists_bezout hA h
  have hp : p ∈ A := by
    rw [h, ← FractionalIdeal.mem_coe, FractionalIdeal.coe_add, Submodule.add_eq_sup]
    exact Submodule.mem_sup_left (FractionalIdeal.mem_coe.2
      (FractionalIdeal.mem_spanSingleton_self _ _))
  have hq : q ∈ A := by
    rw [h, ← FractionalIdeal.mem_coe, FractionalIdeal.coe_add, Submodule.add_eq_sup]
    exact Submodule.mem_sup_right (FractionalIdeal.mem_coe.2
      (FractionalIdeal.mem_spanSingleton_self _ _))
  refine ⟨⟨!![a, b; p, q], by simpa [Matrix.det_fin_two] using hab⟩, ?_, by simp, by simp⟩
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simpa

theorem integral_inv_mul {A : FractionalIdeal (𝓞 F)⁰ F} (hA : A ≠ 0) {r g : SL(2, F)}
    (hr : Adapted A r) (hg : Adapted A g) (i j : Fin 2) :
    ∃ z : 𝓞 F, (z : F) = (r⁻¹ * g) i j := by
  obtain ⟨r0, r1, r2, r3⟩ := hr
  obtain ⟨g0, g1, g2, g3⟩ := hg
  obtain ⟨z1, e1⟩ := integral_of_mem hA r3 g0
  obtain ⟨z2, e2⟩ := integral_of_mem hA r3 g1
  obtain ⟨z3, e3⟩ := integral_of_mem hA r2 g0
  obtain ⟨z4, e4⟩ := integral_of_mem hA r2 g1
  obtain ⟨z5, e5⟩ := integral_of_mem hA g2 r1
  obtain ⟨z6, e6⟩ := integral_of_mem hA g3 r1
  obtain ⟨z7, e7⟩ := integral_of_mem hA g2 r0
  obtain ⟨z8, e8⟩ := integral_of_mem hA g3 r0
  have hinv : ((r⁻¹ * g : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
      !![r 1 1, -r 0 1; -r 1 0, r 0 0] * (g : Matrix (Fin 2) (Fin 2) F) := by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.SL2_inv_expl]
    rfl
  rw [hinv]
  fin_cases i <;> fin_cases j
  · refine ⟨z1 - z5, ?_⟩
    simp only [map_sub, RingOfIntegers.map_mk, Matrix.mul_apply, Fin.sum_univ_two]
    push_cast [e1, e5]
    simp
    ring
  · refine ⟨z2 - z6, ?_⟩
    push_cast [e2, e6]
    simp [Matrix.mul_apply, Fin.sum_univ_two]
    ring
  · refine ⟨z7 - z3, ?_⟩
    push_cast [e7, e3]
    simp [Matrix.mul_apply, Fin.sum_univ_two]
    ring
  · refine ⟨z8 - z4, ?_⟩
    push_cast [e8, e4]
    simp [Matrix.mul_apply, Fin.sum_univ_two]
    ring

theorem exists_scale (J I : (Ideal (𝓞 F))⁰) (h : ClassGroup.mk0 I = ClassGroup.mk0 J)
    {c d : 𝓞 F} (hI : (I : Ideal (𝓞 F)) = Ideal.span {c, d}) :
    ∃ l : F, l ≠ 0 ∧ |((Algebra.norm ℚ l : ℚ) : ℝ)| ≤ (Ideal.absNorm (J : Ideal (𝓞 F)) : ℝ) ∧
      ((J : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) =
        FractionalIdeal.spanSingleton _ (l * (c : F)) +
          FractionalIdeal.spanSingleton _ (l * (d : F)) := by
  obtain ⟨x, y, hx, hy, hxy⟩ := ClassGroup.mk0_eq_mk0_iff.1 h
  have hxF : (x : F) ≠ 0 := by simpa using hx
  have hyF : (y : F) ≠ 0 := by simpa using hy
  refine ⟨(x : F) / (y : F), div_ne_zero hxF hyF, ?_, ?_⟩
  · have hn := congrArg Ideal.absNorm hxy
    rw [map_mul, map_mul, Ideal.absNorm_span_singleton, Ideal.absNorm_span_singleton] at hn
    have key : ∀ w : 𝓞 F, (((Algebra.norm ℤ w).natAbs : ℕ) : ℝ) =
        |((Algebra.norm ℚ (w : F) : ℚ) : ℝ)| := by
      intro w
      rw [← Algebra.coe_norm_int]
      simp [Nat.cast_natAbs]
    have hmul : Algebra.norm ℚ (x : F) = Algebra.norm ℚ (y : F) * Algebra.norm ℚ ((x : F) / (y : F)) := by
      rw [← map_mul, mul_div_cancel₀ _ hyF]
    have hnR : (((Algebra.norm ℤ x).natAbs : ℕ) : ℝ) * (Ideal.absNorm (I : Ideal (𝓞 F)) : ℝ) =
        (((Algebra.norm ℤ y).natAbs : ℕ) : ℝ) * (Ideal.absNorm (J : Ideal (𝓞 F)) : ℝ) := by
      exact_mod_cast hn
    rw [key, key, hmul] at hnR
    have hb : |((Algebra.norm ℚ (y : F) : ℚ) : ℝ)| ≠ 0 := by
      have : Algebra.norm ℚ (y : F) ≠ 0 := Algebra.norm_ne_zero_iff.2 hyF
      simpa using this
    have hI1 : (1 : ℝ) ≤ (Ideal.absNorm (I : Ideal (𝓞 F)) : ℝ) := by
      have : Ideal.absNorm (I : Ideal (𝓞 F)) ≠ 0 := by
        rw [Ne, Ideal.absNorm_eq_zero_iff]
        exact nonZeroDivisors.ne_zero I.2
      exact_mod_cast Nat.one_le_iff_ne_zero.2 this
    set t := |((Algebra.norm ℚ ((x : F) / (y : F)) : ℚ) : ℝ)| with ht
    have h3 : t * (Ideal.absNorm (I : Ideal (𝓞 F)) : ℝ) = (Ideal.absNorm (J : Ideal (𝓞 F)) : ℝ) := by
      apply mul_left_cancel₀ hb
      rw [← hnR]
      push_cast
      rw [abs_mul]
      ring
    have ht0 : 0 ≤ t := abs_nonneg _
    calc t = t * 1 := (mul_one t).symm
      _ ≤ t * (Ideal.absNorm (I : Ideal (𝓞 F)) : ℝ) := mul_le_mul_of_nonneg_left hI1 ht0
      _ = _ := h3
  · have hF := congrArg (fun K : Ideal (𝓞 F) => (K : FractionalIdeal (𝓞 F)⁰ F)) hxy
    simp only [FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_span_singleton] at hF
    rw [hI, Ideal.span_insert, FractionalIdeal.coeIdeal_sup,
      FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.coeIdeal_span_singleton] at hF
    simp only [← RingOfIntegers.coe_eq_algebraMap] at hF
    calc ((J : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F)
        = FractionalIdeal.spanSingleton _ (y : F)⁻¹ * (FractionalIdeal.spanSingleton _ (y : F) *
            ((J : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F)) := by
          rw [← mul_assoc, FractionalIdeal.spanSingleton_mul_spanSingleton, inv_mul_cancel₀ hyF,
            FractionalIdeal.spanSingleton_one, one_mul]
      _ = FractionalIdeal.spanSingleton _ (y : F)⁻¹ * (FractionalIdeal.spanSingleton _ (x : F) *
            (FractionalIdeal.spanSingleton _ (c : F) + FractionalIdeal.spanSingleton _ (d : F))) := by
          rw [hF]
      _ = _ := by
          simp only [mul_add, FractionalIdeal.spanSingleton_mul_spanSingleton]
          congr 2 <;> field_simp

end GlobalTheory.CompanionTheory.SW.Core.RowCompletion

open nonZeroDivisors GlobalTheory.CompanionTheory.SW.Core.RowCompletion in

theorem GlobalTheory.CompanionTheory.SW.Core.exists_finset_row_completion :
    ∀ (F : Type) [Field F] [NumberField F], ∃ (s : Finset SL(2, F)) (C : ℝ), ∀ c d : 𝓞 F, (c ≠ 0 ∨ d ≠ 0) → ∃ l : F, l ≠ 0 ∧ |((Algebra.norm ℚ l : ℚ) : ℝ)| ≤ C ∧ ∀ u : (𝓞 F)ˣ, ∃ r ∈ s, ∃ k : SL(2, F), (∀ i j, ∃ z : 𝓞 F, (z : F) = k i j) ∧ (r * k) 1 0 = ((u : 𝓞 F) : F) * l * (c : F) ∧ (r * k) 1 1 = ((u : 𝓞 F) : F) * l * (d : F) := by
  intro F _ _
  classical
  let J : ClassGroup (𝓞 F) → (Ideal (𝓞 F))⁰ := fun g => (ClassGroup.mk0_surjective g).choose
  have hJ : ∀ g, ClassGroup.mk0 (J g) = g := fun g => (ClassGroup.mk0_surjective g).choose_spec
  let A : ClassGroup (𝓞 F) → FractionalIdeal (𝓞 F)⁰ F :=
    fun g => ((J g : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F)
  have hA : ∀ g, A g ≠ 0 := by
    intro g
    simpa [A] using nonZeroDivisors.ne_zero (J g).2
  let r : ClassGroup (𝓞 F) → SL(2, F) := fun g =>
    if h : ∃ r, Adapted (A g) r then h.choose else 1
  have hr : ∀ g, (∃ r, Adapted (A g) r) → Adapted (A g) (r g) := by
    intro g h
    simp only [r, dif_pos h]
    exact h.choose_spec
  refine ⟨Finset.univ.image r, ∑ g, (Ideal.absNorm (J g : Ideal (𝓞 F)) : ℝ), ?_⟩
  intro c d hcd
  have hI : Ideal.span {c, d} ∈ (Ideal (𝓞 F))⁰ := by
    refine mem_nonZeroDivisors_of_ne_zero ?_
    intro h0
    have h1 : c ∈ Ideal.span {c, d} := Ideal.subset_span (by simp)
    have h2 : d ∈ Ideal.span {c, d} := Ideal.subset_span (by simp)
    rw [h0] at h1 h2
    rcases hcd with h | h
    · exact h (by simpa using h1)
    · exact h (by simpa using h2)
  let g := ClassGroup.mk0 ⟨Ideal.span {c, d}, hI⟩
  obtain ⟨l, hl0, hln, hlA⟩ := exists_scale (F := F) (J g) ⟨Ideal.span {c, d}, hI⟩ (hJ g).symm rfl
  refine ⟨l, hl0, hln.trans ?_, ?_⟩
  · exact Finset.single_le_sum (f := fun g => (Ideal.absNorm (J g : Ideal (𝓞 F)) : ℝ))
      (fun _ _ => by positivity) (Finset.mem_univ g)
  intro u
  have hu : FractionalIdeal.spanSingleton (𝓞 F)⁰ ((u : 𝓞 F) : F) = 1 := by
    have := FractionalIdeal.coeIdeal_span_singleton (S := (𝓞 F)⁰) (P := F) (u : 𝓞 F)
    rw [Ideal.span_singleton_eq_top.2 u.isUnit] at this
    simpa using this.symm
  have hAu : A g = FractionalIdeal.spanSingleton _ (((u : 𝓞 F) : F) * l * (c : F)) +
      FractionalIdeal.spanSingleton _ (((u : 𝓞 F) : F) * l * (d : F)) := by
    have : A g = FractionalIdeal.spanSingleton (𝓞 F)⁰ ((u : 𝓞 F) : F) * A g := by rw [hu, one_mul]
    rw [this]
    change _ * ((J g : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) = _
    rw [hlA, mul_add, FractionalIdeal.spanSingleton_mul_spanSingleton,
      FractionalIdeal.spanSingleton_mul_spanSingleton, mul_assoc, mul_assoc]
  obtain ⟨γ, hγ, h10, h11⟩ := exists_adapted (hA g) hAu
  have hrg := hr g ⟨γ, hγ⟩
  refine ⟨r g, Finset.mem_image_of_mem _ (Finset.mem_univ g), (r g)⁻¹ * γ,
    integral_inv_mul (hA g) hrg hγ, ?_, ?_⟩
  · rw [mul_inv_cancel_left]; exact h10
  · rw [mul_inv_cancel_left]; exact h11
