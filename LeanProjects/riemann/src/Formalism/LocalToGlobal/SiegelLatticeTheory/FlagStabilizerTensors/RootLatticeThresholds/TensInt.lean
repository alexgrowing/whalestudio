import Mathlib

noncomputable section

open MeasureTheory
open scoped InnerProductSpace

namespace Formalism.L2.SG.Pf.WuDec

section Tens

variable {ι : Type} [Fintype ι] {V : ι → Type} [∀ v, NormedAddCommGroup (V v)] [∀ v, InnerProductSpace ℂ (V v)]
  {Vπ : Type} [NormedAddCommGroup Vπ] [InnerProductSpace ℂ Vπ] {tens : (∀ v, V v) → Vπ}

theorem norm_tens (hi : ∀ x y, ⟪tens x, tens y⟫_ℂ = ∏ v, ⟪x v, y v⟫_ℂ) (x : ∀ v, V v) :
    ‖tens x‖ = ∏ v, ‖x v‖ := by
  have h := hi x x
  simp_rw [inner_self_eq_norm_sq_to_K] at h
  have h2 : ‖tens x‖ ^ 2 = (∏ v, ‖x v‖) ^ 2 := by
    rw [← Finset.prod_pow]
    exact_mod_cast h
  rw [← Real.sqrt_sq (norm_nonneg (tens x)), h2,
    Real.sqrt_sq (Finset.prod_nonneg fun v _ => norm_nonneg (x v))]

theorem norm_sub_tens_sq (hi : ∀ x y, ⟪tens x, tens y⟫_ℂ = ∏ v, ⟪x v, y v⟫_ℂ) (x y : ∀ v, V v) :
    ‖tens x - tens y‖ ^ 2 = RCLike.re ((∏ v, ⟪x v, x v⟫_ℂ) - (∏ v, ⟪x v, y v⟫_ℂ) - (∏ v, ⟪y v, x v⟫_ℂ) +
      (∏ v, ⟪y v, y v⟫_ℂ)) := by
  have e := inner_self_eq_norm_sq (𝕜 := ℂ) (tens x - tens y)
  rw [← e, inner_sub_left, inner_sub_right, inner_sub_right, hi, hi, hi, hi]
  congr 1
  ring

theorem continuous_tens [∀ v, FiniteDimensional ℂ (V v)] (hi : ∀ x y, ⟪tens x, tens y⟫_ℂ = ∏ v, ⟪x v, y v⟫_ℂ) :
    Continuous tens := by
  rw [continuous_iff_continuousAt]
  intro x
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have p : ∀ v, Continuous fun y : (∀ v, V v) => y v := fun v => _root_.continuous_apply v
  have hF : Continuous fun y : (∀ v, V v) => RCLike.re ((∏ v, ⟪y v, y v⟫_ℂ) - (∏ v, ⟪y v, x v⟫_ℂ) -
      (∏ v, ⟪x v, y v⟫_ℂ) + (∏ v, ⟪x v, x v⟫_ℂ)) := by
    refine RCLike.continuous_re.comp
      (Continuous.add (Continuous.sub (Continuous.sub ?_ ?_) ?_) continuous_const)
    · exact continuous_finset_prod _ fun v _ => (p v).inner (p v)
    · exact continuous_finset_prod _ fun v _ => (p v).inner continuous_const
    · exact continuous_finset_prod _ fun v _ => continuous_const.inner (p v)
  have h2 : Filter.Tendsto (fun y => ‖tens y - tens x‖ ^ 2) (nhds x) (nhds 0) := by
    have e : (fun y => ‖tens y - tens x‖ ^ 2) = fun y : (∀ v, V v) =>
        RCLike.re ((∏ v, ⟪y v, y v⟫_ℂ) - (∏ v, ⟪y v, x v⟫_ℂ) - (∏ v, ⟪x v, y v⟫_ℂ) +
          (∏ v, ⟪x v, x v⟫_ℂ)) :=
      funext fun y => norm_sub_tens_sq hi y x
    rw [e]
    convert hF.tendsto x using 2
    simp
  have h3 := h2.sqrt
  simp only [Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] at h3
  exact h3

theorem tens_smul (hi : ∀ x y, ⟪tens x, tens y⟫_ℂ = ∏ v, ⟪x v, y v⟫_ℂ) (c : ι → ℂ) (x : ∀ v, V v) :
    tens (fun v => c v • x v) = (∏ v, c v) • tens x := by
  have key : ⟪tens (fun v => c v • x v) - (∏ v, c v) • tens x,
      tens (fun v => c v • x v) - (∏ v, c v) • tens x⟫_ℂ = 0 := by
    simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, hi,
      Finset.prod_mul_distrib, map_prod]
    ring
  exact sub_eq_zero.mp (inner_self_eq_zero.mp key)

theorem inner_tens_update [DecidableEq ι] (hi : ∀ x y, ⟪tens x, tens y⟫_ℂ = ∏ v, ⟪x v, y v⟫_ℂ) (ξ : ∀ v, V v)
    (v : ι) (a b : V v) :
    ⟪tens (Function.update ξ v a), tens (Function.update ξ v b)⟫_ℂ =
      ⟪a, b⟫_ℂ * ∏ w ∈ Finset.univ.erase v, ⟪ξ w, ξ w⟫_ℂ := by
  rw [hi, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ v)]
  simp only [Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun w hw => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hw), Function.update_of_ne (Finset.ne_of_mem_erase hw)]

theorem tens_update_inj [DecidableEq ι] (hi : ∀ x y, ⟪tens x, tens y⟫_ℂ = ∏ v, ⟪x v, y v⟫_ℂ) (ξ : ∀ v, V v)
    (v : ι) (hne : ∀ w, w ≠ v → ξ w ≠ 0) (a b : V v)
    (h : tens (Function.update ξ v a) = tens (Function.update ξ v b)) : a = b := by
  have hP : ∏ w ∈ Finset.univ.erase v, ⟪ξ w, ξ w⟫_ℂ ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro w hw
    exact inner_self_ne_zero.mpr (hne w (Finset.ne_of_mem_erase hw))
  have e : ∀ p q : V v, ⟪tens (Function.update ξ v p), tens (Function.update ξ v q)⟫_ℂ =
      ⟪p, q⟫_ℂ * ∏ w ∈ Finset.univ.erase v, ⟪ξ w, ξ w⟫_ℂ :=
    fun p q => inner_tens_update hi ξ v p q
  have h0 : ⟪tens (Function.update ξ v a) - tens (Function.update ξ v b),
      tens (Function.update ξ v a) - tens (Function.update ξ v b)⟫_ℂ = 0 := by
    rw [h, sub_self, inner_zero_left]
  rw [inner_sub_left, inner_sub_right, inner_sub_right, e, e, e, e] at h0
  have key : ⟪a - b, a - b⟫_ℂ * ∏ w ∈ Finset.univ.erase v, ⟪ξ w, ξ w⟫_ℂ = 0 := by
    rw [inner_sub_left, inner_sub_right, inner_sub_right]
    linear_combination h0
  exact sub_eq_zero.mp (inner_self_eq_zero.mp ((mul_eq_zero.mp key).resolve_right hP))

end Tens

theorem integrable_and_integral_pi_apply :
  ∀ (ι : Type) [Fintype ι] (X : ι → Type) [∀ v, MeasurableSpace (X v)] (μ : ∀ v, Measure (X v))
    [∀ v, SigmaFinite (μ v)] (V : ι → Type) [∀ v, NormedAddCommGroup (V v)] [∀ v, InnerProductSpace ℂ (V v)]
    [∀ v, FiniteDimensional ℂ (V v)] (Vπ : Type) [NormedAddCommGroup Vπ] [InnerProductSpace ℂ Vπ]
    [FiniteDimensional ℂ Vπ] (tens : (∀ v, V v) → Vπ),
    (∀ x y, ⟪tens x, tens y⟫_ℂ = ∏ v, ⟪x v, y v⟫_ℂ) → Submodule.span ℂ (Set.range tens) = ⊤ →
    ∀ G : ∀ v, X v → V v, (∀ v, Integrable (G v) (μ v)) →
      Integrable (fun y : ∀ v, X v => tens (fun v => G v (y v))) (Measure.pi μ) ∧
        ∫ y, tens (fun v => G v (y v)) ∂(Measure.pi μ) = tens (fun v => ∫ t, G v t ∂(μ v)) := by
  intro ι _ X _ μ _ V _ _ _ Vπ _ _ _ tens hi hspan G hG
  have hcoord : ∀ w : Vπ, Integrable (fun y : ∀ v, X v => ⟪w, tens fun v => G v (y v)⟫_ℂ)
      (Measure.pi μ) := by
    intro w
    have hw : w ∈ Submodule.span ℂ (Set.range tens) := by rw [hspan]; exact Submodule.mem_top
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨z, rfl⟩ := hx
      simp_rw [hi]
      exact Integrable.fintype_prod_dep (fun v => (hG v).const_inner (z v))
    | zero =>
      simp only [inner_zero_left]
      exact integrable_zero _ _ _
    | add x y _ _ hx hy =>
      simp only [inner_add_left]
      exact hx.add hy
    | smul a x _ hx =>
      simp only [inner_smul_left]
      exact hx.const_mul _
  have hFint : Integrable (fun y : ∀ v, X v => tens fun v => G v (y v)) (Measure.pi μ) := by
    have e : (fun y : ∀ v, X v => tens fun v => G v (y v)) = fun y =>
        ∑ i, ⟪stdOrthonormalBasis ℂ Vπ i, tens fun v => G v (y v)⟫_ℂ • stdOrthonormalBasis ℂ Vπ i :=
      funext fun y => ((stdOrthonormalBasis ℂ Vπ).sum_repr' _).symm
    rw [e]
    exact integrable_finset_sum _ fun i _ => (hcoord _).smul_const _
  refine ⟨hFint, ?_⟩
  refine ext_inner_left ℂ fun w => ?_
  have hw : w ∈ Submodule.span ℂ (Set.range tens) := by rw [hspan]; exact Submodule.mem_top
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨z, rfl⟩ := hx
    rw [← integral_inner hFint]
    simp_rw [hi]
    refine (integral_fintype_prod_eq_prod (fun v t => ⟪z v, G v t⟫_ℂ)).trans ?_
    exact Finset.prod_congr rfl fun v _ => integral_inner (hG v) (z v)
  | zero => simp only [inner_zero_left]
  | add x y _ _ hx hy => rw [inner_add_left, inner_add_left, hx, hy]
  | smul a x _ hx => rw [inner_smul_left, inner_smul_left, hx]

end Formalism.L2.SG.Pf.WuDec
