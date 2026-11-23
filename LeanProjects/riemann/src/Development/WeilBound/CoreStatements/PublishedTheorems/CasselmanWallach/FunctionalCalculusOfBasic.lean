import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.FunctionalCalculusLaws

noncomputable section

open Matrix Finset ReciprocityTheory.ChartRestriction.DS

namespace PositivityTheory.CW

namespace FunctionalCalculusInner

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {ι : Type}

theorem fc_basis (b : Module.Basis ι ℂ V) (μ : ι → ℝ) (φ : ℝ → ℝ) (i : ι) :
    fc b μ φ (b i) = ((φ (μ i) : ℝ) : ℂ) • b i := by
  unfold fc
  exact b.constr_basis ℂ _ i

theorem repr_fc (b : Module.Basis ι ℂ V) (μ : ι → ℝ) (φ : ℝ → ℝ) (v : V) (i : ι) :
    b.repr (fc b μ φ v) i = ((φ (μ i) : ℝ) : ℂ) * b.repr v i := by
  have key : (b.coord i).comp (fc b μ φ) = ((φ (μ i) : ℝ) : ℂ) • b.coord i := by
    refine b.ext fun j => ?_
    simp only [LinearMap.comp_apply, Module.Basis.coord_apply, fc_basis, map_smul,
      LinearMap.smul_apply, Module.Basis.repr_self]
    by_cases hji : j = i
    · subst hji; simp
    · simp [Finsupp.single_apply, hji]
  exact LinearMap.congr_fun key v

theorem inner_basis_left (b : Module.Basis ι ℂ V) (hb : Orthonormal ℂ b) (i : ι) (y : V) :
    inner ℂ (b i) y = b.repr y i := by
  classical
  have key : (innerₛₗ ℂ (b i) : V →ₗ[ℂ] ℂ) = b.coord i := by
    refine b.ext fun j => ?_
    show inner ℂ (b i) (b j) = b.repr (b j) i
    rw [Module.Basis.repr_self, orthonormal_iff_ite.mp hb i j]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij, Ne.symm hij]
  exact LinearMap.congr_fun key y

theorem inner_eq_sum (b : Module.Basis ι ℂ V) (hb : Orthonormal ℂ b) (x y : V) (s : Finset ι)
    (hs : (b.repr x).support ⊆ s) :
    inner ℂ x y = ∑ i ∈ s, starRingEnd ℂ (b.repr x i) * b.repr y i := by
  have hx : x = ∑ i ∈ s, b.repr x i • b i := by
    conv_lhs => rw [← b.linearCombination_repr x]
    rw [Finsupp.linearCombination_apply, Finsupp.sum_of_support_subset _ hs]
    intro i _
    simp
  conv_lhs => rw [hx]
  rw [sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_smul_left, inner_basis_left b hb]

theorem fc_id (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (b : Module.Basis ι ℂ V) (μ : ι → ℝ)
    (h : ∀ i, Eig ε E (μ i) (b i)) : fc b μ (fun x => x) = casimirK ε E :=
  b.ext fun i => by rw [fc_basis]; exact (h i).symm

theorem re_conj_mul (z : ℂ) (r : ℝ) : (starRingEnd ℂ z * ((r : ℂ) * z)).re = r * ‖z‖ ^ 2 := by
  rw [mul_left_comm, Complex.conj_mul']
  norm_cast

theorem re_inner_fc (b : Module.Basis ι ℂ V) (hb : Orthonormal ℂ b) (μ : ι → ℝ) (φ : ℝ → ℝ) (w : V) :
    (inner ℂ w (fc b μ φ w)).re = ∑ i ∈ (b.repr w).support, φ (μ i) * ‖b.repr w i‖ ^ 2 := by
  rw [inner_eq_sum b hb w _ _ subset_rfl, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [repr_fc, re_conj_mul]

end FunctionalCalculusInner

open FunctionalCalculusInner in
theorem functional_calculus_of_basic : A0 → FunctionalCalculusLaws := by
  intro _ n ε V _ _ E _ ι b μ hb
  have hid := fc_id ε E b μ hb.eig
  refine ⟨fun φ ν v hv => ?_, fun φ x y => ?_, fun φ ψ hφψ w => ?_, fun φ ψ => ?_, fun φ ψ => ?_,
    fun c => ?_, hid⟩
  · refine b.repr.injective (Finsupp.ext fun i => ?_)
    have h1 : b.repr (casimirK ε E v) i = b.repr ((ν : ℂ) • v) i := by rw [show casimirK ε E v = (ν : ℂ) • v from hv]
    rw [← hid, repr_fc] at h1
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul] at h1
    rw [repr_fc, map_smul, Finsupp.smul_apply, smul_eq_mul]
    by_cases h0 : b.repr v i = 0
    · simp [h0]
    · have : μ i = ν := by
        have := mul_right_cancel₀ h0 h1
        exact_mod_cast this
      rw [this]
  · have hs : (b.repr (fc b μ φ x)).support ⊆ (b.repr x).support := by
      intro i hi
      rw [Finsupp.mem_support_iff] at hi ⊢
      rw [repr_fc] at hi
      exact right_ne_zero_of_mul hi
    rw [inner_eq_sum b hb.on _ _ _ hs, inner_eq_sum b hb.on _ _ _ subset_rfl]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [repr_fc, repr_fc, map_mul, Complex.conj_ofReal]
    ring
  · rw [re_inner_fc b hb.on, re_inner_fc b hb.on]
    exact Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_right (hφψ _ (hb.nonneg i)) (sq_nonneg _)
  · refine b.ext fun i => ?_
    simp only [fc_basis, LinearMap.add_apply, Complex.ofReal_add, add_smul]
  · refine b.ext fun i => ?_
    simp only [fc_basis, Module.End.mul_apply, map_smul, smul_smul, Complex.ofReal_mul, mul_comm]
  · refine b.ext fun i => ?_
    simp [fc_basis]

end PositivityTheory.CW

end
