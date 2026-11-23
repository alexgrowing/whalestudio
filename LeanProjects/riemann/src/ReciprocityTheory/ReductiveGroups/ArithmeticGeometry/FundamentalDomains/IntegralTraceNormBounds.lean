import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.TraceIntegralBasis

namespace ReciprocityTheory.ChartRestriction.G.FD.IntegralTraceNormBounds

open NumberField InfinitePlace Module Submodule TraceIntegralBasis
open scoped ComplexConjugate Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

lemma cc_mul (a b : E) : cc (a * b) = cc a * cc b := by
  unfold cc
  exact map_mul _ a b

lemma cc_cc (a : E) : cc (cc a) = a := IsCMField.complexConj_apply_apply E a

lemma cc_two : cc (2 : E) = 2 := by
  unfold cc
  exact map_ofNat _ 2

lemma inner_iota_eq_trace (x y : E) :
    inner ℝ (iota E x) (iota E y) = (1 / 2 : ℝ) * (Algebra.trace ℚ E (x * cc y) : ℝ) := by
  rw [inner_iota, ← sum_re_eq_trace]
  apply Finset.sum_congr rfl
  intro w _
  simp only [cc, map_mul, IsCMField.complexEmbedding_complexConj]

variable (E) in

noncomputable def ed : Basis (Free.ChooseBasisIndex ℤ (𝓞 E)) ℚ E :=
  (Algebra.traceForm ℚ E).dualBasis (traceForm_nondegenerate (K := ℚ) (L := E)) (integralBasis E)

lemma trace_ed (i j : Free.ChooseBasisIndex ℤ (𝓞 E)) :
    Algebra.trace ℚ E (integralBasis E i * ed E j) = if i = j then 1 else 0 := by
  rw [← Algebra.traceForm_apply]
  exact LinearMap.BilinForm.apply_dualBasis_right _ (Algebra.traceForm_isSymm ℚ) _ i j

variable (E) in

noncomputable def bd (j : Free.ChooseBasisIndex ℤ (𝓞 E)) : VS E := iota E (2 * cc (ed E j))

lemma inner_bas_bd (i j : Free.ChooseBasisIndex ℤ (𝓞 E)) :
    inner ℝ (bas E i) (bd E j) = if i = j then 1 else 0 := by
  rw [bas_apply, bd, inner_iota_eq_trace, cc_mul, cc_cc, cc_two]
  have h2 : integralBasis E i * (2 * ed E j) = (2 : ℚ) • (integralBasis E i * ed E j) := by
    rw [Algebra.smul_def, map_ofNat]
    ring
  rw [h2, LinearMap.map_smul, trace_ed]
  split_ifs <;> norm_num

lemma trace_int (c : Free.ChooseBasisIndex ℤ (𝓞 E) → ℤ) (γ : 𝓞 E) :
    ∃ m : ℤ, Algebra.trace ℚ E ((∑ j, c j • ed E j) * (γ : E)) = m := by
  obtain ⟨m, hm⟩ : ∃ m : Free.ChooseBasisIndex ℤ (𝓞 E) → ℤ,
      (γ : E) = ∑ i, m i • integralBasis E i := by
    refine ⟨(RingOfIntegers.basis E).repr γ, ?_⟩
    conv_lhs => rw [← (RingOfIntegers.basis E).sum_repr γ]
    simp [integralBasis_apply]
  have key : ∀ j i, Algebra.trace ℚ E ((c j • ed E j) * (m i • integralBasis E i)) =
      if i = j then ((c j * m i : ℤ) : ℚ) else 0 := by
    intro j i
    rw [smul_mul_smul_comm, map_zsmul, mul_comm (ed E j), trace_ed]
    split_ifs <;> simp
  refine ⟨∑ j, c j * m j, ?_⟩
  rw [hm, Finset.sum_mul_sum, map_sum]
  simp_rw [map_sum, key]
  simp [Finset.sum_ite_eq']

lemma norm_discr (β : E) (hβ : β ≠ 0)
    (hint : ∀ γ : 𝓞 E, ∃ m : ℤ, Algebra.trace ℚ E (β * (γ : E)) = m) :
    1 ≤ |(Algebra.norm ℚ β : ℝ)| * dE E := by
  choose m hm using fun i j => hint (RingOfIntegers.basis E i * RingOfIntegers.basis E j)
  have hbB : ∀ i, integralBasis E i = ((RingOfIntegers.basis E i : 𝓞 E) : E) := by
    intro i
    rw [integralBasis_apply]
  have hP : Matrix.of (fun i j => ((m i j : ℤ) : ℚ)) =
      Algebra.traceMatrix ℚ (integralBasis E) * Algebra.leftMulMatrix (integralBasis E) β := by
    ext i j
    rw [Matrix.of_apply, ← hm i j, Matrix.mul_apply]
    have e : β * ((RingOfIntegers.basis E i * RingOfIntegers.basis E j : 𝓞 E) : E) =
        integralBasis E i * (β * integralBasis E j) := by
      rw [hbB, hbB]
      push_cast
      ring
    rw [e]
    conv_lhs => rw [← (integralBasis E).sum_repr (β * integralBasis E j)]
    rw [Finset.mul_sum, map_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [Algebra.leftMulMatrix_eq_repr_mul, Algebra.traceMatrix_apply, Algebra.traceForm_apply,
      mul_smul_comm, LinearMap.map_smul, smul_eq_mul]
    ring
  have h1 : ((Matrix.of m).det : ℚ) = (Matrix.of (fun i j => ((m i j : ℤ) : ℚ))).det := by
    rw [show ((Matrix.of m).det : ℚ) = (Int.castRingHom ℚ) (Matrix.of m).det from rfl,
      RingHom.map_det]
    rfl
  have hdet : ((Matrix.of m).det : ℚ) = (NumberField.discr E : ℚ) * Algebra.norm ℚ β := by
    rw [h1, hP, Matrix.det_mul, NumberField.coe_discr, Algebra.discr_def,
      Algebra.norm_eq_matrix_det (integralBasis E)]
  have hN0 : Algebra.norm ℚ β ≠ 0 := Algebra.norm_ne_zero_iff.mpr hβ
  have hD0 : (NumberField.discr E : ℚ) ≠ 0 := by exact_mod_cast NumberField.discr_ne_zero E
  have hZ : (Matrix.of m).det ≠ 0 := by
    intro h
    have h0 : ((Matrix.of m).det : ℚ) = 0 := by rw [h]; simp
    rw [hdet] at h0
    exact mul_ne_zero hD0 hN0 h0
  have hR : ((Matrix.of m).det : ℝ) =
      ((NumberField.discr E : ℤ) : ℝ) * ((Algebra.norm ℚ β : ℚ) : ℝ) := by
    have h2 := congrArg (Rat.cast : ℚ → ℝ) hdet
    simp only [Rat.cast_mul, Rat.cast_intCast] at h2
    exact h2
  unfold dE
  rw [← abs_mul, mul_comm, ← hR]
  exact_mod_cast Int.one_le_abs hZ

lemma prod_norm (β : E) :
    ∏ w : CP E, ‖w.1.embedding β‖ ^ 2 = |(Algebra.norm ℚ β : ℝ)| := by
  rw [← Rat.cast_abs, ← NumberField.InfinitePlace.prod_eq_abs_norm,
    ← (Equiv.subtypeUnivEquiv (fun w : InfinitePlace E => IsTotallyComplex.isComplex w)).prod_comp]
  apply Finset.prod_congr rfl
  intro w _
  rw [InfinitePlace.norm_embedding_eq]
  change w.1 β ^ 2 = w.1 β ^ w.1.mult
  rw [InfinitePlace.mult_isComplex]

lemma dE_pos : 0 < dE E := by
  unfold dE
  exact abs_pos.mpr (by exact_mod_cast NumberField.discr_ne_zero E)

lemma card_complexPlaces_pos : 0 < Fintype.card (CP E) := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
  exact Fintype.card_pos_iff.mpr ⟨⟨w, IsTotallyComplex.isComplex w⟩⟩

lemma norm_bd_ge (x : VS E) (hx : x ∈ span ℤ (Set.range (bd E))) (hx0 : x ≠ 0) :
    4 * (Fintype.card (CP E) : ℝ) * dE E ^ (-(1 / (Fintype.card (CP E) : ℝ))) ≤ ‖x‖ ^ 2 := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hx
  obtain ⟨β, hβdef⟩ : ∃ β : E, β = ∑ j, c j • ed E j := ⟨_, rfl⟩
  have hxβ : x = iota E (2 * cc β) := by
    rw [← hc, hβdef]
    simp only [bd, cc, map_sum, map_zsmul, Finset.mul_sum, mul_smul_comm]
  have hβ0 : β ≠ 0 := by
    rintro h
    apply hx0
    rw [hxβ, h, cc, map_zero, mul_zero, map_zero]
  have hint : ∀ γ : 𝓞 E, ∃ m : ℤ, Algebra.trace ℚ E (β * γ) = m := by
    intro γ
    rw [hβdef]
    exact trace_int c γ
  have hN := norm_discr β hβ0 hint
  have h2n : ‖(2 : ℂ)‖ = 2 := by norm_num
  have hnorm : ‖x‖ ^ 2 = 4 * ∑ w : CP E, ‖w.1.embedding β‖ ^ 2 := by
    rw [hxβ, norm_sq_iota, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w _
    rw [map_mul, norm_mul, cc, IsCMField.complexEmbedding_complexConj, Complex.norm_conj,
      map_ofNat, h2n]
    ring
  have hn : (0 : ℝ) < Fintype.card (CP E) := by exact_mod_cast card_complexPlaces_pos
  have hd : 0 < dE E := dE_pos
  have hNinv : (dE E)⁻¹ ≤ |(Algebra.norm ℚ β : ℝ)| := by
    rw [inv_eq_one_div, div_le_iff₀ hd]
    exact hN
  have hgm := Real.geom_mean_le_arith_mean_weighted (Finset.univ : Finset (CP E))
    (fun _ => 1 / (Fintype.card (CP E) : ℝ)) (fun w => ‖w.1.embedding β‖ ^ 2)
    (fun _ _ => by positivity)
    (by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; field_simp)
    (fun _ _ => by positivity)
  rw [Real.finset_prod_rpow _ _ (fun _ _ => by positivity), prod_norm, ← Finset.mul_sum] at hgm
  have h1 : dE E ^ (-(1 / (Fintype.card (CP E) : ℝ))) ≤
      |(Algebra.norm ℚ β : ℝ)| ^ (1 / (Fintype.card (CP E) : ℝ)) := by
    rw [Real.rpow_neg hd.le, ← Real.inv_rpow hd.le]
    exact Real.rpow_le_rpow (inv_nonneg.mpr hd.le) hNinv (by positivity)
  rw [hnorm]
  have h3 := mul_le_mul_of_nonneg_left (h1.trans hgm)
    (by positivity : (0 : ℝ) ≤ 4 * (Fintype.card (CP E) : ℝ))
  calc 4 * (Fintype.card (CP E) : ℝ) * dE E ^ (-(1 / (Fintype.card (CP E) : ℝ)))
      ≤ 4 * (Fintype.card (CP E) : ℝ) *
        (1 / (Fintype.card (CP E) : ℝ) * ∑ w : CP E, ‖w.1.embedding β‖ ^ 2) := h3
    _ = 4 * ∑ w : CP E, ‖w.1.embedding β‖ ^ 2 := by
      rw [← mul_assoc, mul_assoc 4, mul_one_div_cancel hn.ne', mul_one]

end ReciprocityTheory.ChartRestriction.G.FD.IntegralTraceNormBounds
