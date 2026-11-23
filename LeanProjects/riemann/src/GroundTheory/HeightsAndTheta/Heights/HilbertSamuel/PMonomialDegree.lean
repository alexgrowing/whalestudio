import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
import ReciprocityTheory.GeometryOfNumbers.SphericalMonomials.ChiPSt
import ReciprocityTheory.GeometryOfNumbers.SphericalMonomials.SupStMonoNormSqPos
import ReciprocityTheory.GeometryOfNumbers.SphericalMonomials.GaussSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ABridgeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.CSandwichStE
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory MeasureTheory Module

noncomputable section

namespace MonomialDegree

def blockEquiv (D : ℕ) : Fin (D + 1) ≃ Ix (Fin (D + 1)) where
  toFun i := ⟨(), i⟩
  invFun p := p.2
  left_inv _ := rfl
  right_inv _ := rfl

def monoForm (D n : ℕ) (i : Fin (Finset.Nat.antidiagonalTuple (D + 1) n).card) :
    MvPolynomial (Ix (Fin (D + 1))) ℚ :=
  map (Int.castRingHom ℚ) (rename (blockEquiv D) (monoZ (adtEnum D n i)))

def ptEquiv (D : ℕ) : (Fin (D + 1) → ℂ) ≃ᵐ (Ix (Fin (D + 1)) → ℂ) :=
  MeasurableEquiv.piCongrLeft (fun _ => ℂ) (blockEquiv D)

theorem ptEquiv_apply (D : ℕ) (w : Fin (D + 1) → ℂ) (t : Fin (D + 1)) :
    ptEquiv D w (blockEquiv D t) = w t := by
  rfl

theorem comp_ptEquiv (D : ℕ) (w : Fin (D + 1) → ℂ) : ptEquiv D w ∘ blockEquiv D = w :=
  funext (ptEquiv_apply D w)

theorem card_ix (D : ℕ) : Fintype.card (Ix (Fin (D + 1))) = D + 1 := by
  simp [Ix, GlobalTheory, Fintype.card_sigma]

theorem sum_ix_norm (D : ℕ) (w : Fin (D + 1) → ℂ) : ∑ j, ‖ptEquiv D w j‖ ^ 2 = sqN w := by
  rw [← (blockEquiv D).sum_comp]
  simp only [ptEquiv_apply]
  rfl

theorem gaussMeasure_eq (D : ℕ) :
    gaussMeasure (Ix (Fin (D + 1))) = (gaussC (D + 1)).map (ptEquiv D) := by
  have hmp : MeasurePreserving (ptEquiv D) volume volume :=
    volume_measurePreserving_piCongrLeft (fun _ : Ix (Fin (D + 1)) => ℂ) (blockEquiv D)
  ext s hs
  rw [Measure.map_apply (ptEquiv D).measurable hs, gaussMeasure, gaussC, withDensity_apply _ hs,
    withDensity_apply _ ((ptEquiv D).measurable hs), ← hmp.map_eq,
    setLIntegral_map hs (by fun_prop) (ptEquiv D).measurable]
  refine lintegral_congr fun w => ?_
  rw [sum_ix_norm, card_ix, zpow_neg, zpow_natCast]

theorem secFun_monoForm (D n : ℕ) (i : Fin (Finset.Nat.antidiagonalTuple (D + 1) n).card)
    (z : Ix (Fin (D + 1)) → ℂ) : secFun (monoForm D n i) z = monoC (adtEnum D n i) (z ∘ blockEquiv D) := by
  rw [monoForm, secFun_map_intQ, eval_map_int, aeval_rename, aeval_monoZ]
  rfl

theorem fs_rho_ptEquiv (D : ℕ) (w : Fin (D + 1) → ℂ) :
    (fsMetric (Ix (Fin (D + 1)))).ρ (ptEquiv D w) = Real.sqrt (sqN w) := by
  change ‖WithLp.toLp 2 (ptEquiv D w)‖ = _
  rw [EuclideanSpace.norm_eq]
  rw [← sum_ix_norm]

theorem integral_gaussC_mono (D n : ℕ) {a b : Fin (D + 1) → ℕ} (ha : ∑ i, a i = n) (hb : ∑ i, b i = n) :
    ∫ w, starRingEnd ℂ (monoC a w) * monoC b w * ((((Real.sqrt (sqN w)) ^ (2 * n))⁻¹ : ℝ) : ℂ)
        ∂(gaussC (D + 1)) =
      ∫ w, starRingEnd ℂ (monoC a w) * monoC b w ∂(sphProb (D + 1)) := by
  rw [sphMonom_integral_sphProb _ (sphMonom_continuous_f a b)]
  unfold gaussC
  simp only [ENNReal.ofReal]
  have hm : Measurable fun z : Fin (D + 1) → ℂ =>
      Real.toNNReal ((Real.pi ^ (D + 1))⁻¹ * Real.exp (-sqN z)) :=
    (measurable_const.mul (Real.measurable_exp.comp
      sphMonom_continuous_sqN.measurable.neg)).real_toNNReal
  rw [integral_withDensity_eq_integral_smul hm, ← integral_const_mul]
  congr 1
  funext z
  rw [sphMonom_f_smul, ha, hb, NNReal.smul_def, Real.coe_toNNReal _ (by positivity),
    Complex.real_smul]
  push_cast
  rw [inv_pow, two_mul]
  ring

theorem integrable_monoForm (D n : ℕ) (i j : Fin (Finset.Nat.antidiagonalTuple (D + 1) n).card) :
    Integrable (fun z => starRingEnd ℂ (secFun (monoForm D n i) z) * secFun (monoForm D n j) z *
      (wgt (fsMetric (Ix (Fin (D + 1)))) n z : ℂ)) (gaussMeasure (Ix (Fin (D + 1)))) := by
  rw [gaussMeasure_eq, integrable_map_equiv]
  have hfun : (fun z => starRingEnd ℂ (secFun (monoForm D n i) z) * secFun (monoForm D n j) z *
      (wgt (fsMetric (Ix (Fin (D + 1)))) n z : ℂ)) ∘ ptEquiv D = fun w =>
      starRingEnd ℂ (monoC (adtEnum D n i) w) * monoC (adtEnum D n j) w *
        ((((Real.sqrt (sqN w)) ^ (2 * n))⁻¹ : ℝ) : ℂ) := by
    funext w
    simp only [Function.comp, secFun_monoForm, comp_ptEquiv, wgt, fs_rho_ptEquiv]
  rw [hfun]
  refine (integrable_const (1 : ℝ)).mono' ?_ (Filter.Eventually.of_forall fun w => ?_)
  · exact ((sphMonom_continuous_f _ _).measurable.mul (Complex.measurable_ofReal.comp
      ((sphMonom_continuous_sqN.measurable.sqrt.pow_const _).inv))).aestronglyMeasurable
  · have ha := norm_monoC_sq_le (adtEnum D n i) w
    have hb := norm_monoC_sq_le (adtEnum D n j) w
    rw [adtEnum_sum] at ha hb
    have hs : 0 ≤ sqN w := sphMonom_sqN_nonneg w
    have hS : Real.sqrt (sqN w) ^ (2 * n) = sqN w ^ n := by rw [pow_mul, Real.sq_sqrt hs]
    rw [norm_mul, norm_mul, RCLike.norm_conj, Complex.norm_real, Real.norm_eq_abs, hS,
      abs_of_nonneg (inv_nonneg.mpr (pow_nonneg hs n))]
    have h0 : 0 ≤ ‖monoC (adtEnum D n i) w‖ * ‖monoC (adtEnum D n j) w‖ := by positivity
    have hq : 0 ≤ sqN w ^ n := pow_nonneg hs n
    have h2 : (‖monoC (adtEnum D n i) w‖ * ‖monoC (adtEnum D n j) w‖) ^ 2 ≤ (sqN w ^ n) ^ 2 := by
      rw [mul_pow, sq (sqN w ^ n)]
      exact mul_le_mul ha hb (by positivity) hq
    have hP : ‖monoC (adtEnum D n i) w‖ * ‖monoC (adtEnum D n j) w‖ ≤ sqN w ^ n := by nlinarith
    rcases hq.eq_or_lt with h | h
    · rw [← h, inv_zero, mul_zero]
      norm_num
    · rw [← div_eq_mul_inv]
      exact div_le_one_of_le₀ hP h.le

theorem bGram_monoForm (D n : ℕ) :
    bGram (gaussMeasure (Ix (Fin (D + 1)))) (fun k => secFun (monoForm D n k))
        (wgt (fsMetric (Ix (Fin (D + 1)))) n) =
      Matrix.diagonal fun k => ((monoNormSq (adtEnum D n k) : ℝ) : ℂ) := by
  ext i j
  rw [bGram, Matrix.of_apply, gaussMeasure_eq, integral_map_equiv]
  simp only [secFun_monoForm, comp_ptEquiv, wgt, fs_rho_ptEquiv]
  rw [integral_gaussC_mono D n (adtEnum_sum D n i) (adtEnum_sum D n j), supSt_gram, Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst hij
    simp
  · simp [hij, (adtEnum_injective D n).ne hij]

variable {Ω : Type} [Field Ω] {D : ℕ}

theorem coordIdeal_comp_eq_bot {x : Ix (Fin (D + 1)) → Ω} (hx : coordIdeal ℤ x = ⊥) :
    coordIdeal ℤ (x ∘ blockEquiv D) = ⊥ := by
  rw [eq_bot_iff]
  intro f hf
  have h1 : rename (blockEquiv D) f ∈ coordIdeal ℤ x := by
    rw [coordIdeal, RingHom.mem_ker] at hf ⊢
    rw [← hf]
    simp only [coneMap, aeval_rename]
    rfl
  rw [hx, Ideal.mem_bot] at h1
  rw [Ideal.mem_bot]
  exact rename_injective _ (blockEquiv D).injective (by rw [h1, map_zero])

theorem eq_of_aeval_eq {x : Ix (Fin (D + 1)) → Ω} (hx : coordIdeal ℤ x = ⊥) {n : ℕ}
    {f g : MvPolynomial (Ix (Fin (D + 1))) ℤ} (hf : f.IsHomogeneous n) (hg : g.IsHomogeneous n)
    (h : aeval x f = aeval x g) : f = g := by
  have := mem_coordIdeal_of_isHomogeneous ℤ x (hf.sub hg) (by rw [map_sub, h, sub_self])
  rwa [hx, Ideal.mem_bot, sub_eq_zero] at this

variable [CharZero Ω]

theorem aeval_monoForm (x : Ix (Fin (D + 1)) → Ω) (n : ℕ)
    (i : Fin (Finset.Nat.antidiagonalTuple (D + 1) n).card) :
    aeval x (monoForm D n i) = ∏ t, (x ∘ blockEquiv D) t ^ adtEnum D n i t := by
  rw [monoForm, aeval_map_intQ, aeval_rename, aeval_monoZ]

theorem isSecBasis_monoForm {x : Ix (Fin (D + 1)) → Ω} (hx : coordIdeal ℤ x = ⊥) (n : ℕ) :
    IsSecBasis x n (monoForm D n) := by
  refine ⟨fun i => ⟨_, (monoZ_isHomogeneous (adtEnum_sum D n i)).rename_isHomogeneous, rfl⟩, ?_, ?_⟩
  · rw [Fintype.linearIndependent_iff]
    intro u hu i
    have h0 := eq_zero_of_sum_mono (coordIdeal_comp_eq_bot hx) u
      (by simpa only [aeval_monoForm, zsmul_eq_mul] using hu)
    exact congrFun h0 i
  · apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact Submodule.mem_map.mpr ⟨rename (blockEquiv D) (monoZ (adtEnum D n i)),
        (mem_homogeneousSubmodule _ _).mpr (monoZ_isHomogeneous (adtEnum_sum D n i)).rename_isHomogeneous,
        by simp only [AlgHom.toLinearMap_apply, monoForm, aeval_map_intQ]⟩
    · rintro _ ⟨f, hf, rfl⟩
      have hf' : f.IsHomogeneous n := (mem_homogeneousSubmodule _ _).mp hf
      have hg : (rename (blockEquiv D).symm f).IsHomogeneous n := hf'.rename_isHomogeneous
      have hfx : (aeval x : MvPolynomial (Ix (Fin (D + 1))) ℤ →ₐ[ℤ] Ω).toLinearMap f =
          aeval (x ∘ blockEquiv D) (rename (blockEquiv D).symm f) := by
        rw [AlgHom.toLinearMap_apply, aeval_rename]
        congr 1
      rw [hfx, aeval_eq_sum_adt _ hg]
      refine Submodule.sum_mem _ fun a ha => ?_
      have hai : adtEnum D n ((Finset.Nat.antidiagonalTuple (D + 1) n).equivFin ⟨a, ha⟩) = a := by
        simp [adtEnum]
      rw [← zsmul_eq_mul, ← hai, ← aeval_monoForm]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

theorem exists_change {x : Ix (Fin (D + 1)) → Ω} (hx : coordIdeal ℤ x = ⊥) {n : ℕ}
    {b' : Fin (Finset.Nat.antidiagonalTuple (D + 1) n).card → MvPolynomial (Ix (Fin (D + 1))) ℚ}
    (hb' : IsSecBasis x n b') :
    ∃ A : Matrix (Fin (Finset.Nat.antidiagonalTuple (D + 1) n).card)
        (Fin (Finset.Nat.antidiagonalTuple (D + 1) n).card) ℤ,
      (∀ k z, secFun (b' k) z = ∑ l, (A k l : ℂ) * secFun (monoForm D n l) z) ∧ A.det ^ 2 = 1 := by
  have hM := isSecBasis_monoForm hx n
  have hA : ∀ k, ∃ c : Fin (Finset.Nat.antidiagonalTuple (D + 1) n).card → ℤ,
      ∑ l, c l • aeval x (monoForm D n l) = aeval x (b' k) := fun k =>
    (Submodule.mem_span_range_iff_exists_fun ℤ).mp (by rw [hM.2.2, ← hb'.2.2]; exact Submodule.subset_span ⟨k, rfl⟩)
  have hB : ∀ l, ∃ c : Fin (Finset.Nat.antidiagonalTuple (D + 1) n).card → ℤ,
      ∑ m, c m • aeval x (b' m) = aeval x (monoForm D n l) := fun l =>
    (Submodule.mem_span_range_iff_exists_fun ℤ).mp (by rw [hb'.2.2, ← hM.2.2]; exact Submodule.subset_span ⟨l, rfl⟩)
  choose A hA using hA
  choose B hB using hB
  refine ⟨Matrix.of A, fun k z => ?_, ?_⟩
  · obtain ⟨f', hf', hbf'⟩ := hb'.1 k
    have heq : f' = ∑ l, C (A k l) * rename (blockEquiv D) (monoZ (adtEnum D n l)) := by
      refine eq_of_aeval_eq hx hf' (IsHomogeneous.sum _ _ _ fun l _ => ?_) ?_
      · simpa using (isHomogeneous_C _ (A k l)).mul (monoZ_isHomogeneous (adtEnum_sum D n l)).rename_isHomogeneous
      · calc aeval x f' = aeval x (b' k) := by rw [hbf', aeval_map_intQ]
          _ = ∑ l, A k l • aeval x (monoForm D n l) := (hA k).symm
          _ = _ := by
            simp only [map_sum, map_mul, map_intCast, eq_intCast, zsmul_eq_mul, monoForm,
              aeval_map_intQ]
    rw [hbf', secFun_map_intQ, heq]
    simp only [monoForm, secFun_map_intQ, Matrix.of_apply, map_sum, map_mul, map_intCast, eq_intCast]
  · have hAB : Matrix.of A * Matrix.of B = 1 := by
      ext k m
      have h1 : ∑ m, (Matrix.of A * Matrix.of B) k m • aeval x (b' m) = aeval x (b' k) := by
        simp only [Matrix.mul_apply, Matrix.of_apply, Finset.sum_smul, mul_smul]
        rw [Finset.sum_comm]
        simp only [← Finset.smul_sum, hB]
        exact hA k
      have h2 : ∑ m, (1 : Matrix (Fin (Finset.Nat.antidiagonalTuple (D + 1) n).card)
          (Fin (Finset.Nat.antidiagonalTuple (D + 1) n).card) ℤ) k m • aeval x (b' m) = aeval x (b' k) := by
        simp [Matrix.one_apply]
      have hli := Fintype.linearIndependent_iff.mp hb'.2.1
        (fun m => (Matrix.of A * Matrix.of B) k m - (1 : Matrix _ _ ℤ) k m)
        (by simp only [sub_smul, Finset.sum_sub_distrib, h1, h2, sub_self]) m
      exact sub_eq_zero.mp hli
    have hd := congrArg Matrix.det hAB
    rw [Matrix.det_mul, Matrix.det_one] at hd
    exact Int.isUnit_sq (isUnit_iff_exists_inv.mpr ⟨_, hd⟩)

theorem chi_coord {x : Ix (Fin (D + 1)) → Ω} (hx : coordIdeal ℤ x = ⊥) (n : ℕ) :
    chi x (fsMetric (Ix (Fin (D + 1)))) (gaussMeasure (Ix (Fin (D + 1)))) n = chiP D n := by
  classical
  have hM := isSecBasis_monoForm hx n
  have h : ∃ p : (Σ r : ℕ, Fin r → MvPolynomial (Ix (Fin (D + 1))) ℚ), IsSecBasis x n p.2 :=
    ⟨⟨_, monoForm D n⟩, hM⟩
  unfold chi
  rw [dif_pos h]
  have hp := h.choose_spec
  generalize h.choose = p at hp ⊢
  obtain ⟨r', b'⟩ := p
  have hp' : IsSecBasis x n b' := hp
  have hr : r' = (Finset.Nat.antidiagonalTuple (D + 1) n).card := hp'.card_eq.trans hM.card_eq.symm
  subst hr
  obtain ⟨A, hA, hdet⟩ := exists_change hx hp'
  have hG := bGram_change (μ := gaussMeasure (Ix (Fin (D + 1)))) (fun k => secFun (monoForm D n k))
    (fun k => secFun (b' k)) (wgt (fsMetric (Ix (Fin (D + 1)))) n) A (integrable_monoForm D n)
    (fun k => Filter.Eventually.of_forall (hA k))
  rw [bGram_monoForm] at hG
  have hw : (Height.totalWeight ℚ : ℝ) = 1 := by
    rw [NumberField.totalWeight_eq_finrank, Module.finrank_self, Nat.cast_one]
  have hcast : A.map (Int.cast : ℤ → ℂ) = (A.map (Int.cast : ℤ → ℝ)).map Complex.ofRealHom := by
    rw [Matrix.map_map]
    congr 1
  have hR : realGram (K := ℚ) (fun _ => fsMetric (Ix (Fin (D + 1)))) (fun _ => gaussMeasure (Ix (Fin (D + 1))))
      n b' = A.map (Int.cast : ℤ → ℝ) * Matrix.diagonal (fun k => monoNormSq (adtEnum D n k)) *
        (A.map (Int.cast : ℤ → ℝ)).transpose := by
    have hC : A.map (Int.cast : ℤ → ℂ) * Matrix.diagonal (fun k => ((monoNormSq (adtEnum D n k) : ℝ) : ℂ)) *
        (A.map (Int.cast : ℤ → ℂ)).transpose =
        (A.map (Int.cast : ℤ → ℝ) * Matrix.diagonal (fun k => monoNormSq (adtEnum D n k)) *
          (A.map (Int.cast : ℤ → ℝ)).transpose).map Complex.ofRealHom := by
      rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, hcast,
        Matrix.diagonal_map (map_zero _)]
      rfl
    ext k l
    rw [realGram_eq, hG, hC, Matrix.map_apply, Complex.ofRealHom_eq_coe, Complex.ofReal_re]
  have hdA : (A.map (Int.cast : ℤ → ℝ)).det = (A.det : ℝ) := ((Int.castRingHom ℝ).map_det A).symm
  have hdet' : (A.det : ℝ) ^ 2 = 1 := by exact_mod_cast hdet
  simp only [l2Degree, hw, div_one]
  rw [hR, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal, hdA]
  have hprod : (A.det : ℝ) * (∏ k, monoNormSq (adtEnum D n k)) * (A.det : ℝ) =
      ∏ k, monoNormSq (adtEnum D n k) := by
    linear_combination (∏ k, monoNormSq (adtEnum D n k)) * hdet'
  rw [hprod, Real.log_prod (fun k _ => (monoNormSq_pos (adtEnum D n k)).ne'), chiP,
    sum_adtEnum D n (fun a => Real.log (monoNormSq a))]
  ring

theorem bounds (D : ℕ) : ∃ C : ℝ, ∀ n : ℕ, 0 ≤ chiP D n ∧ chiP D n ≤ C * (n : ℝ) ^ (D + 1) ∧
    0 ≤ chiP D (n + 1) - chiP D n ∧
      (1 ≤ n → chiP D (n + 1) - chiP D n ≤ C * (n : ℝ) ^ D * Real.log (n + 1)) := by
  obtain ⟨C₁, h₁⟩ := exists_chiP_le D
  obtain ⟨C₂, h₂⟩ := exists_chiP_succ_sub_le D
  refine ⟨max C₁ C₂, fun n => ⟨chiP_nonneg D n, (h₁ n).trans ?_, chiP_succ_sub_nonneg D n,
    fun hn => (h₂ n hn).trans ?_⟩⟩
  · exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  · have hl : 0 ≤ Real.log ((n : ℝ) + 1) :=
      Real.log_nonneg (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)) hl

end MonomialDegree

theorem MonomialDegree.proof : MonomialDegree.Statement :=
  ⟨fun _ _ _ _ _ hx n => MonomialDegree.chi_coord hx n, MonomialDegree.bounds⟩

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
