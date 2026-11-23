import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MemL2OfSmoothVector
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjInvariantApproxIdentityRealLieSmoothin
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsIsOpenIsCompact

noncomputable section
open NumberField MeasureTheory Matrix Topology
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CuspQuot GlobalTheory.AutGrowth.ApproxId GlobalTheory.GLFin
open scoped ContDiff

namespace GlobalTheory.GLFin.Inhab
variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

section
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
omit [IsTotallyComplex E] in

theorem contDiffOn_invL : ContDiffOn ℝ ∞ (fun x : Lie E a => toL (Matrix.of x)⁻¹) (invSet E a) := by
  haveI : CompleteSpace (Matrix (Fin a) (Fin a) (Cinf E)) := FiniteDimensional.complete ℝ _
  let T : Matrix (Fin a) (Fin a) (Cinf E) →L[ℝ] Lie E a :=
    LinearMap.toContinuousLinearMap (LinearMap.id : Lie E a →ₗ[ℝ] Lie E a)
  let S : Lie E a →L[ℝ] Matrix (Fin a) (Fin a) (Cinf E) :=
    LinearMap.toContinuousLinearMap (LinearMap.id : Lie E a →ₗ[ℝ] Lie E a)
  intro x hx
  have hu : IsUnit (S x) := hx
  have h1 : ContDiffAt ℝ ∞ Ring.inverse (S x) := by simpa using contDiffAt_ringInverse ℝ (n := ∞) hu.unit
  have h2 := (T.contDiff.contDiffAt.comp x (h1.comp x S.contDiff.contDiffAt)).contDiffWithinAt (s := invSet E a)
  refine h2.congr (fun y _ => ?_) ?_ <;> exact congrArg toL (Matrix.nonsing_inv_eq_ringInverse _)
end

theorem cP : Continuous (fun g : GA E a => GeneralLinearGroup.map (pInf E) g) := by
  have h : Continuous (pInf E) := by
    refine continuous_pi fun w => ?_
    exact (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
      ((continuous_apply w).comp continuous_fst)
  exact Continuous.units_map _ (continuous_id.matrix_map h)

omit [IsTotallyComplex E] in

theorem cQ : Continuous (fun g : GA E a => GeneralLinearGroup.map (pFin E) g) :=
  Continuous.units_map _ (continuous_id.matrix_map (continuous_snd : Continuous (pFin E)))

omit [IsTotallyComplex E] in

theorem cF : Continuous (finGL E a) := by
  refine Continuous.units_map _ ?_
  have hs : Continuous (sFin E : Af E → Ad E) := continuous_const.prodMk continuous_id
  exact continuous_const.sub continuous_const |>.add (continuous_id.matrix_map hs)

omit [IsTotallyComplex E] in

theorem cd1 (m : ℝ) (L : Lie E a →L[ℝ] Lie E a) : ContDiff ℝ ∞ fun x => bumpR E a m (L x) :=
  (contDiff_bumpR m).comp L.contDiff

theorem exists_isDirac (μ : Measure (GA E a)) [μ.IsHaarMeasure] (U : Subgroup (GL (Fin a) (Af E)))
    (hUo : IsOpen (U : Set (GL (Fin a) (Af E)))) (hUc : IsCompact (U : Set (GL (Fin a) (Af E))))
    (N : Set (GL (Fin a) (Cinf E))) (hN : N ∈ 𝓝 1) : ∃ f, IsDirac μ U N f := by
  classical
  have : ProperSpace (Lie E a) := FiniteDimensional.proper ℝ _
  have hv : (fun y : GL (Fin a) (Cinf E) => toL y.val) '' N ∈ 𝓝 (oneL E a) := isOpenEmbedding_val.isOpenMap.image_mem_nhds hN
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hv
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
  set m : ℝ := (n : ℝ) + 1 with hmd
  have hm : 0 < m := by positivity
  have hsub : Metric.closedBall (oneL E a) (1 / m) ⊆ (fun y : GL (Fin a) (Cinf E) => toL y.val) '' N :=
    (Metric.closedBall_subset_ball hn).trans hball
  let b : GL (Fin a) (Cinf E) → ℝ := fun y => bumpR E a m (toL y.val)
  have hb : Continuous b := (contDiff_bumpR m).continuous.comp isOpenEmbedding_val.continuous
  have hbc : ∀ (k : Kinf E a) y, b (Unitary.toUnits k * y * (Unitary.toUnits k)⁻¹) = b y := fun k y => bumpR_conj m k _
  let P := GeneralLinearGroup.map (n := Fin a) (pInf E)
  let Q := GeneralLinearGroup.map (n := Fin a) (pFin E)
  let χ : GL (Fin a) (Af E) → ℝ := (U : Set _).indicator 1
  have hχ : Continuous χ := IsClopen.continuous_indicator ⟨U.isClosed_of_isOpen hUo, hUo⟩ continuous_const
  have hχl : ∀ u ∈ U, ∀ k, χ (u * k) = χ k := fun u hu k => by
    simp only [χ, Set.indicator, SetLike.mem_coe, U.mul_mem_cancel_left hu]; rfl
  have hχi : ∀ k, χ k⁻¹ = χ k := fun k => by
    simp only [χ, Set.indicator, SetLike.mem_coe, inv_mem_iff]; rfl
  have hχ0 : ∀ k, 0 ≤ χ k := fun k => Set.indicator_nonneg (fun _ _ => zero_le_one) k
  let f₀ : GA E a → ℝ := fun g => b (P g) * b (P g)⁻¹ * χ (Q g)
  have hc : Continuous f₀ := ((hb.comp cP).mul (hb.comp cP.inv)).mul (hχ.comp cQ)
  have h0 : ∀ g, 0 ≤ f₀ g := fun g => mul_nonneg (mul_nonneg (bumpR_nonneg _ _) (bumpR_nonneg _ _)) (hχ0 _)
  have hsm : ∀ g, f₀ g ≠ 0 → toL (P g).val ∈ Metric.closedBall (oneL E a) (1 / m) ∧ Q g ∈ U := fun g h =>
    ⟨(dist_lt_of_bumpR_ne_zero hm (left_ne_zero_of_mul (left_ne_zero_of_mul h))).le,
      Set.mem_of_indicator_ne_zero (right_ne_zero_of_mul h)⟩
  have hK : IsCompact ((fun y : GL (Fin a) (Cinf E) => toL y.val) ⁻¹' Metric.closedBall (oneL E a) (1 / m)) :=
    isOpenEmbedding_val.isInducing.isCompact_preimage' (isCompact_closedBall (oneL E a) (1 / m))
      (hsub.trans (Set.image_subset_range _ _))
  have hcs : HasCompactSupport f₀ := by
    refine HasCompactSupport.intro ((hK.prod hUc).image
      ((continuous_infGL.comp continuous_fst).mul (cF.comp continuous_snd))) fun g hg => ?_
    by_contra h
    exact hg ⟨(P g, Q g), hsm g h, infGL_mul_finGL g⟩
  have h1 : f₀ 1 = 1 := by
    have : b 1 = 1 := bumpR_one m
    simp [f₀, this, χ]
  have hpos : 0 < ∫ g, f₀ g ∂μ := hc.integral_pos_of_hasCompactSupport_nonneg_nonzero hcs h0 (x := 1) (by rw [h1]; norm_num)
  set c := (∫ g, f₀ g ∂μ)⁻¹
  have hsym : ∀ g, f₀ g⁻¹ = f₀ g := fun g => by
    simp only [f₀, map_inv, inv_inv, hχi, mul_comm (b (P g))]
  have hleft : ∀ u ∈ U, ∀ g, f₀ (finGL E a u * g) = f₀ g := fun u hu g => by
    simp only [f₀, P, Q, map_mul, pInf_finGL, pFin_finGL, one_mul, hχl u hu]
  refine ⟨fun g => ((c * f₀ g : ℝ) : ℂ), ⟨Complex.continuous_ofReal.comp (continuous_const.mul hc), ?_, ?_, ?_⟩,
    fun g => ⟨?_, Complex.ofReal_im _⟩, ?_, fun g => by rw [hsym], fun k g => ?_, fun u hu g => by rw [hleft u hu],
    fun g hg => ?_⟩
  · exact hcs.comp_left (g := fun x : ℝ => ((c * x : ℝ) : ℂ)) (by simp)
  · intro g
    have e1 : ContDiffOn ℝ ∞ (fun x : Lie E a => bumpR E a m (lmul (toL (P g).val) x)) (invSet E a) :=
      (cd1 m (lmul (toL (P g).val))).contDiffOn
    have e2 : ContDiffOn ℝ ∞ (fun x : Lie E a => bumpR E a m (rmul (toL ((P g)⁻¹).val) (toL (Matrix.of x)⁻¹))) (invSet E a) :=
      (cd1 m (rmul (toL ((P g)⁻¹ : GL (Fin a) (Cinf E)).val))).comp_contDiffOn contDiffOn_invL
    refine (Complex.ofRealCLM.contDiff.comp_contDiffOn
      (((e1.mul e2).mul (contDiffOn_const (c := χ (Q g)))).const_smul c)).congr ?_
    rintro x ⟨u, hu⟩
    obtain rfl : x = toL u.val := hu.symm
    rw [chart_val, hsym]
    simp only [f₀, P, Q, map_mul, pInf_infGL, pFin_infGL, mul_one, _root_.mul_inv_rev]
    have : (Matrix.of (toL u.val))⁻¹ = (u⁻¹).val := (Matrix.coe_units_inv u).symm
    simp only [Function.comp_apply, this]
    rfl
  · let S : Subgroup (GL (Fin a) (Af E)) :=
      { carrier := {k | ∀ g, ((c * f₀ (finGL E a k * g) : ℝ) : ℂ) = ((c * f₀ g : ℝ) : ℂ)}
        one_mem' := fun g => by rw [map_one, one_mul]
        mul_mem' := fun {x y} hx hy g => by rw [map_mul, mul_assoc, hx, hy]
        inv_mem' := fun {x} hx g => (hx (finGL E a x⁻¹ * g)).symm.trans (by rw [← mul_assoc (finGL E a x), ← map_mul, mul_inv_cancel, map_one, one_mul]) }
    exact Subgroup.isOpen_mono (H₁ := U) (H₂ := S) (fun u hu g => by rw [hleft u hu]) hUo
  · exact mul_nonneg (inv_nonneg.2 hpos.le) (h0 g)
  · rw [integral_complex_ofReal, integral_const_mul, inv_mul_cancel₀ hpos.ne']; simp
  · refine congrArg (fun t : ℝ => ((c * t : ℝ) : ℂ)) (?_ : f₀ _ = f₀ _)
    simp only [f₀, P, Q, map_mul, pInf_infGL, pFin_infGL, mul_one, one_mul, _root_.mul_inv_rev]
    rw [← hbc k (GeneralLinearGroup.map (pInf E) g * _), ← hbc k ((Unitary.toUnits k)⁻¹ * _)]
    simp only [mul_assoc, mul_inv_cancel, mul_one, mul_inv_cancel_left]
  · have h : f₀ g ≠ 0 := fun e => hg (by simp [e])
    obtain ⟨y, hy, e⟩ := hsub (hsm g h).1
    obtain rfl : y = P g := Units.ext e
    exact ⟨_, hy, _, (hsm g h).2, (infGL_mul_finGL g).symm⟩

theorem one_mem_smv (μ : Measure (GA E 1)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] : oneFn E 1 ∈ smv μ ⊤ := by
  have h : MemL2Quotient (latticeGL E 1) μ (oneFn E 1).1 := memL2_of_rank_one continuous_const fun _ _ _ => rfl
  refine mem_smv.2 fun l => ?_
  induction l using List.reverseRecOn with
  | nil =>
    have e : word ([] : List (Lie E 1)) (oneFn E 1) = oneFn E 1 := by simp [word]
    rw [e]
    refine ⟨one_mem_cuspCont_iff.2 le_rfl, ?_, ⟨1, fun g => by simp [oneFn]⟩, h.toL2, trivial, h.lift_toL2_ae_eq⟩
    have : {k | finRep E 1 k (oneFn E 1) = oneFn E 1} = Set.univ := Set.eq_univ_of_forall fun k => rfl
    rw [this]; exact isOpen_univ
  | append_singleton l X _ =>
    have e : word (l ++ [X]) (oneFn E 1) = 0 := by simp [word, List.map_append, List.prod_append, lie_oneFn]
    rw [e]; exact zero_mem _

theorem smv_top_ne_bot (μ : Measure (GA E 1)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] :
    smv μ (⊤ : Submodule ℂ (L2 (latticeGL E 1) μ)) ≠ ⊥ := by
  intro h
  have h1 := one_mem_smv μ
  rw [h, Submodule.mem_bot] at h1
  have h2 := congrFun (congrArg Subtype.val h1) 1
  simp [oneFn] at h2

theorem exists_isDirac' (μ : Measure (GA E a)) [μ.IsHaarMeasure] (N : Set (GL (Fin a) (Cinf E))) (hN : N ∈ 𝓝 1) :
    ∃ U f, IsDirac μ U N f ∧ IsTestGL f ∧ f ≠ 0 := by
  have h := GlobalTheory.GLIntegral.exists_isOpen_isCompact E a
  obtain ⟨U, hU⟩ := h
  obtain ⟨f, hf⟩ := exists_isDirac μ U hU.1 (by first | exact hU.2 | exact hU.2.1) N hN
  refine ⟨U, f, hf, hf.test, fun e => ?_⟩
  have := hf.mass
  simp [e] at this
end GlobalTheory.GLFin.Inhab
end
