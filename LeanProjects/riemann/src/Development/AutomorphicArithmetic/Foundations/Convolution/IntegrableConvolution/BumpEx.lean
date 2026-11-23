import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.TensSmooth
import GroundTheory.AutomorphicForms.L2LocalComponents.ArchBump
import GroundTheory.AutomorphicForms.CuspidalProjection.OrthogonalProjectionOntoCompSubtypeL

noncomputable section

open MeasureTheory NumberField Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open scoped InnerProductSpace ComplexConjugate ContDiff Matrix

namespace UpperTheory.ConvolutionTheory.L1

private theorem frob_left {𝕜 : Type*} [RCLike 𝕜] {n : ℕ} {U : Matrix (Fin n) (Fin n) 𝕜}
    (hU : U ∈ Matrix.unitaryGroup (Fin n) 𝕜) (M : Matrix (Fin n) (Fin n) 𝕜) :
    frobSq (U * M) = frobSq M := by
  apply RCLike.ofReal_injective (K := 𝕜)
  have h1 : star U * U = 1 := Matrix.mem_unitaryGroup_iff'.1 hU
  rw [Matrix.star_eq_conjTranspose] at h1
  rw [frobSq_eq_trace, frobSq_eq_trace, Matrix.conjTranspose_mul, Matrix.mul_assoc,
    ← Matrix.mul_assoc Uᴴ, h1, Matrix.one_mul]

private theorem frob_right {𝕜 : Type*} [RCLike 𝕜] {n : ℕ} {U : Matrix (Fin n) (Fin n) 𝕜}
    (hU : U ∈ Matrix.unitaryGroup (Fin n) 𝕜) (M : Matrix (Fin n) (Fin n) 𝕜) :
    frobSq (M * U) = frobSq M := by
  have h1 : U * star U = 1 := Matrix.mem_unitaryGroup_iff.1 hU
  have h2 := frobSq_conj hU (M * U)
  rw [Matrix.mul_assoc U, Matrix.mul_assoc M, h1, Matrix.mul_one] at h2
  rw [← h2, frob_left hU]

section
variable {K : Type} [Field K] [NumberField K] {n : ℕ}

private theorem quad_left {k : archGroup K n} (hk : k ∈ archCompact K n) (X : ArchMatrix K n) :
    archQuad (archVal k * X) = archQuad X := by
  simp only [archQuad, map_mul, frob_left (realCompM_mem_unitaryGroup hk _),
    frob_left (complexCompM_mem_unitaryGroup hk _)]

private theorem quad_right {k : archGroup K n} (hk : k ∈ archCompact K n) (X : ArchMatrix K n) :
    archQuad (X * archVal k) = archQuad X := by
  simp only [archQuad, map_mul, frob_right (realCompM_mem_unitaryGroup hk _),
    frob_right (complexCompM_mem_unitaryGroup hk _)]

private theorem quad_bound (R : ℝ) : ∃ D : ℝ, ∀ X : ArchMatrix K n, archQuad X < R → ‖X‖ ≤ D := by
  obtain ⟨m, hm, hmδ⟩ := exists_archQuad_lt (K := K) (n := n) one_pos
  set R' := max R 1
  have hR' : 0 < R' := lt_of_lt_of_le one_pos (le_max_right _ _)
  set t : ℝ := Real.sqrt (m / (2 * R'))
  have ht : 0 < t := Real.sqrt_pos.2 (by positivity)
  have ht2 : t ^ 2 = m / (2 * R') := Real.sq_sqrt (by positivity)
  refine ⟨1 / t, fun X hX => ?_⟩
  have h1 : archQuad (t • X) < m := by
    rw [archQuad_smul, ht2]
    have h2 : archQuad X < R' := lt_of_lt_of_le hX (le_max_left _ _)
    have h3 : m / (2 * R') * archQuad X ≤ m / (2 * R') * R' :=
      mul_le_mul_of_nonneg_left h2.le (by positivity)
    have h4 : m / (2 * R') * R' = m / 2 := by field_simp
    linarith
  have h2 := hmδ _ h1
  rw [_root_.norm_smul, Real.norm_eq_abs, abs_of_pos ht] at h2
  rw [le_div_iff₀ ht]
  linarith

private theorem exists_cut : ∃ c : archGroup K n → ℝ, (∀ a, 0 ≤ c a) ∧ c 1 ≠ 0 ∧ Continuous c ∧ HasCompactSupport c ∧
    (∀ k ∈ archCompact K n, ∀ a, c (k * a) = c a) ∧
    ∀ g, ContDiff ℝ ∞ (fun Y : archLie K n => c (g * (isExpLieAlgebra K n).expG Y)) := by
  set R : ℝ := |archQuad (1 : ArchMatrix K n)| + 1 with hR
  have hR0 : 0 < R := by positivity
  set β : ContDiffBump (0 : ℝ) := ⟨R, R + 1, hR0, by linarith⟩
  have hβ0 : ∀ x : ℝ, β x ≠ 0 → x < R + 1 := by
    intro x hx
    have : x ∈ Function.support β := hx
    rw [β.support_eq, Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at this
    exact lt_of_le_of_lt (le_abs_self x) this
  set c : archGroup K n → ℝ := fun a => β (archQuad (archVal a)) * β (archQuad (archVal a⁻¹)) with hc
  have hsm : ∀ g, ContDiff ℝ ∞ (fun Y : archLie K n => c (g * (isExpLieAlgebra K n).expG Y)) := by
    intro g
    have e : (fun Y : archLie K n => c (g * (isExpLieAlgebra K n).expG Y)) = fun Y : archLie K n =>
        β (archQuad (archVal g * NormedSpace.exp (Y : ArchMatrix K n))) *
          β (archQuad (NormedSpace.exp (-(Y : ArchMatrix K n)) * archVal g⁻¹)) := by
      funext Y
      simp only [hc, archVal, _root_.mul_inv_rev, Subgroup.coe_mul, Units.val_mul,
        ← IsExpLieAlgebra.expG_neg, IsExpLieAlgebra.coe_expG]
      rfl
    rw [e]
    have hY : ContDiff ℝ ∞ (fun Y : archLie K n => (Y : ArchMatrix K n)) :=
      (Submodule.subtypeL (archLie K n)).contDiff
    have hexp : ContDiff ℝ ∞ (NormedSpace.exp : ArchMatrix K n → ArchMatrix K n) :=
      contDiff_exp ℝ _
    have hq : ContDiff ℝ ∞ (archQuad : ArchMatrix K n → ℝ) := contDiff_archQuad.of_le le_top
    refine ContDiff.mul ?_ ?_
    · exact β.contDiff.comp (hq.comp (contDiff_const.mul (hexp.comp hY)))
    · exact β.contDiff.comp (hq.comp ((hexp.comp hY.neg).mul contDiff_const))
  have hqc : Continuous (archQuad : ArchMatrix K n → ℝ) := (contDiff_archQuad (K := K) (n := n)).continuous
  have hcont : Continuous c :=
    (β.continuous.comp (hqc.comp continuous_archVal)).mul
      (β.continuous.comp (hqc.comp continuous_archVal_inv))
  refine ⟨c, fun a => mul_nonneg β.nonneg β.nonneg, ?_, hcont, ?_, ?_, hsm⟩
  · have h0 : β (archQuad (1 : ArchMatrix K n)) = 1 :=
      β.one_of_mem_closedBall (by
        rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs]
        show _ ≤ R
        linarith)
    simp only [hc, inv_one, archVal, OneMemClass.coe_one, Units.val_one, h0, mul_one]
    exact one_ne_zero
  · obtain ⟨D, hD⟩ := quad_bound (K := K) (n := n) (R + 1)
    set C : Set (ArchMatrix K n × (ArchMatrix K n)ᵐᵒᵖ) :=
      Metric.closedBall 0 D ×ˢ (MulOpposite.op '' Metric.closedBall 0 D)
    have hC : IsCompact C := (isCompact_closedBall _ _).prod
      ((isCompact_closedBall _ _).image MulOpposite.continuous_op)
    refine HasCompactSupport.intro (isClosedEmbedding_archPair.isCompact_preimage hC) fun a ha => ?_
    by_contra h0
    have h1 : β (archQuad (archVal a)) ≠ 0 := left_ne_zero_of_mul h0
    have h2 : β (archQuad (archVal a⁻¹)) ≠ 0 := right_ne_zero_of_mul h0
    refine ha ⟨Metric.mem_closedBall.2 ?_, ⟨archVal a⁻¹, Metric.mem_closedBall.2 ?_, rfl⟩⟩
    · rw [dist_zero_right]; exact hD _ (hβ0 _ h1)
    · rw [dist_zero_right]; exact hD _ (hβ0 _ h2)
  · intro k hk a
    have e1 : archVal (k * a) = archVal k * archVal a := rfl
    have e2 : archVal (k * a)⁻¹ = archVal a⁻¹ * archVal k⁻¹ := by
      rw [_root_.mul_inv_rev]; rfl
    simp only [hc, e1, e2, quad_left hk, quad_right (inv_mem hk)]

private def Good (P : archGroup K n → ℂ) : Prop :=
  (isExpLieAlgebra K n).IsSmoothFun P ∧ ∃ W : Submodule ℂ (archGroup K n → ℂ), W.FG ∧
    ∀ k : archCompact K n, (fun g => P ((k : archGroup K n) * g)) ∈ W

private theorem Good.cont {P : archGroup K n → ℂ} (h : Good P) : Continuous P := by
  letI := (isExpLieAlgebra K n).chartedSpace
  exact ContMDiff.continuous h.1

private theorem Good.add {P Q : archGroup K n → ℂ} (hP : Good P) (hQ : Good Q) :
    Good (fun g => P g + Q g) := by
  obtain ⟨h1, W₁, f1, k1⟩ := hP
  obtain ⟨h2, W₂, f2, k2⟩ := hQ
  refine ⟨?_, W₁ ⊔ W₂, f1.sup f2, fun k => Submodule.add_mem_sup (k1 k) (k2 k)⟩
  rw [IsExpLieAlgebra.isSmoothFun_iff] at h1 h2 ⊢
  exact fun g => (h1 g).add (h2 g)

private theorem Good.mul {P Q : archGroup K n → ℂ} (hP : Good P) (hQ : Good Q) :
    Good (fun g => P g * Q g) := by
  obtain ⟨h1, W₁, f1, k1⟩ := hP
  obtain ⟨h2, W₂, f2, k2⟩ := hQ
  refine ⟨?_, W₁ * W₂, f1.mul f2, fun k => Submodule.mul_mem_mul (k1 k) (k2 k)⟩
  rw [IsExpLieAlgebra.isSmoothFun_iff] at h1 h2 ⊢
  exact fun g => (h1 g).mul (h2 g)

private theorem Good.const (z : ℂ) : Good (fun _ : archGroup K n => z) := by
  refine ⟨?_, Submodule.span ℂ {fun _ => (1 : ℂ)}, Submodule.fg_span_singleton _, fun k =>
    Submodule.mem_span_singleton.2 ⟨z, by ext; simp⟩⟩
  rw [IsExpLieAlgebra.isSmoothFun_iff]
  exact fun g => contDiff_const

private theorem Good.conj {P : archGroup K n → ℂ} (hP : Good P) : Good (fun g => conj (P g)) := by
  obtain ⟨h1, W, f1, k1⟩ := hP
  refine ⟨?_, W.map (starLinearEquiv ℂ (A := archGroup K n → ℂ)).toLinearMap, f1.map _, fun k =>
    Submodule.mem_map_of_mem (k1 k)⟩
  rw [IsExpLieAlgebra.isSmoothFun_iff] at h1 ⊢
  exact fun g => Complex.conjCLE.contDiff.comp (h1 g)

private theorem coord_mul {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ (ArchMatrix K n)) (i : ι)
    (a x : ArchMatrix K n) : b.coord i (a * x) = ∑ j, b.coord j x * b.coord i (a * b j) := by
  let L : ArchMatrix K n →ₗ[ℝ] ℝ := (b.coord i).comp (LinearMap.mulLeft ℝ a)
  have h : L x = ∑ j, b.repr x j • L (b j) := by
    conv_lhs => rw [← b.sum_repr x]
    rw [map_sum]
    simp only [map_smul]
  exact h

private theorem good_coord {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ (ArchMatrix K n)) (i : ι) :
    Good (fun g : archGroup K n => ((b.coord i (archVal g) : ℝ) : ℂ)) := by
  refine ⟨?_, Submodule.span ℂ (Set.range fun (j : ι) (g : archGroup K n) =>
    ((b.coord j (archVal g) : ℝ) : ℂ)), Submodule.fg_span (Set.finite_range _), fun k => ?_⟩
  · rw [IsExpLieAlgebra.isSmoothFun_iff]
    intro g
    have e : (fun Y : archLie K n => ((b.coord i (archVal (g * (isExpLieAlgebra K n).expG Y)) : ℝ) : ℂ)) =
        fun Y : archLie K n => ((b.coord i (archVal g * NormedSpace.exp (Y : ArchMatrix K n)) : ℝ) : ℂ) := by
      funext Y
      simp only [archVal, Subgroup.coe_mul, Units.val_mul, IsExpLieAlgebra.coe_expG]
    rw [e]
    have hY : ContDiff ℝ ∞ (fun Y : archLie K n => (Y : ArchMatrix K n)) :=
      (Submodule.subtypeL (archLie K n)).contDiff
    have hexp : ContDiff ℝ ∞ (NormedSpace.exp : ArchMatrix K n → ArchMatrix K n) :=
      contDiff_exp ℝ _
    exact Complex.ofRealCLM.contDiff.comp ((LinearMap.toContinuousLinearMap (b.coord i)).contDiff.comp
      (contDiff_const.mul (hexp.comp hY)))
  · have e : (fun g : archGroup K n => ((b.coord i (archVal ((k : archGroup K n) * g)) : ℝ) : ℂ)) =
        ∑ j, ((b.coord i (archVal (k : archGroup K n) * b j) : ℝ) : ℂ) •
          fun g : archGroup K n => ((b.coord j (archVal g) : ℝ) : ℂ) := by
      funext g
      have e1 : archVal ((k : archGroup K n) * g) = archVal (k : archGroup K n) * archVal g := rfl
      rw [e1, coord_mul b i]
      simp [Finset.sum_apply, mul_comm]
    rw [e]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

private def polS (C : Set (archGroup K n)) : StarSubalgebra ℂ C(C, ℂ) where
  carrier := {f | ∃ P : archGroup K n → ℂ, Good P ∧ ∀ x : C, f x = P x}
  mul_mem' := by
    rintro f g ⟨P, hP, hf⟩ ⟨Q, hQ, hg⟩
    exact ⟨_, hP.mul hQ, fun x => by simp [hf, hg]⟩
  add_mem' := by
    rintro f g ⟨P, hP, hf⟩ ⟨Q, hQ, hg⟩
    exact ⟨_, hP.add hQ, fun x => by simp [hf, hg]⟩
  algebraMap_mem' := fun z => ⟨_, Good.const z, fun x => by rw [Algebra.algebraMap_eq_smul_one]; simp⟩
  star_mem' := by
    rintro f ⟨P, hP, hf⟩
    exact ⟨_, hP.conj, fun x => by simp [hf]⟩

private theorem exists_good_near {C : Set (archGroup K n)} (hC : IsCompact C) (f : archGroup K n → ℂ)
    (hf : Continuous f) {ε : ℝ} (hε : 0 < ε) :
    ∃ P : archGroup K n → ℂ, Good P ∧ ∀ x ∈ C, ‖P x - f x‖ < ε := by
  haveI : CompactSpace C := isCompact_iff_compactSpace.1 hC
  set b := Module.finBasis ℝ (ArchMatrix K n)
  have hsep : (polS C).SeparatesPoints := by
    intro x y hxy
    obtain ⟨i, hi⟩ : ∃ i, b.coord i (archVal (x : archGroup K n)) ≠ b.coord i (archVal (y : archGroup K n)) := by
      by_contra hall
      push_neg at hall
      refine hxy (Subtype.ext (Subtype.ext (Units.ext (b.ext_elem fun i => ?_))))
      exact hall i
    have hG := good_coord b i
    refine ⟨_, ⟨⟨fun x : C => ((b.coord i (archVal (x : archGroup K n)) : ℝ) : ℂ),
      hG.cont.comp continuous_subtype_val⟩, ⟨_, hG, fun x => rfl⟩, rfl⟩, ?_⟩
    simpa using hi
  have htop := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints (polS C) hsep
  set f' : C(C, ℂ) := ⟨fun x => f x, hf.comp continuous_subtype_val⟩
  have hmem : f' ∈ ((polS C).topologicalClosure : Set C(C, ℂ)) := by rw [htop]; trivial
  rw [StarSubalgebra.topologicalClosure_coe, Metric.mem_closure_iff] at hmem
  obtain ⟨s, ⟨P, hP, hs⟩, hd⟩ := hmem ε hε
  refine ⟨P, hP, fun x hx => ?_⟩
  have h1 := ContinuousMap.dist_apply_le_dist (f := f') (g := s) (⟨x, hx⟩ : C)
  have h2 : dist (f' ⟨x, hx⟩) (s ⟨x, hx⟩) = ‖P x - f x‖ := by
    rw [dist_comm, dist_eq_norm, hs]; rfl
  linarith

end

end UpperTheory.ConvolutionTheory.L1

open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.L1

theorem UpperTheory.ConvolutionTheory.L1.bumpEx :
    UpperTheory.ConvolutionTheory.L1.BumpEx := by
  intro K _ _ n ν _ H _ _ _ π v hv
  obtain ⟨c, hc0, hc1, hcc, hcs, hcK, hcsm⟩ := exists_cut (K := K) (n := n)
  set F : archGroup K n → ℂ := fun g => ⟪v, π g v⟫_ℂ with hFdef
  have hF : Continuous F := continuous_const.inner (π.continuous_orbit v)
  have hF1 : F 1 ≠ 0 := by
    simp [hFdef, hv]

  have hcG : Good (fun g : archGroup K n => ((c g : ℝ) : ℂ)) := by
    refine ⟨?_, Submodule.span ℂ {fun g => ((c g : ℝ) : ℂ)}, Submodule.fg_span_singleton _, fun k => ?_⟩
    · rw [IsExpLieAlgebra.isSmoothFun_iff]
      exact fun g => Complex.ofRealCLM.contDiff.comp (hcsm g)
    · have e : (fun g => ((c ((k : archGroup K n) * g) : ℝ) : ℂ)) = fun g => ((c g : ℝ) : ℂ) := by
        funext g; rw [hcK _ k.2]
      rw [e]
      exact Submodule.mem_span_singleton_self _
  set w : archGroup K n → ℝ := fun g => c g * ‖F g‖ ^ 2 with hwdef
  have hwc : Continuous w := hcc.mul (hF.norm.pow 2)
  have hws : HasCompactSupport w := hcs.mul_right
  have hJ : 0 < ∫ g, w g ∂ν := hwc.integral_pos_of_hasCompactSupport_nonneg_nonzero hws
    (fun g => mul_nonneg (hc0 g) (by positivity)) (x := 1)
    (mul_ne_zero hc1 (pow_ne_zero 2 (norm_ne_zero_iff.2 hF1)))
  set J := ∫ g, w g ∂ν
  set m : archGroup K n → ℝ := fun g => c g * ‖F g‖ with hmdef
  have hmc : Continuous m := hcc.mul hF.norm
  have hms : HasCompactSupport m := hcs.mul_right
  have hmi : Integrable m ν := hmc.integrable_of_hasCompactSupport hms
  set M := ∫ g, m g ∂ν
  have hM : 0 ≤ M := integral_nonneg fun g => mul_nonneg (hc0 g) (norm_nonneg _)
  set ε : ℝ := J / (2 * (M + 1)) with hεdef
  have hε : 0 < ε := by positivity
  have hεM : ε * M < J := by
    have h1 : ε * (M + 1) = J / 2 := by rw [hεdef]; field_simp
    nlinarith
  obtain ⟨P, hP, hPε⟩ := exists_good_near (K := K) (n := n) hcs.isCompact (fun g => conj (F g))
    (Complex.continuous_conj.comp hF) hε
  have hPc := hP.cont

  set I : ℂ := ∫ g, P g * (c g : ℂ) * F g ∂ν with hIdef
  have hI : I ≠ 0 := by
    intro h0
    have hi1 : Integrable (fun g => P g * (c g : ℂ) * F g) ν :=
      ((hPc.mul (Complex.continuous_ofReal.comp hcc)).mul hF).integrable_of_hasCompactSupport
        ((hcs.comp_left Complex.ofReal_zero).mul_left.mul_right)
    have hi2 : Integrable (fun g => ((w g : ℝ) : ℂ)) ν :=
      (hwc.integrable_of_hasCompactSupport hws).ofReal
    have h1 : ‖I - (J : ℂ)‖ ≤ ε * M := by
      have e : I - (J : ℂ) = ∫ g, (P g * (c g : ℂ) * F g - ((w g : ℝ) : ℂ)) ∂ν := by
        rw [integral_sub hi1 hi2, integral_complex_ofReal]
      rw [e, ← integral_const_mul]
      refine norm_integral_le_of_norm_le (hmi.const_mul ε) (Filter.Eventually.of_forall fun g => ?_)
      have e2 : P g * (c g : ℂ) * F g - ((w g : ℝ) : ℂ) = (P g - conj (F g)) * (c g : ℂ) * F g := by
        have e3 : conj (F g) * F g = ((‖F g‖ ^ 2 : ℝ) : ℂ) := by
          rw [Complex.conj_mul']; push_cast; rfl
        simp only [hwdef]
        push_cast at e3 ⊢
        linear_combination (c g : ℂ) * e3
      rw [e2, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hc0 g)]
      by_cases hg : g ∈ tsupport c
      · have := (hPε g hg).le
        simp only [hmdef]
        have h3 : 0 ≤ c g * ‖F g‖ := mul_nonneg (hc0 g) (norm_nonneg _)
        nlinarith
      · have : c g = 0 := image_eq_zero_of_notMem_tsupport hg
        simp [hmdef, this]
    rw [h0, zero_sub, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hJ] at h1
    linarith

  set B : ℝ := ∫ g, ‖P g * (c g : ℂ)‖ ∂ν with hBdef
  have hB : 0 ≤ B := integral_nonneg fun g => norm_nonneg _
  set t : ℝ := (1 + B)⁻¹ with htdef
  have ht : 0 < t := by positivity
  have hQ : Good (fun g => (t : ℂ) * (P g * (c g : ℂ))) := (Good.const (t : ℂ)).mul (hP.mul hcG)
  have hQs : HasCompactSupport (fun g => (t : ℂ) * (P g * (c g : ℂ))) :=
    ((hcs.comp_left Complex.ofReal_zero).mul_left).mul_left
  let b : TI K n := ⟨⟨fun g => (t : ℂ) * (P g * (c g : ℂ)), hQ.cont⟩, hQs⟩
  have hb : ∀ g, b g = (t : ℂ) * (P g * (c g : ℂ)) := fun g => rfl
  refine ⟨b, hQ.1, ?_, ?_, fun h0 => ?_⟩
  · obtain ⟨W, hW, hk⟩ := hQ.2
    haveI : FiniteDimensional ℂ W := Module.Finite.iff_fg.2 hW
    refine Submodule.finiteDimensional_of_le (S₂ := W) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    exact hk k
  · have e : (fun g => ‖b g‖) = fun g => t * ‖P g * (c g : ℂ)‖ := by
      funext g
      rw [hb, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
    rw [e, integral_const_mul, htdef, inv_mul_le_iff₀ (by positivity)]
    linarith
  · have hin := CuspidalProjection.inner_integrated_ccToL1 ν π b v v
    have hz : ⟪v, π.integrated ν (UnitaryRep.ccToL1 ν b) v⟫_ℂ = 0 := by
      rw [← ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.star_eq_adjoint, h0,
        inner_zero_left]
    have e : (fun g => b g * ⟪v, π g v⟫_ℂ) = fun g => (t : ℂ) * (P g * (c g : ℂ) * F g) := by
      funext g
      rw [hb, mul_assoc]
    rw [hz, e, integral_const_mul] at hin
    exact (mul_ne_zero (Complex.ofReal_ne_zero.2 ht.ne') hI) hin.symm
