import Mathlib
import GroundTheory.AutomorphicForms.HarishChandraRegularity.ContDiffCompCoordEquiv
import GroundTheory.AutomorphicForms.HarishChandraRegularity.ExpChart
import GroundTheory.AutomorphicForms.HarishChandraRegularity.ExpHaar
import GroundTheory.AutomorphicForms.HarishChandraRegularity.TupleOp
import GroundTheory.AutomorphicForms.GKModules.Casimir
import GroundTheory.AutomorphicForms.PartialDifferential.AnalyticHypoelliptic
import GroundTheory.AutomorphicForms.PartialDifferential.EllipticParametrix
import GroundTheory.AutomorphicForms.HarishChandraRegularity.CartanBasis

namespace GroundTheory.Automorphic

open Sobolev Set Filter Topology MeasureTheory
open scoped ContDiff Manifold

set_option linter.unusedSectionVars false

namespace Sobolev

variable {n : ℕ}

def sqSymbol {ι : Type*} [Fintype ι] (c : ι → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x ξ : EuclideanSpace ℝ (Fin n)) : ℂ :=
  ∑ i, (∑ j, ((c i x j : ℝ) : ℂ) * ((ξ j : ℝ) : ℂ)) ^ 2

theorem sqSymbol_eq {ι : Type*} [Fintype ι] (c : ι → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x ξ : EuclideanSpace ℝ (Fin n)) :
    sqSymbol c x ξ = ((∑ i, (inner ℝ (c i x) ξ) ^ 2 : ℝ) : ℂ) := by
  simp only [sqSymbol, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem exists_ball_sqSymbol_ne_zero {ι : Type*} [Fintype ι]
    {c : ι → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)} (hc : ∀ i, ContinuousAt (c i) 0)
    (hspan : ∀ ξ : EuclideanSpace ℝ (Fin n), (∀ i, inner ℝ (c i 0) ξ = 0) → ξ = 0) :
    ∃ δ > 0, ∀ x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ, ∀ ξ, ξ ≠ 0 → sqSymbol c x ξ ≠ 0 := by
  classical
  let Q : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) := fun x => ∑ i, (innerSL ℝ (c i x)).smulRight (c i x)
  have hQ : ∀ x ξ, Q x ξ = ∑ i, inner ℝ (c i x) ξ • c i x := by
    intro x ξ; simp [Q]
  have hquad : ∀ x ξ, inner ℝ (Q x ξ) ξ = ∑ i, (inner ℝ (c i x) ξ) ^ 2 := by
    intro x ξ
    rw [hQ, sum_inner]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [real_inner_smul_left, sq]
  have hzero : ∀ x ξ, ∑ i, (inner ℝ (c i x) ξ) ^ 2 = 0 → Q x ξ = 0 := by
    intro x ξ h0
    have hall := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => sq_nonneg (inner ℝ (c i x) ξ)).1 h0
    rw [hQ]
    exact Finset.sum_eq_zero fun i hi => by
      rw [pow_eq_zero_iff two_ne_zero |>.1 (hall i hi), zero_smul]
  have hinj : Function.Injective (Q 0) := by
    rw [injective_iff_map_eq_zero]
    intro ξ hξ
    apply hspan
    have h0 : ∑ i, (inner ℝ (c i 0) ξ) ^ 2 = 0 := by rw [← hquad, hξ, inner_zero_left]
    intro i
    exact pow_eq_zero_iff two_ne_zero |>.1
      ((Finset.sum_eq_zero_iff_of_nonneg fun i _ => sq_nonneg (inner ℝ (c i 0) ξ)).1 h0 i
        (Finset.mem_univ _))
  have hsurj : Function.Surjective (Q 0) :=
    LinearMap.injective_iff_surjective (f := ((Q 0 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
      EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))).1 hinj
  let e := ContinuousLinearEquiv.ofBijective (Q 0) (LinearMap.ker_eq_bot.2 hinj)
    (LinearMap.range_eq_top.2 hsurj)
  have hU : IsUnit (Q 0) :=
    ⟨(ContinuousLinearEquiv.unitsEquiv ℝ (EuclideanSpace ℝ (Fin n))).symm e, ContinuousLinearMap.ext fun _ => rfl⟩
  have hQc : ContinuousAt Q 0 := by
    rw [continuousAt_clm_apply]
    intro ξ
    simp only [hQ]
    exact tendsto_finsetSum _ fun i _ =>
      (Filter.Tendsto.inner (hc i) tendsto_const_nhds).smul (hc i)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 (hQc.preimage_mem_nhds (Units.isOpen.mem_nhds hU))
  refine ⟨δ, hδ, fun x hx ξ hξ hs => hξ ?_⟩
  obtain ⟨u, hu⟩ := hball hx
  rw [sqSymbol_eq, Complex.ofReal_eq_zero] at hs
  have h1 := hzero x ξ hs
  rw [← hu] at h1
  have h2 := congrArg (fun v => ((↑u⁻¹ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))) v) h1
  have h3 : ((↑u⁻¹ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) *
      (↑u : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))) ξ = 0 := by
    change (↑u⁻¹ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
      ((↑u : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) ξ) = 0
    rw [h1, map_zero]
  rw [Units.inv_mul] at h3
  simpa using h3

theorem integral_euclideanSpace_of_eq_zero {d : ℕ} (hd : d = 0) (F : EuclideanSpace ℝ (Fin d) → ℂ) :
    ∫ x, F x = F 0 := by
  subst hd
  rw [volume_euclideanSpace_eq_dirac, integral_dirac]

end Sobolev

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}

theorem coordEquiv_map_neg {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) (x : EuclideanSpace ℝ (Fin d)) :
    coordEquiv (b.map (LinearEquiv.neg ℝ)) x = -coordEquiv b x := by
  simp [coordEquiv_apply, Finset.sum_neg_distrib]

namespace IsExpLieAlgebra

variable (h : IsExpLieAlgebra G 𝔤)

def lieEquiv : h.lieSubalgebra ≃ₗ[ℝ] 𝔤 where
  toFun := h.ofLie
  invFun := h.toLie
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem lieEquiv_apply (X : h.lieSubalgebra) : h.lieEquiv X = h.ofLie X := rfl

theorem span_coord_of_basis {ι : Type*} [Fintype ι] (bL : Module.Basis ι ℝ h.lieSubalgebra) {d : ℕ}
    (b : Module.Basis (Fin d) ℝ 𝔤) (ξ : EuclideanSpace ℝ (Fin d))
    (hξ : ∀ i, inner ℝ ((coordEquiv b).symm (h.ofLie (bL i))) ξ = 0) : ξ = 0 := by
  have hall : ∀ v : h.lieSubalgebra, inner ℝ ((coordEquiv b).symm (h.lieEquiv v)) ξ = 0 := by
    intro v
    rw [← bL.sum_repr v, map_sum, map_sum, sum_inner]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [map_smul, map_smul, real_inner_smul_left, lieEquiv_apply, hξ i, mul_zero]
  have := hall (h.lieEquiv.symm (coordEquiv b ξ))
  rw [LinearEquiv.apply_symm_apply, ContinuousLinearEquiv.symm_apply_apply] at this
  exact inner_self_eq_zero.1 this

theorem laplacian_apply_coe {ι : Type*} [Fintype ι] (bL : Module.Basis ι ℝ h.lieSubalgebra)
    (w : h.smoothFuns (F := ℂ)) :
    ((h.laplacian bL w : h.smoothFuns (F := ℂ)) : G → ℂ) =
      ∑ i, h.rightDeriv (h.ofLie (bL i)) (h.rightDeriv (h.ofLie (bL i)) (w : G → ℂ)) := by
  simp [laplacian, LinearMap.sum_apply, Module.End.mul_apply]

theorem exists_tupleOp_laplacian_pow {ι : Type*} [Fintype ι] (bL : Module.Basis ι ℝ h.lieSubalgebra)
    {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩ : IsOpen Ω)
    (c : ι → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hc : ∀ i, AnalyticOnNhd ℝ (c i) Ω)
    (hR : ∀ i (F : G → ℂ), h.IsSmoothFun F → ∀ g : G, ∀ x ∈ Ω,
      h.rightDeriv (h.ofLie (bL i)) F (g * h.expG (coordEquiv b x)) =
        vfOp (c i) (fun y => F (g * h.expG (coordEquiv b y))) x)
    (k : ℕ) : ∃ a : (k : ℕ) → (Fin k → Fin d) → EuclideanSpace ℝ (Fin d) → ℂ,
      (∀ k' J, AnalyticOnNhd ℝ (a k' J) Ω) ∧
      (∀ x ∈ Ω, ∀ ξ, tupleSymbol (2 * k) a x ξ = sqSymbol c x ξ ^ k) ∧
      ∀ (F : h.smoothFuns (F := ℂ)) (g : G), ∀ x ∈ Ω,
        ((((h.laplacian bL) ^ k) F : h.smoothFuns (F := ℂ)) : G → ℂ) (g * h.expG (coordEquiv b x)) =
          tupleOp (2 * k) a (fun y => (F : G → ℂ) (g * h.expG (coordEquiv b y))) x := by
  induction k with
  | zero =>
    refine ⟨idCoeff, fun k J => analyticOnNhd_idCoeff k J Ω,
      fun x _ ξ => by simpa using tupleSymbol_idCoeff x ξ, fun F g x _ => ?_⟩
    simp [tupleOp_idCoeff]
  | succ k ih =>
    obtain ⟨a, ha, hs, hop⟩ := ih
    have s1 := fun i => exists_vfOp_tupleOp (hc i) (m := 2 * k) ha
    choose a1 ha1 hs1 hop1 using s1
    have s2 := fun i => exists_vfOp_tupleOp (hc i) (m := 2 * k + 1) (ha1 i)
    choose a2 ha2 hs2 hop2 using s2
    have e2 : 2 * (k + 1) = 2 * k + 1 + 1 := by ring
    refine ⟨∑ i, a2 i, fun k' J => ?_, fun x hx ξ => ?_, fun F g x hx => ?_⟩
    · have : (∑ i, a2 i) k' J = ∑ i, a2 i k' J := by ext y; simp [Finset.sum_apply]
      rw [this]; exact Finset.analyticOnNhd_sum _ fun i _ => ha2 i k' J
    · rw [e2, tupleSymbol_sum]
      simp only [hs2 _ x, hs1 _ x, hs x hx]
      rw [pow_succ', sqSymbol, Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by ring
    · set u := fun y => (F : G → ℂ) (g * h.expG (coordEquiv b y)) with hu_def
      have hu : ContDiff ℝ ∞ u := h.contDiff_comp_coordEquiv F.2 g b
      rw [pow_succ', Module.End.mul_apply, laplacian_apply_coe, Finset.sum_apply, e2, tupleOp_sum]
      set w := ((h.laplacian bL) ^ k) F
      have hw : h.IsSmoothFun (w : G → ℂ) := w.2
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hR i _ (h.isSmoothFun_rightDeriv hw _) g x hx]
      have E1 : EqOn (fun y => h.rightDeriv (h.ofLie (bL i)) (w : G → ℂ) (g * h.expG (coordEquiv b y)))
          (vfOp (c i) (fun y => (w : G → ℂ) (g * h.expG (coordEquiv b y)))) Ω :=
        fun y hy => hR i _ hw g y hy
      have E2 : EqOn (fun y => (w : G → ℂ) (g * h.expG (coordEquiv b y))) (tupleOp (2 * k) a u) Ω :=
        fun y hy => hop F g y hy
      have E3 : EqOn (vfOp (c i) (fun y => (w : G → ℂ) (g * h.expG (coordEquiv b y))))
          (tupleOp (2 * k + 1) (a1 i) u) Ω :=
        fun y hy => (vfOp_congr_of_eqOn hΩ E2 (c i) hy).trans (hop1 i u hu y hy)
      rw [vfOp_congr_of_eqOn hΩ (E1.trans E3) (c i) hx, hop2 i u hu x hx]

theorem exists_tupleOp_aeval_laplacian {ι : Type*} [Fintype ι] (bL : Module.Basis ι ℝ h.lieSubalgebra)
    {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩ : IsOpen Ω)
    (c : ι → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hc : ∀ i, AnalyticOnNhd ℝ (c i) Ω)
    (hR : ∀ i (F : G → ℂ), h.IsSmoothFun F → ∀ g : G, ∀ x ∈ Ω,
      h.rightDeriv (h.ofLie (bL i)) F (g * h.expG (coordEquiv b x)) =
        vfOp (c i) (fun y => F (g * h.expG (coordEquiv b y))) x)
    (P : Polynomial ℂ) (hP : P.Monic) :
    ∃ a : (k : ℕ) → (Fin k → Fin d) → EuclideanSpace ℝ (Fin d) → ℂ,
      (∀ k J, AnalyticOnNhd ℝ (a k J) Ω) ∧
      (∀ x ∈ Ω, ∀ ξ, tupleSymbol (2 * P.natDegree) a x ξ = sqSymbol c x ξ ^ P.natDegree) ∧
      ∀ (F : h.smoothFuns (F := ℂ)) (g : G), ∀ x ∈ Ω,
        ((Polynomial.aeval (h.laplacian bL) P F : h.smoothFuns (F := ℂ)) : G → ℂ)
            (g * h.expG (coordEquiv b x)) =
          tupleOp (2 * P.natDegree) a (fun y => (F : G → ℂ) (g * h.expG (coordEquiv b y))) x := by
  classical
  set N := P.natDegree with hN
  have s := fun i => h.exists_tupleOp_laplacian_pow bL b hΩ c hc hR i
  choose a ha hs hop using s
  let a' : ℕ → (k : ℕ) → (Fin k → Fin d) → EuclideanSpace ℝ (Fin d) → ℂ :=
    fun i => P.coeff i • raiseCoeff (2 * i) (a i)
  refine ⟨∑ i ∈ Finset.range (N + 1), a' i, fun k J => ?_, fun x hx ξ => ?_, fun F g x hx => ?_⟩
  · exact analyticOnNhd_sum_coeff _
      (fun i _ => analyticOnNhd_smul_coeff _ (analyticOnNhd_raiseCoeff _ (ha i))) k J
  · rw [tupleSymbol_sum, Finset.sum_range_succ, Finset.sum_eq_zero, zero_add]
    · simp only [a']
      rw [tupleSymbol_smul, tupleSymbol_raiseCoeff, hs N x hx, show P.coeff N = 1 from hP.coeff_natDegree,
        one_mul]
    · intro i hi
      simp only [a']
      rw [tupleSymbol_smul, tupleSymbol_raiseCoeff_of_lt (by simp at hi; omega), mul_zero]
  · rw [Polynomial.aeval_eq_sum_range, LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply,
      tupleOp_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    simp only [a']
    rw [LinearMap.smul_apply, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, hop i F g x hx,
      tupleOp_smul, tupleOp_raiseCoeff (by simp at hi; omega)]

theorem exists_elliptic_aeval_laplacian {ι : Type*} [Fintype ι] (bL : Module.Basis ι ℝ h.lieSubalgebra)
    {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) (P : Polynomial ℂ) (hP : P.Monic) :
    ∃ δ > 0, ∃ (A : Finset (Fin d → ℕ)) (a : (Fin d → ℕ) → EuclideanSpace ℝ (Fin d) → ℂ),
      (∀ α ∈ A, mabs α ≤ 2 * P.natDegree) ∧
      (∀ α ∈ A, AnalyticOn ℝ (a α) (Metric.ball 0 δ)) ∧
      (∀ x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) δ, ∀ ξ, ξ ≠ 0 →
        prinSymbol A a (2 * P.natDegree) x ξ ≠ 0) ∧
      ∀ (F : h.smoothFuns (F := ℂ)) (g : G), ∀ x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) δ,
        diffOp A a (fun y => (F : G → ℂ) (g * h.expG (coordEquiv b y))) x =
          ((Polynomial.aeval (h.laplacian bL) P F : h.smoothFuns (F := ℂ)) : G → ℂ)
            (g * h.expG (coordEquiv b x)) := by
  obtain ⟨r, hr, cX, hcan, hc0, hchart⟩ := h.exists_expChart_coeff b
  set c : ι → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) := fun i => cX (h.ofLie (bL i))
  have hcont : ∀ i, ContinuousAt (c i) 0 := fun i =>
    (hcan _ 0 (Metric.mem_ball_self hr)).continuousAt
  have hspan : ∀ ξ : EuclideanSpace ℝ (Fin d), (∀ i, inner ℝ (c i 0) ξ = 0) → ξ = 0 := by
    intro ξ hξ
    exact h.span_coord_of_basis bL b ξ fun i => by rw [← hc0]; exact hξ i
  obtain ⟨δ₀, hδ₀, hell⟩ := exists_ball_sqSymbol_ne_zero hcont hspan
  set δ := min r δ₀
  have hδ : 0 < δ := lt_min hr hδ₀
  have hΩr : Metric.ball (0 : EuclideanSpace ℝ (Fin d)) δ ⊆ Metric.ball 0 r :=
    Metric.ball_subset_ball (min_le_left _ _)
  have hΩδ : Metric.ball (0 : EuclideanSpace ℝ (Fin d)) δ ⊆ Metric.ball 0 δ₀ :=
    Metric.ball_subset_ball (min_le_right _ _)
  have hR : ∀ i (F : G → ℂ), h.IsSmoothFun F → ∀ g : G, ∀ x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) δ,
      h.rightDeriv (h.ofLie (bL i)) F (g * h.expG (coordEquiv b x)) =
        vfOp (c i) (fun y => F (g * h.expG (coordEquiv b y))) x := fun i F hF g x hx =>
    hchart _ F hF g x (hΩr hx)
  obtain ⟨a, ha, hs, hop⟩ := h.exists_tupleOp_aeval_laplacian bL b Metric.isOpen_ball c
    (fun i => (hcan _).mono hΩr) hR P hP
  obtain ⟨A, a', hA, ha', hsym, hconv⟩ := exists_diffOp_eq_tupleOp _ a ha
  refine ⟨δ, hδ, A, a', hA, fun α hα => (ha' α hα).analyticOn, fun x hx ξ hξ => ?_,
    fun F g x hx => ?_⟩
  · rw [hsym x ξ, hs x hx]
    exact pow_ne_zero _ (hell x (hΩδ hx) ξ hξ)
  · rw [hconv _ (h.contDiff_comp_coordEquiv F.2 g b), hop F g x hx]

theorem analyticAt_of_aeval_laplacian_eq_zero {ι : Type*} [Fintype ι]
    (bL : Module.Basis ι ℝ h.lieSubalgebra) (P : Polynomial ℂ) (hP : P.Monic)
    (f : h.smoothFuns (F := ℂ)) (hf : Polynomial.aeval (h.laplacian bL) P f = 0) (g : G) :
    AnalyticAt ℝ (fun Y : 𝔤 => (f : G → ℂ) (g * h.expG Y)) 0 := by
  set b := Module.finBasis ℝ 𝔤
  obtain ⟨δ, hδ, A, a, hA, ha, hell, hop⟩ := h.exists_elliptic_aeval_laplacian bL b P hP
  set u := fun y => (f : G → ℂ) (g * h.expG (coordEquiv b y))
  have hu : ContDiff ℝ ∞ u := h.contDiff_comp_coordEquiv f.2 g b
  have han : AnalyticOn ℝ u (Metric.ball 0 δ) :=
    analyticOn_of_elliptic Metric.isOpen_ball hA ha hell hu.contDiffOn fun x hx => by
      rw [hop f g x hx, hf]; rfl
  have hu0 : AnalyticAt ℝ u 0 :=
    (Metric.isOpen_ball.analyticOn_iff_analyticOnNhd.1 han) 0 (Metric.mem_ball_self hδ)
  have e : (fun Y : 𝔤 => (f : G → ℂ) (g * h.expG Y)) = u ∘ (coordEquiv b).symm := by
    funext Y; simp [u]
  rw [e]
  refine AnalyticAt.comp (by simpa using hu0) ?_
  exact (coordEquiv b).symm.toContinuousLinearMap.analyticAt _

theorem exists_eq_conv_of_aeval_laplacian_eq_zero [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] {ι : Type*} [Fintype ι]
    (bL : Module.Basis ι ℝ h.lieSubalgebra) (P : Polynomial ℂ) (hP : P.Monic) (hPd : 0 < P.natDegree)
    (f : h.smoothFuns (F := ℂ)) (hf : Polynomial.aeval (h.laplacian bL) P f = 0)
    {U : Set G} (hU : U ∈ 𝓝 (1 : G)) :
    ∃ α : G → ℂ, (letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ α) ∧ HasCompactSupport α ∧
      tsupport α ⊆ U ∧ ∀ g : G, (f : G → ℂ) g = ∫ y, (f : G → ℂ) (g * y⁻¹) * α y ∂μ := by
  let _ := h.chartedSpace
  set b := Module.finBasis ℝ 𝔤
  set d := Module.finrank ℝ 𝔤
  have hfc : Continuous (f : G → ℂ) := (show h.IsSmoothFun (f : G → ℂ) from f.2).continuous
  have hφc : ∀ g : G, Continuous fun y : G => (f : G → ℂ) (g * y⁻¹) := fun g =>
    hfc.comp (continuous_const.mul continuous_inv)
  have hexpc : Continuous fun x : EuclideanSpace ℝ (Fin d) => h.expG (coordEquiv b x) :=
    h.continuous_expG.comp (coordEquiv b).continuous
  obtain ⟨ε, hε, hdens⟩ := h.exists_smooth_density_expCoord μ b
  have hV : {x : EuclideanSpace ℝ (Fin d) | h.expG (coordEquiv b x) ∈ U} ∈ 𝓝 0 := by
    refine hexpc.continuousAt.preimage_mem_nhds ?_
    simpa using hU
  obtain ⟨ρ₀, hρ₀, hρ₀V⟩ := Metric.mem_nhds_iff.1 hV
  rcases Nat.eq_zero_or_pos d with hd | hd
  ·
    have hsub : ∀ x y : EuclideanSpace ℝ (Fin d), x = y := by
      intro x y; ext i; exact absurd i.2 (by omega)
    obtain ⟨κ, hκs, hκc, hκU, hκ⟩ := hdens (fun _ => 1) contDiff_const (fun x _ => by
      rw [hsub x 0]; exact Metric.mem_closedBall_self hε.le)
    refine ⟨κ, hκs, hκc, hκU.trans ?_, fun g => ?_⟩
    · rintro _ ⟨x, -, rfl⟩
      exact hρ₀V (by rw [hsub x 0]; exact Metric.mem_ball_self hρ₀)
    · have := hκ _ (hφc g)
      simp_rw [mul_comm ((f : G → ℂ) _)]
      rw [this, integral_euclideanSpace_of_eq_zero hd]
      simp
  ·
    set b' := b.map (LinearEquiv.neg ℝ)
    set Q := P ^ (d + 1)
    have hQ : Q.Monic := hP.pow _
    have hQd : Q.natDegree = (d + 1) * P.natDegree := hP.natDegree_pow _
    have hQf : Polynomial.aeval (h.laplacian bL) Q f = 0 := by
      rw [show Q = P ^ d * P from pow_succ P d, map_mul, Module.End.mul_apply, hf, map_zero]
    obtain ⟨δ, hδ, A, a, hA, ha, hell, hop⟩ := h.exists_elliptic_aeval_laplacian bL b' Q hQ
    set ρ := min (min δ ε) ρ₀
    have hρ : 0 < ρ := lt_min (lt_min hδ hε) hρ₀
    have hρδ : Metric.ball (0 : EuclideanSpace ℝ (Fin d)) ρ ⊆ Metric.ball 0 δ :=
      Metric.ball_subset_ball ((min_le_left _ _).trans (min_le_left _ _))
    have hρε : Metric.ball (0 : EuclideanSpace ℝ (Fin d)) ρ ⊆ Metric.closedBall 0 ε :=
      Metric.ball_subset_closedBall.trans
        (Metric.closedBall_subset_closedBall ((min_le_left _ _).trans (min_le_right _ _)))
    have hρV : Metric.ball (0 : EuclideanSpace ℝ (Fin d)) ρ ⊆ Metric.ball 0 ρ₀ :=
      Metric.ball_subset_ball (min_le_right _ _)
    have hm1 : 1 ≤ 2 * Q.natDegree := by rw [hQd]; nlinarith
    have hnm : d < 2 * (2 * Q.natDegree) := by rw [hQd]; nlinarith
    obtain ⟨E, β, -, -, hEs, -, hβs, -, hβU, hid⟩ := exists_parametrix hd hm1 hnm Metric.isOpen_ball
      hA (fun α hα => (ha α hα).contDiffOn Metric.isOpen_ball.uniqueDiffOn) hell Metric.isOpen_ball
      (Metric.mem_ball_self hρ) hρδ
    obtain ⟨κ, hκs, hκc, hκU, hκ⟩ := hdens β hβs (hβU.trans hρε)
    refine ⟨κ, hκs, hκc, hκU.trans ?_, fun g => ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact hρ₀V (hρV (hβU hx))
    · set ψ := fun y => (f : G → ℂ) (g * h.expG (coordEquiv b' y))
      have hψ : ContDiff ℝ ∞ ψ := h.contDiff_comp_coordEquiv f.2 g b'
      have h1 := hid ψ hψ.contDiffOn
      have h0 : ∫ x, E x * diffOp A a ψ x = 0 := by
        rw [← integral_zero (EuclideanSpace ℝ (Fin d)) ℂ]
        congr 1
        funext x
        by_cases hx : x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) δ
        · rw [hop f g x hx, hQf]; simp
        · rw [image_eq_zero_of_notMem_tsupport fun hE => hx (hρδ (hEs hE)), zero_mul]
      rw [h0, eq_comm, sub_eq_zero] at h1
      have hψ0 : ψ 0 = (f : G → ℂ) g := by simp [ψ]
      have hφ : ∀ x, (f : G → ℂ) (g * (h.expG (coordEquiv b x))⁻¹) = ψ x := by
        intro x; simp only [ψ, coordEquiv_map_neg, h.expG_neg, b']
      rw [← hψ0, h1]
      simp_rw [mul_comm ((f : G → ℂ) _)]
      rw [hκ _ (hφc g)]
      simp_rw [hφ]

end IsExpLieAlgebra

section Groups

open Matrix
open scoped Matrix.Norms.L2Operator

namespace IsExpLieAlgebra

theorem harishChandra_regularity_real {ι : Type*} [Fintype ι] [DecidableEq ι]
    {G : Subgroup (Matrix ι ι ℝ)ˣ} {𝔤 : Submodule ℝ (Matrix ι ι ℝ)} (h : IsExpLieAlgebra G 𝔤)
    (hstar : ∀ X ∈ 𝔤, Xᴴ ∈ 𝔤) [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
    {f : G → ℂ} (hf : h.IsSmoothFun f) (hK : IsRightKFinite (maxCompact G) f)
    (hZ : h.IsZFinite ⟨f, hf⟩) :
    (∀ g : G, AnalyticAt ℝ (fun Y : 𝔤 => f (g * h.expG Y)) 0) ∧
    ∀ U ∈ 𝓝 (1 : G), ∃ α : G → ℂ, (letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ α) ∧
      HasCompactSupport α ∧ tsupport α ⊆ U ∧ ∀ g : G, f g = ∫ y, f (g * y⁻¹) * α y ∂μ := by
  obtain ⟨d, b, ε, hε, horth, hKb⟩ := h.exists_cartanData_real hstar
  obtain ⟨P, hPm, hPd, hPf⟩ := h.exists_aeval_laplacian_eq_zero (maxCompact G)
    (traceForm h.lieSubalgebra) b ε hε horth (fun X Y => traceForm_symm X Y)
    (fun X Y Z => traceForm_lie X Y Z) hKb ⟨f, hf⟩ hK hZ
  exact ⟨fun g => h.analyticAt_of_aeval_laplacian_eq_zero b P hPm ⟨f, hf⟩ hPf g, fun U hU =>
    h.exists_eq_conv_of_aeval_laplacian_eq_zero μ b P hPm hPd ⟨f, hf⟩ hPf hU⟩

theorem harishChandra_regularity_complex {ι : Type*} [Fintype ι] [DecidableEq ι]
    {G : Subgroup (Matrix ι ι ℂ)ˣ} {𝔤 : Submodule ℝ (Matrix ι ι ℂ)} (h : IsExpLieAlgebra G 𝔤)
    (hstar : ∀ X ∈ 𝔤, Xᴴ ∈ 𝔤) [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
    {f : G → ℂ} (hf : h.IsSmoothFun f) (hK : IsRightKFinite (maxCompact G) f)
    (hZ : h.IsZFinite ⟨f, hf⟩) :
    (∀ g : G, AnalyticAt ℝ (fun Y : 𝔤 => f (g * h.expG Y)) 0) ∧
    ∀ U ∈ 𝓝 (1 : G), ∃ α : G → ℂ, (letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ α) ∧
      HasCompactSupport α ∧ tsupport α ⊆ U ∧ ∀ g : G, f g = ∫ y, f (g * y⁻¹) * α y ∂μ := by
  obtain ⟨d, b, ε, hε, horth, hKb⟩ := h.exists_cartanData_complex hstar
  obtain ⟨P, hPm, hPd, hPf⟩ := h.exists_aeval_laplacian_eq_zero (maxCompact G)
    (traceForm h.lieSubalgebra) b ε hε horth (fun X Y => traceForm_symm X Y)
    (fun X Y Z => traceForm_lie X Y Z) hKb ⟨f, hf⟩ hK hZ
  exact ⟨fun g => h.analyticAt_of_aeval_laplacian_eq_zero b P hPm ⟨f, hf⟩ hPf g, fun U hU =>
    h.exists_eq_conv_of_aeval_laplacian_eq_zero μ b P hPm hPd ⟨f, hf⟩ hPf hU⟩

end IsExpLieAlgebra

theorem harishChandra_regularity_GL_real (n : ℕ)
    [MeasurableSpace (⊤ : Subgroup (GL (Fin n) ℝ))] [BorelSpace (⊤ : Subgroup (GL (Fin n) ℝ))]
    (μ : Measure (⊤ : Subgroup (GL (Fin n) ℝ))) [μ.IsHaarMeasure]
    {f : (⊤ : Subgroup (GL (Fin n) ℝ)) → ℂ}
    (hf : (isExpLieAlgebra_top (𝔸 := Matrix (Fin n) (Fin n) ℝ)).IsSmoothFun f)
    (hK : IsExpLieAlgebra.IsRightKFinite (maxCompact ⊤) f)
    (hZ : (isExpLieAlgebra_top (𝔸 := Matrix (Fin n) (Fin n) ℝ)).IsZFinite ⟨f, hf⟩) :
    (∀ g, AnalyticAt ℝ
      (fun Y => f (g * (isExpLieAlgebra_top (𝔸 := Matrix (Fin n) (Fin n) ℝ)).expG Y)) 0) ∧
    ∀ U ∈ 𝓝 (1 : (⊤ : Subgroup (GL (Fin n) ℝ))), ∃ α : (⊤ : Subgroup (GL (Fin n) ℝ)) → ℂ,
      (letI := (isExpLieAlgebra_top (𝔸 := Matrix (Fin n) (Fin n) ℝ)).chartedSpace;
        ContMDiff 𝓘(ℝ, (⊤ : Submodule ℝ (Matrix (Fin n) (Fin n) ℝ))) 𝓘(ℝ, ℂ) ∞ α) ∧
      HasCompactSupport α ∧ tsupport α ⊆ U ∧ ∀ g, f g = ∫ y, f (g * y⁻¹) * α y ∂μ :=
  (isExpLieAlgebra_top (𝔸 := Matrix (Fin n) (Fin n) ℝ)).harishChandra_regularity_real
    (fun _ _ => Submodule.mem_top) μ hf hK hZ

theorem harishChandra_regularity_GL_complex (n : ℕ)
    [MeasurableSpace (⊤ : Subgroup (GL (Fin n) ℂ))] [BorelSpace (⊤ : Subgroup (GL (Fin n) ℂ))]
    (μ : Measure (⊤ : Subgroup (GL (Fin n) ℂ))) [μ.IsHaarMeasure]
    {f : (⊤ : Subgroup (GL (Fin n) ℂ)) → ℂ}
    (hf : (isExpLieAlgebra_top (𝔸 := Matrix (Fin n) (Fin n) ℂ)).IsSmoothFun f)
    (hK : IsExpLieAlgebra.IsRightKFinite (maxCompact ⊤) f)
    (hZ : (isExpLieAlgebra_top (𝔸 := Matrix (Fin n) (Fin n) ℂ)).IsZFinite ⟨f, hf⟩) :
    (∀ g, AnalyticAt ℝ
      (fun Y => f (g * (isExpLieAlgebra_top (𝔸 := Matrix (Fin n) (Fin n) ℂ)).expG Y)) 0) ∧
    ∀ U ∈ 𝓝 (1 : (⊤ : Subgroup (GL (Fin n) ℂ))), ∃ α : (⊤ : Subgroup (GL (Fin n) ℂ)) → ℂ,
      (letI := (isExpLieAlgebra_top (𝔸 := Matrix (Fin n) (Fin n) ℂ)).chartedSpace;
        ContMDiff 𝓘(ℝ, (⊤ : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ))) 𝓘(ℝ, ℂ) ∞ α) ∧
      HasCompactSupport α ∧ tsupport α ⊆ U ∧ ∀ g, f g = ∫ y, f (g * y⁻¹) * α y ∂μ :=
  (isExpLieAlgebra_top (𝔸 := Matrix (Fin n) (Fin n) ℂ)).harishChandra_regularity_complex
    (fun _ _ => Submodule.mem_top) μ hf hK hZ

theorem harishChandra_regularity_indefiniteUnitary (p q : ℕ)
    [MeasurableSpace (indefiniteUnitaryGroup p q)] [BorelSpace (indefiniteUnitaryGroup p q)]
    (μ : Measure (indefiniteUnitaryGroup p q)) [μ.IsHaarMeasure]
    {f : indefiniteUnitaryGroup p q → ℂ}
    (hf : (isExpLieAlgebra_indefiniteUnitary p q).IsSmoothFun f)
    (hK : IsExpLieAlgebra.IsRightKFinite (maxCompact (indefiniteUnitaryGroup p q)) f)
    (hZ : (isExpLieAlgebra_indefiniteUnitary p q).IsZFinite ⟨f, hf⟩) :
    (∀ g, AnalyticAt ℝ (fun Y => f (g * (isExpLieAlgebra_indefiniteUnitary p q).expG Y)) 0) ∧
    ∀ U ∈ 𝓝 (1 : indefiniteUnitaryGroup p q), ∃ α : indefiniteUnitaryGroup p q → ℂ,
      (letI := (isExpLieAlgebra_indefiniteUnitary p q).chartedSpace;
        ContMDiff 𝓘(ℝ, indefiniteUnitaryLieAlgebra p q) 𝓘(ℝ, ℂ) ∞ α) ∧
      HasCompactSupport α ∧ tsupport α ⊆ U ∧ ∀ g, f g = ∫ y, f (g * y⁻¹) * α y ∂μ :=
  (isExpLieAlgebra_indefiniteUnitary p q).harishChandra_regularity_complex
    (fun _ hX => conjTranspose_mem_indefiniteUnitaryLieAlgebra hX) μ hf hK hZ

end Groups

end GroundTheory.Automorphic
