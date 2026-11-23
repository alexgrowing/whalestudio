import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.HasFDerivAtInt
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.Imports
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.ScalarDir

noncomputable section

open MeasureTheory Filter Topology Set Metric Matrix
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.LVs

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs.HolB PositivityTheory.Rg.Sw.LVs.HolC

variable {n : ℕ}

theorem two_le_infty : ((2 : ℕ) : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top

theorem det_ne_zero_of_inG {y : M2 n} (hy : InG y) : y.det ≠ 0 := by
  intro h
  have hJ : (JJ n).det ≠ 0 := by
    intro hJ
    have := congrArg Matrix.det (JJ_sq (n := n))
    rw [det_mul, hJ, mul_zero, det_neg, det_one] at this
    simp at this
  have := congrArg Matrix.det hy
  rw [det_mul, det_mul, h, mul_zero] at this
  exact hJ this.symm

theorem fderiv_eq_zero_of_vanish {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    {Ω : Set (M2 n)} (hΩ : IsOpen Ω) (hG : GSet n ⊆ Ω) {H : M2 n → V} (hH : ContDiffOn ℂ ∞ H Ω)
    (h0 : ∀ g, InG g → H g = 0) {y : M2 n} (hy : InG y) : fderiv ℂ H y = 0 := by
  have hdiff : ∀ g, InG g → DifferentiableAt ℂ H g := fun g hg =>
    (hH.contDiffAt (hΩ.mem_nhds (hG hg))).differentiableAt (by simp)
  have hlow : ∀ g, InG g → ∀ c : Matrix (Fin n) (Fin n) ℂ, cᴴ = c →
      fderiv ℂ H g (g * fromBlocks 0 0 c 0) = 0 := by
    intro g hg c hc
    refine fderiv_line (hdiff g hg) (fun t => ?_)
    rw [lower_line, h0 _ (inG_mul hg (inG_lower (herm_real_smul hc t))), h0 g hg]
  have hup : ∀ g, InG g → ∀ b : Matrix (Fin n) (Fin n) ℂ, bᴴ = b →
      fderiv ℂ H g (g * fromBlocks 0 b 0 0) = 0 := by
    intro g hg b hb
    refine fderiv_line (hdiff g hg) (fun t => ?_)
    rw [upper_line, h0 _ (inG_mul hg (inG_upper (herm_real_smul hb t))), h0 g hg]
  have hone : fderiv ℂ H y (y * 1) = 0 := by
    rw [mul_one]
    refine HolD.scalar_dir (hdiff y hy) (fun t => h0 _ ?_)
    have e : Complex.exp (↑t * Complex.I) • y = y * (Complex.exp (↑t * Complex.I) • (1 : M2 n)) := by
      rw [mul_smul_comm, mul_one]
    rw [e]
    refine inG_mul hy (inG_scalar ?_)
    rw [Complex.star_def, Complex.conj_mul', Complex.norm_exp_ofReal_mul_I]
    simp
  have hCy : ContDiffAt ℂ ∞ H y := hH.contDiffAt (hΩ.mem_nhds (hG hy))
  have hsymm : IsSymmSndFDerivAt ℂ H y :=
    hCy.isSymmSndFDerivAt (by simpa [minSmoothness_of_isRCLikeNormedField] using two_le_infty)
  have hD : DifferentiableAt ℂ (fderiv ℂ H) y :=
    (hCy.fderiv_right (m := 1) (by simpa [one_add_one_eq_two] using two_le_infty)).differentiableAt one_ne_zero
  have hcomm : ∀ b c : Matrix (Fin n) (Fin n) ℂ, bᴴ = b → cᴴ = c →
      fderiv ℂ H y (y * fromBlocks (-(b * c)) 0 0 (c * b)) = 0 := by
    intro b c hb hc
    set U : M2 n := fromBlocks 0 b 0 0 with hU
    set L : M2 n := fromBlocks 0 0 c 0 with hL
    let mL : M2 n →L[ℂ] M2 n := LinearMap.toContinuousLinearMap (LinearMap.mulRight ℂ L)
    let mU : M2 n →L[ℂ] M2 n := LinearMap.toContinuousLinearMap (LinearMap.mulRight ℂ U)
    have e1 := HolD.line2 (H := H) (y := y) (w := y * U) (m := mL) hD (fun t => by
      have hg := inG_mul hy (inG_upper (herm_real_smul hb t))
      show fderiv ℂ H _ ((y + (t : ℂ) • (y * U)) * L) = 0
      rw [upper_line]
      exact hlow _ hg c hc)
    have e2 := HolD.line2 (H := H) (y := y) (w := y * L) (m := mU) hD (fun t => by
      have hg := inG_mul hy (inG_lower (herm_real_smul hc t))
      show fderiv ℂ H _ ((y + (t : ℂ) • (y * L)) * U) = 0
      rw [lower_line]
      exact hup _ hg b hb)
    change fderiv ℂ (fderiv ℂ H) y (y * U) (y * L) + fderiv ℂ H y (y * U * L) = 0 at e1
    change fderiv ℂ (fderiv ℂ H) y (y * L) (y * U) + fderiv ℂ H y (y * L * U) = 0 at e2
    have key : fromBlocks (-(b * c)) 0 0 (c * b) = L * U - U * L := by
      simp only [hU, hL, Matrix.fromBlocks_multiply]
      rw [sub_eq_add_neg, Matrix.fromBlocks_neg, Matrix.fromBlocks_add]
      simp
    rw [key, mul_sub, ← mul_assoc, ← mul_assoc, map_sub]
    have a1 := eq_neg_of_add_eq_zero_right e1
    have a2 := eq_neg_of_add_eq_zero_right e2
    have hs : fderiv ℂ (fderiv ℂ H) y (y * L) (y * U) = fderiv ℂ (fderiv ℂ H) y (y * U) (y * L) :=
      hsymm _ _
    rw [sub_eq_zero]
    exact a2.trans ((congrArg Neg.neg hs).trans a1.symm)
  let W : Submodule ℂ (M2 n) :=
    LinearMap.ker ((fderiv ℂ H y : M2 n →ₗ[ℂ] V) ∘ₗ LinearMap.mulLeft ℂ y)
  have hW : W = ⊤ :=
    span_top W (fun b hb => LinearMap.mem_ker.mpr (hup y hy b hb))
      (fun c hc => LinearMap.mem_ker.mpr (hlow y hy c hc))
      (fun b c hb hc => LinearMap.mem_ker.mpr (hcomm b c hb hc))
      (LinearMap.mem_ker.mpr hone)
  have hdet : IsUnit y.det := isUnit_iff_ne_zero.mpr (det_ne_zero_of_inG hy)
  ext u
  have hu : y⁻¹ * u ∈ W := hW ▸ Submodule.mem_top
  have e := LinearMap.mem_ker.mp hu
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.mulLeft_apply,
    ContinuousLinearMap.coe_coe, Matrix.mul_nonsing_inv_cancel_left _ _ hdet] at e
  simpa using e

theorem nat_lt_infty (N : ℕ) : ((N : ℕ) : WithTop ℕ∞) < ∞ := WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top N)

private theorem iteratedFDeriv_eq_zero_of_eq_zero_on_inG {n : ℕ} {Ω : Set (M2 n)} (hΩ : IsOpen Ω) (hG : GSet n ⊆ Ω) (N : ℕ) :
    ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] (H : M2 n → V),
      ContDiffOn ℂ ∞ H Ω → (∀ g, InG g → H g = 0) → ∀ g, InG g → iteratedFDeriv ℂ N H g = 0 := by
  induction N with
  | zero =>
    intro V _ _ _ H _ h0 g hg
    ext v
    simp [h0 g hg]
  | succ N ih =>
    intro V _ _ _ H hH h0 g hg
    have hH' := (contDiffOn_infty_iff_fderiv_of_isOpen hΩ).mp hH
    letI : NormedAddCommGroup (M2 n →L[ℂ] V) := ContinuousLinearMap.toNormedAddCommGroup
    letI : NormedSpace ℂ (M2 n →L[ℂ] V) := ContinuousLinearMap.toNormedSpace
    haveI : SequentialSpace (M2 n) :=
      inferInstanceAs (SequentialSpace ((Fin n ⊕ Fin n) → (Fin n ⊕ Fin n) → ℂ))
    haveI : @CompleteSpace (M2 n →L[ℂ] V) PseudoMetricSpace.toUniformSpace :=
      ContinuousLinearMap.instCompleteSpace
    have e : iteratedFDeriv ℂ N (fun y => fderiv ℂ H y) g = 0 :=
      ih (fun y => fderiv ℂ H y) hH'.2 (fun g' hg' => fderiv_eq_zero_of_vanish hΩ hG hH h0 hg') g hg
    rw [iteratedFDeriv_succ_eq_comp_right, Function.comp_apply]
    have e' := congrArg (continuousMultilinearCurryRightEquiv' ℂ N (M2 n) V).symm e
    exact e'.trans (map_zero _)

theorem holZero : HolZero := by
  intro n Ω F hΩ hG hF h0 N g hg
  exact iteratedFDeriv_eq_zero_of_eq_zero_on_inG hΩ hG N F hF (fun g hg => h0 g hg) g hg

private theorem contDiffOn_integral_and_iteratedFDeriv_integral {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {Kg : Type} [TopologicalSpace Kg] [CompactSpace Kg] [MeasurableSpace Kg] [BorelSpace Kg]
    (μ : Measure Kg) [IsFiniteMeasure μ] {Ω : Set E} (F : Kg → E → ℂ) (hΩ : IsOpen Ω)
    (hcont : ∀ N : ℕ, ContinuousOn (fun y : Kg × E => iteratedFDeriv ℂ N (F y.1) y.2) (univ ×ˢ Ω))
    (hF : ∀ k, ContDiffOn ℂ ∞ (F k) Ω) :
    ContDiffOn ℂ ∞ (fun x => ∫ k, F k x ∂μ) Ω ∧ ∀ (N : ℕ) (x : E) (v : Fin N → E), x ∈ Ω →
      iteratedFDeriv ℂ N (fun x => ∫ k, F k x ∂μ) x v = ∫ k, iteratedFDeriv ℂ N (F k) x v ∂μ := by
  have hFd : ∀ k, ∀ x ∈ Ω, ContDiffAt ℂ ∞ (F k) x := fun k x hx =>
    (hF k).contDiffAt (hΩ.mem_nhds hx)
  have hA : ∀ N : ℕ, ∀ x ∈ Ω, HasFDerivAt (fun x => ∫ k, iteratedFDeriv ℂ N (F k) x ∂μ)
      (∫ k, fderiv ℂ (iteratedFDeriv ℂ N (F k)) x ∂μ) x := by
    intro N x hx
    refine HolA.hasFDerivAt_int hΩ (hcont N) ?_ ?_ hx
    · have e : (fun y : Kg × E => fderiv ℂ (iteratedFDeriv ℂ N (F y.1)) y.2) =
          fun y => continuousMultilinearCurryLeftEquiv ℂ (fun _ : Fin (N + 1) => E) ℂ
            (iteratedFDeriv ℂ (N + 1) (F y.1) y.2) := by
        funext y
        rw [fderiv_iteratedFDeriv]
        rfl
      rw [e]
      exact (continuousMultilinearCurryLeftEquiv ℂ (fun _ : Fin (N + 1) => E) ℂ).continuous.comp_continuousOn
        (hcont (N + 1))
    · intro k x hx
      exact ((hFd k x hx).differentiableAt_iteratedFDeriv (by simpa using nat_lt_infty N)).hasFDerivAt
  have hB : ∀ N : ℕ, ∀ x ∈ Ω, iteratedFDeriv ℂ N (fun x => ∫ k, F k x ∂μ) x =
      ∫ k, iteratedFDeriv ℂ N (F k) x ∂μ := by
    intro N
    induction N with
    | zero =>
      intro x _
      simp only [iteratedFDeriv_zero_eq_comp, Function.comp_apply]
      exact ((continuousMultilinearCurryFin0 ℂ E ℂ).symm.toContinuousLinearEquiv.integral_comp_comm _).symm
    | succ N ih =>
      intro x hx
      have hev : iteratedFDeriv ℂ N (fun x => ∫ k, F k x ∂μ) =ᶠ[𝓝 x]
          fun x => ∫ k, iteratedFDeriv ℂ N (F k) x ∂μ :=
        Filter.eventually_of_mem (hΩ.mem_nhds hx) ih
      rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, hev.fderiv_eq, (hA N x hx).fderiv]
      exact ((continuousMultilinearCurryLeftEquiv ℂ (fun _ : Fin (N + 1) => E) ℂ).symm.toContinuousLinearEquiv.integral_comp_comm
        (fun k => fderiv ℂ (iteratedFDeriv ℂ N (F k)) x)).symm
  have hD : ∀ m : ℕ, DifferentiableOn ℂ (fun x => iteratedFDerivWithin ℂ m (fun x => ∫ k, F k x ∂μ) Ω x) Ω :=
    fun m x hx => ((hA m x hx).differentiableAt.differentiableWithinAt).congr
      (fun y hy => (iteratedFDerivWithin_of_isOpen m hΩ hy).trans (hB m y hy))
      ((iteratedFDerivWithin_of_isOpen m hΩ hx).trans (hB m x hx))
  refine ⟨contDiffOn_of_continuousOn_differentiableOn (n := ⊤) (fun m _ => (hD m).continuousOn)
    (fun m _ => hD m), ?_⟩
  intro N x v hx
  rw [hB N x hx]
  have hint : Integrable (fun k => iteratedFDeriv ℂ N (F k) x) μ :=
    HolA.integrable_of_cont ((hcont N).comp_continuous (continuous_id.prodMk continuous_const)
      (fun k => ⟨mem_univ _, hx⟩))
  exact ((ContinuousMultilinearMap.apply ℂ (fun _ : Fin N => E) ℂ v).integral_comp_comm hint).symm

theorem holInt : HolInt := by
  intro n Kg _ _ _ _ μ _ Ω F hΩ hcont hF
  exact contDiffOn_integral_and_iteratedFDeriv_integral μ F hΩ hcont hF

end PositivityTheory.Rg.Sw.LVs
