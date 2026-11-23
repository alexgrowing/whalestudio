import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StParamPieceInt
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSheetSumMeasurable
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.OsgoodSeparate
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.LintegralImageEqLintegralNormSqDetMul
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

namespace ParamPieceInt

theorem analyticAt_of_differentiableOn {d m : ℕ} {U : Set (Fin d → ℂ)} {f : (Fin d → ℂ) → Fin m → ℂ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) {x : Fin d → ℂ} (hx : x ∈ U) : AnalyticAt ℂ f x := by
  refine AnalyticAt.pi fun i => ?_
  refine IndefiniteRowSideFullHecke.ComplexSets.analyticOnNhd_of_continuousOn_of_separately hU
    ((continuous_apply i).comp_continuousOn hf.continuousOn) (fun z hz j => ?_) x hx
  have hfz : DifferentiableAt ℂ (fun w => f w i) z :=
    differentiableAt_pi.mp (hf.differentiableAt (hU.mem_nhds hz)) i
  have hu : DifferentiableAt ℂ (Function.update z j) (z j) :=
    (hasFDerivAt_update z (z j)).differentiableAt
  have hfz' : DifferentiableAt ℂ (fun w => f w i) (Function.update z j (z j)) := by
    rwa [Function.update_eq_self]
  exact hfz'.comp (z j) hu

variable {n d : ℕ}

theorem differentiable_mulVec (A : Matrix (Fin d) (Fin n) ℂ) :
    Differentiable ℂ (fun x : Fin n → ℂ => A *ᵥ x) := by
  have h := (Matrix.mulVecLin A).toContinuousLinearMap.differentiable
  convert h using 1
  funext x
  simp

theorem exists_sheet {W : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    {σ : (Fin d → ℂ) → Fin n → ℂ} {r r' : ℝ} {N : Set (Fin n → ℂ)}
    (hσ : DifferentiableOn ℂ σ (Metric.ball 0 r)) (hinj : Set.InjOn σ (Metric.ball 0 r))
    (hN : IsOpen N) (hrr : r' < r)
    (hprop : ∀ w ∈ Metric.ball (0 : Fin d → ℂ) r, σ w ∈ N → σ w ∈ zeroSet W ∧ ‖w‖ ≤ r')
    (hcov : zeroSet W ∩ N ⊆ σ '' Metric.ball 0 r)
    {w : Fin d → ℂ} (hw : w ∈ Metric.ball 0 r) (hwN : σ w ∈ N)
    (hdet : LinearMap.det (fderiv ℂ (fun v => A *ᵥ σ v) w : (Fin d → ℂ) →ₗ[ℂ] Fin d → ℂ) ≠ 0) :
    ∃ s : (Fin d → ℂ) → Fin n → ℂ, IsSheetAt W A (σ w) s ∧
      ∀ᶠ v in 𝓝 w, s (A *ᵥ σ v) = σ v := by
  classical
  set g : (Fin d → ℂ) → Fin d → ℂ := fun v => A *ᵥ σ v with hg
  set Ω : Set (Fin d → ℂ) := Metric.ball 0 r ∩ σ ⁻¹' N with hΩ
  have hΩo : IsOpen Ω := hσ.continuousOn.isOpen_inter_preimage Metric.isOpen_ball hN
  have hgd : DifferentiableOn ℂ g (Metric.ball 0 r) :=
    (differentiable_mulVec A).comp_differentiableOn hσ
  have hgan : ∀ v ∈ Metric.ball (0 : Fin d → ℂ) r, AnalyticAt ℂ g v := fun v hv =>
    analyticAt_of_differentiableOn Metric.isOpen_ball hgd hv

  have hstrict : HasStrictFDerivAt g
      (((fderiv ℂ g w).toContinuousLinearEquivOfDetNeZero hdet : (Fin d → ℂ) ≃L[ℂ] Fin d → ℂ) :
        (Fin d → ℂ) →L[ℂ] Fin d → ℂ) w := by
    have he : (((fderiv ℂ g w).toContinuousLinearEquivOfDetNeZero hdet : (Fin d → ℂ) ≃L[ℂ] Fin d → ℂ) :
        (Fin d → ℂ) →L[ℂ] Fin d → ℂ) = fderiv ℂ g w := by
      ext1 v
      simp
    rw [he]
    exact (hgan w hw).hasStrictFDerivAt
  obtain ⟨e, heg, hwe⟩ : ∃ e : OpenPartialHomeomorph (Fin d → ℂ) (Fin d → ℂ),
      (e : (Fin d → ℂ) → Fin d → ℂ) = g ∧ w ∈ e.source :=
    ⟨hstrict.toOpenPartialHomeomorph g, hstrict.toOpenPartialHomeomorph_coe,
      hstrict.mem_toOpenPartialHomeomorph_source⟩

  have hdetc : ContinuousAt (fun v => (fderiv ℂ g v).det) w :=
    ContinuousLinearMap.continuous_det.continuousAt.comp (hgan w hw).fderiv.continuousAt
  have h1 : ∀ᶠ v in 𝓝 w, v ∈ Ω := hΩo.mem_nhds ⟨hw, hwN⟩
  have h2 : ∀ᶠ v in 𝓝 w, v ∈ e.source := e.open_source.mem_nhds hwe
  have hev : ∀ᶠ v in 𝓝 w, (v ∈ Ω ∧ v ∈ e.source) ∧ (fderiv ℂ g v).det ≠ 0 :=
    (h1.and h2).and (hdetc.eventually_ne hdet)
  obtain ⟨O, hOp, hOo, hwO⟩ := eventually_nhds_iff.1 hev
  have hsymm : ∀ v ∈ O, e.symm (g v) = v := fun v hv => by
    rw [← heg]; exact e.left_inv (hOp v hv).1.2
  set U : Set (Fin d → ℂ) := e.target ∩ e.symm ⁻¹' O with hU
  have hUo : IsOpen U := e.isOpen_inter_preimage_symm hOo
  have hgU : ∀ v ∈ O, g v ∈ U := fun v hv =>
    ⟨by rw [← heg]; exact e.map_source (hOp v hv).1.2, by
      show e.symm (g v) ∈ O; rw [hsymm v hv]; exact hv⟩
  have hright : ∀ y ∈ U, g (e.symm y) = y := fun y hy => by
    rw [← heg]; exact e.right_inv hy.1
  have hsymmd : ∀ y ∈ U, DifferentiableAt ℂ e.symm y := by
    intro y hy
    have hv : e.symm y ∈ O := hy.2
    have hd := (hOp _ hv).2
    have hf : HasFDerivAt (e : (Fin d → ℂ) → Fin d → ℂ)
        (((fderiv ℂ g (e.symm y)).toContinuousLinearEquivOfDetNeZero hd :
          (Fin d → ℂ) ≃L[ℂ] Fin d → ℂ) : (Fin d → ℂ) →L[ℂ] Fin d → ℂ) (e.symm y) := by
      have he : (((fderiv ℂ g (e.symm y)).toContinuousLinearEquivOfDetNeZero hd :
          (Fin d → ℂ) ≃L[ℂ] Fin d → ℂ) : (Fin d → ℂ) →L[ℂ] Fin d → ℂ) = fderiv ℂ g (e.symm y) := by
        ext1 v
        simp
      rw [he, heg]
      exact (hgan _ (hOp _ hv).1.1.1).differentiableAt.hasFDerivAt
    exact (e.hasFDerivAt_symm hy.1 hf).differentiableAt
  refine ⟨σ ∘ e.symm, ⟨U, hUo, hgU w hwO, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro y hy
    have hv : e.symm y ∈ O := hy.2
    exact ((hσ.differentiableAt (Metric.isOpen_ball.mem_nhds (hOp _ hv).1.1.1)).comp y
      (hsymmd y hy)).differentiableWithinAt
  · show σ (e.symm (g w)) = σ w
    rw [hsymm w hwO]
  · intro y hy
    have hv : e.symm y ∈ O := hy.2
    refine ⟨hright y hy, ?_⟩
    exact (hprop _ (hOp _ hv).1.1.1 (hOp _ hv).1.1.2).1
  ·
    set K : Set (Fin d → ℂ) := Metric.closedBall 0 r' \ O with hK
    have hKb : K ⊆ Metric.ball 0 r := fun v hv => Metric.closedBall_subset_ball hrr hv.1
    have hKc : IsCompact (σ '' K) :=
      ((isCompact_closedBall 0 r').diff hOo).image_of_continuousOn (hσ.continuousOn.mono hKb)
    have hwK : σ w ∉ σ '' K := by
      rintro ⟨k, hk, hkw⟩
      exact hk.2 (hinj (hKb hk) hw hkw ▸ hwO)
    refine ⟨N ∩ (σ '' K)ᶜ, (hN.inter hKc.isClosed.isOpen_compl).mem_nhds ⟨hwN, hwK⟩, ?_⟩
    rintro x' ⟨hx'Z, hx'N, hx'K⟩ -
    obtain ⟨v, hvb, rfl⟩ := hcov ⟨hx'Z, hx'N⟩
    have hvr : ‖v‖ ≤ r' := (hprop v hvb hx'N).2
    have hvO : v ∈ O := by
      by_contra hvO
      exact hx'K ⟨v, ⟨mem_closedBall_zero_iff.2 hvr, hvO⟩, rfl⟩
    show σ v = σ (e.symm (g v))
    rw [hsymm v hvO]
  · filter_upwards [hOo.mem_nhds hwO] with v hv
    show σ (e.symm (g v)) = σ v
    rw [hsymm v hv]

end ParamPieceInt

open ParamPieceInt in

theorem ParamPieceInt.proof : ParamPieceInt.Statement := by
  intro n d W A σ r r' N hσ hinj hN hrr hprop hcov f φ P hφ hPm hPb hPw hgP
  classical
  set g : (Fin d → ℂ) → Fin d → ℂ := fun v => A *ᵥ σ v with hg
  have hgd : DifferentiableOn ℂ g (Metric.ball 0 r) :=
    (differentiable_mulVec A).comp_differentiableOn hσ
  have hgan : ∀ v ∈ Metric.ball (0 : Fin d → ℂ) r, AnalyticAt ℂ g v := fun v hv =>
    analyticAt_of_differentiableOn Metric.isOpen_ball hgd hv

  have hdens : ∀ w ∈ P, Complex.normSq (ReciprocityTheory.AnForm.A.jacC g w).det *
      chartDens W A ((σ '' P).indicator f) φ (g w) =
        f (σ w) * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ σ) w := by
    intro w hw
    obtain ⟨s, hs, hsg⟩ := exists_sheet hσ hinj hN hrr hprop hcov (hPb hw) (hPw w hw).1 (hPw w hw).2
    have hex : ∃ s, IsSheetAt W A (σ w) s := ⟨s, hs⟩
    have hfib : σ w ∈ fibre W A (g w) := ⟨(hprop w (hPb hw) (hPw w hw).1).1, rfl⟩
    have hsum : chartDens W A ((σ '' P).indicator f) φ (g w) =
        f (σ w) * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ s) (g w) := by
      unfold chartDens sheetSum
      rw [finsum_eq_single _ (σ w), finsum_eq_if, if_pos hfib, dif_pos hex]
      · beta_reduce
        rw [Set.indicator_of_mem (Set.mem_image_of_mem σ hw), IndefiniteRowSideFullHecke.ComplexSets.maDens_congr_of_eventuallyEq fun k =>
          (SheetSumMeasurable.sheet_eventuallyEq hs hex.choose_spec).fun_comp (φ k)]
      · intro x hxne
        rw [finsum_eq_if]
        split_ifs with hx h
        · beta_reduce
          rw [Set.indicator_of_notMem, zero_mul]
          rintro ⟨w', hw', rfl⟩
          exact hxne (by rw [hgP hw' hw hx.2])
        · rfl
        · rfl

    obtain ⟨U, hUo, hwU, hsd, hsx, -, -⟩ := hs
    have hsc : ContDiffAt ℝ 2 s (g w) :=
      (analyticAt_of_differentiableOn hUo hsd hwU).contDiffAt.restrict_scalars ℝ
    have hφs : ∀ k, ContDiffAt ℝ 2 (φ k ∘ s) (g w) := by
      intro k
      obtain ⟨Uk, hUko, hZU, hcd⟩ := hφ k
      have hmem : s (g w) ∈ Uk := by
        show s (A *ᵥ σ w) ∈ Uk
        rw [hsx]; exact hZU (hprop w (hPb hw) (hPw w hw).1).1
      exact ((hcd.contDiffAt (hUko.mem_nhds hmem)).of_le
        (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤))).comp (g w) hsc
    have hcomp : ReciprocityTheory.AnForm.maDens (fun k => (φ k ∘ s) ∘ g) w =
        ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ s) (g w) * Complex.normSq (ReciprocityTheory.AnForm.A.jacC g w).det :=
      ReciprocityTheory.AnForm.A.maDens_comp (fun k => φ k ∘ s) g w (hgan w (hPb hw)) hφs
    have hev : ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ σ) w =
        ReciprocityTheory.AnForm.maDens (fun k => (φ k ∘ s) ∘ g) w :=
      IndefiniteRowSideFullHecke.ComplexSets.maDens_congr_of_eventuallyEq fun k => by
        filter_upwards [hsg] with v hv
        simp only [Function.comp_apply, g]
        rw [hv]
    rw [hsum, hev, hcomp]
    ring

  have hzero : ∀ y, y ∉ g '' P → chartDens W A ((σ '' P).indicator f) φ y = 0 := by
    intro y hy
    unfold chartDens sheetSum
    refine finsum_mem_eq_zero_of_forall_eq_zero fun x hx => ?_
    split_ifs with h
    · beta_reduce
      rw [Set.indicator_of_notMem, zero_mul]
      rintro ⟨w, hw, rfl⟩
      exact hy ⟨w, hw, hx.2⟩
    · rfl
  have hgdP : ∀ w ∈ P, DifferentiableAt ℂ g w := fun w hw => (hgan w (hPb hw)).differentiableAt
  unfold chartInt
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero,
    integral_image_eq_integral_abs_det_fderiv_smul volume hPm
      (fun x hx => ((hgdP x hx).restrictScalars ℝ).hasFDerivAt.hasFDerivWithinAt) hgP]
  refine setIntegral_congr_fun hPm fun w hw => ?_
  rw [ReciprocityTheory.AnForm.A.det_fderiv_real_eq_normSq g w (hgdP w hw),
    abs_of_nonneg (Complex.normSq_nonneg _), smul_eq_mul, hdens w hw]

end

end GroundTheory.Heights₂.Heights
