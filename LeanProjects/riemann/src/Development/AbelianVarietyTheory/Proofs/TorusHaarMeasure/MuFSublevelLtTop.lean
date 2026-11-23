import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspidalExponentialDecay
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.OneLeMinorOfIsOrth
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.IsUpqSubmatrix
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MuFLtTopOfIsCompact

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.SublevelFin

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem isClosed_isOrth {r : ℕ} (X : Data E r) : IsClosed {x : Frame X.Ψ r | IsOrth X x} := by
  have e : {x : Frame X.Ψ r | IsOrth X x} = ⋂ τ : X.Ψ, {x | gram τ.1 X.Gm (mat x τ) =
      Matrix.diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)} := by
    ext x; simp [IsOrth]
  rw [e]
  refine isClosed_iInter fun τ => isClosed_eq ?_ continuous_const
  have hm : Continuous fun x : Frame X.Ψ r => mat x τ := continuous_apply τ
  simp only [FrameDegreeData.gram_eq]
  exact (hm.matrix_transpose.matrix_mul continuous_const).matrix_mul
    (hm.matrix_map Complex.continuous_conj)

theorem entry_sq_le {r : ℕ} (X : Data E r) {x0 x : Frame X.Ψ r} (h0 : IsOrth X x0)
    (hx : IsOrth X x) (τ : X.Ψ) (i j : Fin r) :
    ‖((mat x0 τ)⁻¹ * mat x τ) i j‖ ^ 2 ≤ ((r : ℝ) + 1) *
      ‖lminor ((mat x0 τ)⁻¹ * mat x τ) ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩‖ ^ 2 := by
  have h := sumBd_entry_bound (FrameSumBound.isUpq_frame X h0 hx τ)
    ((FrameSumBound.swapIdx X.p0_le).symm i) ((FrameSumBound.swapIdx X.p0_le).symm j)
  have hm : ∀ M : Matrix (Fin r) (Fin r) ℂ,
      lminor M (⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ : Fin (r + 1)) =
        (M.submatrix (FrameSumBound.swapIdx X.p0_le)
          (FrameSumBound.swapIdx X.p0_le)).toBlocks₂₂.det := fun M => by
    unfold lminor
    congr 1
  rw [Matrix.submatrix_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply,
    Nat.sub_add_cancel X.p0_le, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, ← hm] at h
  exact h

theorem minor_sq_le {r : ℕ} (X : Data E r) {x0 x b : Frame X.Ψ r} (h0 : IsOrth X x0)
    (hx : IsOrth X x) (hb : b ∈ Bor X.Ψ r) {z : V (nd X)} (hz : z ∈ OmF X x0)
    (he : cpt X x0 z = rmul x b) {a : ℝ} (ha : rhF X x0 z ≤ a) (τ : X.Ψ) :
    ‖lminor ((mat x0 τ)⁻¹ * mat x τ) ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩‖ ^ 2 ≤ Real.exp a := by
  classical
  have h := (FramePotential.frame_potential_basic r X x0 h0).2.2.2 z hz
  rw [he] at h
  simp only [FramePotential.factor_rmul X x0 x hb, FramePotential.norm_dmin_of_isOrth X hx,
    one_div, Finset.prod_inv_distrib, Real.exp_neg, inv_inj] at h
  refine le_trans ?_ (h.le.trans (Real.exp_le_exp.2 ha))
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ τ)]
  refine le_mul_of_one_le_right (by positivity) ?_
  exact Finset.prod_induction _ (fun t : ℝ => 1 ≤ t) (fun _ _ => one_le_mul_of_one_le_of_one_le)
    le_rfl fun σ _ => FramePotential.one_le_minor_of_isOrth X h0 hx σ

theorem muF_sublevel_lt_top : MeasInvStatement (E := E) → ∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → ∀ a : ℝ,
    muF X x0 {z | rhF X x0 z ≤ a} < ⊤ := by
  intro hI r X x0 h0 a
  set M : ℝ := Real.sqrt (((r : ℝ) + 1) * Real.exp a) with hM
  have hc : Continuous fun g : Frame X.Ψ r => rmul x0 g := by
    refine continuous_pi fun τ => ?_
    have hm : Continuous fun x : Frame X.Ψ r => mat x τ := continuous_apply τ
    exact continuous_const.matrix_mul hm
  have hK : IsCompact ((fun g : Frame X.Ψ r => rmul x0 g) '' Metric.closedBall 0 M ∩
      {x | IsOrth X x}) :=
    ((isCompact_closedBall _ _).image hc).inter_right (isClosed_isOrth X)
  have hfin := SatFin.muF_sat_lt_top hI r X x0 h0 _ hK fun x hx => IW.orth_mem_dom X x hx.2
  have hnull : muF X x0 (OmF X x0)ᶜ = 0 := by
    unfold muF
    refine withDensity_absolutelyContinuous _ _ ?_
    rw [Measure.restrict_apply (OntoB.isOpen_OmF X x0).measurableSet.compl]
    simp
  refine lt_of_le_of_lt (measure_mono (t := sat X x0 _ ∪ (OmF X x0)ᶜ) fun z ha => ?_)
    (measure_union_lt_top hfin (by rw [hnull]; exact ENNReal.zero_lt_top))
  by_cases hz : z ∈ OmF X x0
  swap
  · exact Or.inr hz
  obtain ⟨x, hx, b, hb, he⟩ := ortho_holds r X _ hz
  refine Or.inl ⟨hz, x, ⟨⟨fun τ i j => ((mat x0 τ)⁻¹ * mat x τ : Matrix (Fin r) (Fin r) ℂ) i j, ?_, ?_⟩, hx⟩,
    b, hb, he⟩
  · have hM0 : 0 ≤ M := Real.sqrt_nonneg _
    refine mem_closedBall_zero_iff.2 ?_
    refine (pi_norm_le_iff_of_nonneg hM0).2 fun τ => (pi_norm_le_iff_of_nonneg hM0).2 fun i =>
      (pi_norm_le_iff_of_nonneg hM0).2 fun j => ?_
    refine Real.le_sqrt_of_sq_le ((entry_sq_le X h0 hx τ i j).trans ?_)
    exact mul_le_mul_of_nonneg_left (minor_sq_le X h0 hx hb hz he ha τ) (by positivity)
  · funext τ
    have hu : IsUnit (mat x0 τ).det := isUnit_iff_ne_zero.mpr (ExF.det_ne_of_orth X h0 τ)
    exact Matrix.mul_nonsing_inv_cancel_left (mat x0 τ) (mat x τ) hu

end GlobalTheory.SublevelFin
