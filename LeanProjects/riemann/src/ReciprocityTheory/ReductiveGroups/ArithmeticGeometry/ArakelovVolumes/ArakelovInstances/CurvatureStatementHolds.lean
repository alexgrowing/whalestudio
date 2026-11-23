import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.CoefNonneg

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf

open Matrix NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.L2DbarEstimates Filter Topology

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem cd_coord (j : Fin (nd X)) : ContDiff ℝ 2 fun w : V (nd X) => w j := by
  first
  | fun_prop
  | exact ((EuclideanSpace.proj j).restrictScalars ℝ).contDiff
  | exact (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (nd X) => ℂ) j).contDiff

theorem cd_nmat (τ : X.Ψ) (a c : Fin r) : ContDiff ℝ 2 fun w : V (nd X) => mat (nmat X w) τ a c := by
  simp only [mat, nmat, Matrix.of_apply]
  split_ifs
  · exact cd_coord X _
  · exact contDiff_const
  · exact contDiff_const

theorem cd_dmin (x0 : Frame X.Ψ r) (τ : X.Ψ) (k : Fin (r + 1)) :
    ContDiff ℝ 2 fun w : V (nd X) => dmin X.Gm (cpt X x0 w) τ k := by
  have hM : ∀ a c : Fin r, ContDiff ℝ 2 fun w : V (nd X) => (mat x0 τ * mat (nmat X w) τ) a c :=
    cd_mul (fun _ => mat x0 τ) (fun w => mat (nmat X w) τ) (fun _ _ => contDiff_const) (cd_nmat X τ)
  have hMt : ∀ a c : Fin r, ContDiff ℝ 2 fun w : V (nd X) => ((mat x0 τ * mat (nmat X w) τ)ᵀ) a c :=
    fun a c => hM c a
  have hMc : ∀ a c : Fin r, ContDiff ℝ 2 fun w : V (nd X) =>
      ((mat x0 τ * mat (nmat X w) τ).map (starRingEnd ℂ)) a c :=
    fun a c => Complex.conjCLE.contDiff.comp (hM a c)
  have hG : ∀ a c : Fin r, ContDiff ℝ 2 fun w : V (nd X) =>
      ((mat x0 τ * mat (nmat X w) τ)ᵀ * X.Gm.map τ.1 * (mat x0 τ * mat (nmat X w) τ).map (starRingEnd ℂ)) a c :=
    cd_mul _ _ (cd_mul _ _ hMt (fun _ _ => contDiff_const)) hMc
  unfold dmin lminor
  simp only [FrameDegreeData.gram_eq]
  exact cd_det (fun w : V (nd X) => ((mat x0 τ * mat (nmat X w) τ)ᵀ * X.Gm.map τ.1 *
    (mat x0 τ * mat (nmat X w) τ).map (starRingEnd ℂ)).submatrix _ _) (fun a c => hG _ _)

theorem cd_lognorm {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (d : F → ℂ) (hd : ContDiff ℝ 2 d)
    (z : F) (hz : d z ≠ 0) : ContDiffAt ℝ 2 (fun w => Real.log ‖d w‖) z := by
  have h1 : ContDiffAt ℝ 2 (fun w => ‖d w‖) z := (hd.contDiffAt).norm ℝ hz
  exact h1.log (norm_ne_zero_iff.mpr hz)

theorem cd_h (x0 : Frame X.Ψ r) (z : V (nd X)) (hz : cpt X x0 z ∈ X.dom) (la : Wt X.Ψ r) :
    ContDiffAt ℝ 2 (fun w => -2 * Real.log (X.nfac la (cpt X x0 w))) z := by
  have hne : ∀ τ k, dmin X.Gm (cpt X x0 z) τ k ≠ 0 := fun τ k h => by
    have := (hz τ).2 k
    rw [h] at this
    simp at this
  have hev : ∀ᶠ w in 𝓝 z, ∀ τ k, dmin X.Gm (cpt X x0 w) τ k ≠ 0 := by
    rw [Filter.eventually_all]; intro τ
    rw [Filter.eventually_all]; intro k
    exact (cd_dmin X x0 τ k).continuous.continuousAt.eventually_ne (hne τ k)
  have hEq : (fun w => -2 * Real.log (X.nfac la (cpt X x0 w))) =ᶠ[𝓝 z] fun w => ∑ τ, ∑ i : Fin r,
      (la τ i : ℝ) * (Real.log ‖dmin X.Gm (cpt X x0 w) τ i.succ‖ -
        Real.log ‖dmin X.Gm (cpt X x0 w) τ i.castSucc‖) := by
    filter_upwards [hev] with w hw
    exact neg2log_nfac X la _ hw
  refine ContDiffAt.congr_of_eventuallyEq ?_ hEq
  exact ContDiffAt.sum fun τ _ => ContDiffAt.sum fun i _ => contDiffAt_const.mul
    ((cd_lognorm _ (cd_dmin X x0 τ _) z (hne τ _)).sub (cd_lognorm _ (cd_dmin X x0 τ _) z (hne τ _)))

theorem levi_formula (la : Wt X.Ψ r) (x0 : Frame X.Ψ r) (z : V (nd X)) (hz : cpt X x0 z ∈ X.dom)
    (b : Frame X.Ψ r) (hb : b ∈ Bor X.Ψ r) (hgram : ∀ τ, gram τ.1 X.Gm (mat (rmul (cpt X x0 z) b) τ) =
      diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)) (ξ : Fin (nd X) → ℂ) :
    (leviV (nd X) (fun w => ((-2 * Real.log (X.nfac la (cpt X x0 w)) : ℝ) : ℂ)) z ξ).re =
      ∑ τ, ∑ a : Fin r, ∑ j : Fin r, if (a : ℕ) < j then
        coef X la τ a j * ‖Yd X b z (WithLp.toLp 2 ξ) τ j a‖ ^ 2 else 0 := by
  rw [leviV_re_line (fun w => -2 * Real.log (X.nfac la (cpt X x0 w))) z (cd_h X x0 z hz la) ξ,
    line_levi hb hgram la]
  exact Finset.sum_congr rfl fun τ _ => tele X b z _ la τ

theorem curvature_statement_holds : CurvGGStatement (E := E) := by
  intro r X la x0 z hz
  obtain ⟨b, hb, hgr⟩ := MajorantNormalForms.exists_normal_frame X hz
  have hgram : ∀ τ, gram τ.1 X.Gm (mat (rmul (cpt X x0 z) b) τ) =
      diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ) := fun τ => (hgr τ).1
  have hval : ∀ ξ : Fin (nd X) → ℂ,
      (leviV (nd X) (fun w => ((-2 * Real.log (X.nfac la (cpt X x0 w)) : ℝ) : ℂ)) z ξ).re =
        ∑ τ, ∑ a : Fin r, ∑ j : Fin r, if (a : ℕ) < j then
          coef X la τ a j * ‖Yd X b z (WithLp.toLp 2 ξ) τ j a‖ ^ 2 else 0 := by
    intro ξ
    rw [leviV_re_line (fun w => -2 * Real.log (X.nfac la (cpt X x0 w))) z (cd_h X x0 z hz la) ξ,
      line_levi hb hgram la]
    exact Finset.sum_congr rfl fun τ _ => tele X b z _ la τ
  constructor
  · intro hdom ξ
    rw [hval]
    refine Finset.sum_nonneg fun τ _ => Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun j _ => ?_
    split_ifs with h
    · exact mul_nonneg (coef_nonneg X la hdom τ a j h) (sq_nonneg _)
    · exact le_rfl
  · intro hs ξ hξ
    rw [hval]
    have hu : (WithLp.toLp 2 ξ : V (nd X)) ≠ 0 := fun h => hξ (by simpa using congrArg WithLp.ofLp h)
    obtain ⟨τ, a, j, haj, hY⟩ := Yd_ne X b hb z _ hu
    have hnn : ∀ τ' (a' j' : Fin r), 0 ≤ (if (a' : ℕ) < j' then
        coef X la τ' a' j' * ‖Yd X b z (WithLp.toLp 2 ξ) τ' j' a'‖ ^ 2 else 0) := by
      intro τ' a' j'
      split_ifs with h
      · exact mul_nonneg (coef_pos X la hs τ' a' j' h).le (sq_nonneg _)
      · exact le_rfl
    refine Finset.sum_pos' (fun τ' _ => Finset.sum_nonneg fun a' _ => Finset.sum_nonneg fun j' _ => hnn τ' a' j')
      ⟨τ, Finset.mem_univ _, Finset.sum_pos' (fun a' _ => Finset.sum_nonneg fun j' _ => hnn τ a' j')
        ⟨a, Finset.mem_univ _, Finset.sum_pos' (fun j' _ => hnn τ a j') ⟨j, Finset.mem_univ _, ?_⟩⟩⟩
    rw [if_pos haj]
    exact mul_pos (coef_pos X la hs τ a j haj) (pow_pos (norm_pos_iff.2 hY) 2)

end ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf
