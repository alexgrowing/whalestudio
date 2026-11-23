import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetMeasStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExhaustStatementPfB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FourierCoefficientDomain
import ReciprocityTheory.L2DbarEstimates.LeviForms.EventuallyDifferentiableAtOfContDiffAt

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.OntoB

open NumberField Complex Matrix Topology Filter ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst
  ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.ExhC ReciprocityTheory.ChartRestriction.G.AR.Up.ExhD
open scoped ComplexConjugate ContDiff

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) (x0 : Frame X.Ψ r)

theorem cd_nmat (τ : X.Ψ) (a b : Fin r) : ContDiff ℂ ∞ fun z : V (nd X) => nmat X z τ a b := by
  unfold nmat
  by_cases h : b < a
  · simp only [dif_pos h]
    first
    | fun_prop
    | exact (EuclideanSpace.proj (𝕜 := ℂ) _).contDiff
  · simp only [dif_neg h]
    exact contDiff_const

theorem cd_cpt_entry (τ : X.Ψ) (a b : Fin r) :
    ContDiff ℂ ∞ fun z : V (nd X) => cpt X x0 z τ a b := by
  have he : (fun z : V (nd X) => cpt X x0 z τ a b) = fun z => ∑ c, x0 τ a c * nmat X z τ c b := by
    funext z
    simp [cpt, rmul, mat, Matrix.mul_apply]
  rw [he]
  exact ContDiff.sum fun c _ => contDiff_const.mul (cd_nmat X τ c b)

theorem cd_cpt : ContDiff ℂ ∞ (cpt X x0) := contDiff_pi.mpr fun τ => contDiff_pi.mpr fun a => contDiff_pi.mpr fun b =>
  cd_cpt_entry X x0 τ a b

theorem hol_comp {f : Frame X.Ψ r → ℂ} (hf : DifferentiableOn ℂ f X.dom) :
    DifferentiableOn ℂ (fun z => f (cpt X x0 z)) (OmF X x0) := hf.comp ((cd_cpt X x0).differentiable (by simp)).differentiableOn (fun _ hz => hz)

theorem isOpen_OmF : IsOpen (OmF X x0) := by
  have hmat : ∀ τ : X.Ψ, Continuous fun x : Frame X.Ψ r => mat x τ := fun τ =>
    continuous_matrix fun a b => (continuous_apply b).comp ((continuous_apply a).comp (continuous_apply τ))
  have hent : ∀ (τ : X.Ψ) (a b : Fin r), Continuous fun x : Frame X.Ψ r => x τ a b := fun τ a b =>
    (continuous_apply b).comp ((continuous_apply a).comp (continuous_apply τ))
  have hdmin : ∀ (τ : X.Ψ) (i : Fin (r + 1)), Continuous fun x : Frame X.Ψ r => dmin X.Gm x τ i := by
    intro τ i
    unfold dmin lminor
    refine Continuous.matrix_det ?_
    refine continuous_matrix fun a b => ?_
    simp only [Matrix.submatrix_apply, ReciprocityTheory.ChartRestriction.G.FD.gram, ReciprocityTheory.ChartRestriction.G.FD.hermC,
      ReciprocityTheory.ChartRestriction.G.FD.col, ReciprocityTheory.ChartRestriction.G.FD.mat, Matrix.of_apply]
    refine continuous_finset_sum _ fun c _ => continuous_finset_sum _ fun d _ => ?_
    exact ((hent τ c _).mul continuous_const).mul (Complex.continuous_conj.comp (hent τ d _))
  have hGG : GG X.Ψ X.Gm X.p0 = ⋂ τ : X.Ψ, ({x : Frame X.Ψ r | (mat x τ).det ≠ 0} ∩
      ⋂ i : Fin (r + 1), {x : Frame X.Ψ r | 0 < psgn X.p0 i * (dmin X.Gm x τ i).re}) := by
    ext x
    simp [GG]
  have hopen : IsOpen (GG X.Ψ X.Gm X.p0) := by
    rw [hGG]
    refine isOpen_iInter_of_finite fun τ => ?_
    refine IsOpen.inter (isOpen_ne_fun (hmat τ).matrix_det continuous_const)
      (isOpen_iInter_of_finite fun i => ?_)
    exact isOpen_lt continuous_const (continuous_const.mul (Complex.continuous_re.comp (hdmin τ i)))
  exact (cd_cpt X x0).continuous.isOpen_preimage _ hopen

theorem cd_dmin (τ : X.Ψ) (i : Fin (r + 1)) :
    ContDiff ℝ ∞ fun z : V (nd X) => dmin X.Gm (cpt X x0 z) τ i := by
  have hE : ∀ (τ : X.Ψ) (a b : Fin r), ContDiff ℝ ∞ fun z : V (nd X) => cpt X x0 z τ a b :=
    fun τ a b => (cd_cpt_entry X x0 τ a b).restrict_scalars ℝ
  have hC : ∀ (τ : X.Ψ) (a b : Fin r),
      ContDiff ℝ ∞ fun z : V (nd X) => starRingEnd ℂ (cpt X x0 z τ a b) := by
    intro τ a b
    have h := Complex.conjCLE.contDiff.comp (hE τ a b)
    simpa [Function.comp_def] using h
  unfold dmin lminor
  simp only [Matrix.det_apply, Units.smul_def, zsmul_eq_mul]
  refine ContDiff.sum fun σ _ => contDiff_const.mul ?_
  refine contDiff_prod fun k _ => ?_
  simp only [Matrix.submatrix_apply, ReciprocityTheory.ChartRestriction.G.FD.gram, ReciprocityTheory.ChartRestriction.G.FD.hermC,
      ReciprocityTheory.ChartRestriction.G.FD.col, ReciprocityTheory.ChartRestriction.G.FD.mat, Matrix.of_apply]
  refine ContDiff.sum fun c _ => ContDiff.sum fun d _ => ?_
  exact ((hE τ c _).mul contDiff_const).mul (hC τ d _)

variable {X x0}

theorem dmin_ne {z : V (nd X)} (hz : z ∈ OmF X x0) (τ : X.Ψ) (i : Fin (r + 1)) :
    dmin X.Gm (cpt X x0 z) τ i ≠ 0 := by
  intro h0
  have h1 : 0 < psgn X.p0 i * (dmin X.Gm (cpt X x0 z) τ i).re := (hz τ).2 i
  rw [h0, Complex.zero_re, mul_zero] at h1
  exact lt_irrefl _ h1

variable (X x0)

def LD (z : V (nd X)) : ℝ :=
  ∑ τ, ∑ i : Fin r, (-2) * Real.log ‖dmin X.Gm (cpt X x0 z) τ i.castSucc‖

variable {X x0}

theorem densF_pos {z : V (nd X)} (hz : z ∈ OmF X x0) : 0 < densF X x0 z := by
  unfold densF
  refine Finset.prod_pos fun τ _ => Finset.prod_pos fun i _ => ?_
  exact zpow_pos (norm_pos_iff.mpr (dmin_ne hz τ i.castSucc)) _

theorem log_densF {z : V (nd X)} (hz : z ∈ OmF X x0) : Real.log (densF X x0 z) = LD X x0 z := by
  have hp : ∀ (τ : X.Ψ) (i : Fin r), 0 < ‖dmin X.Gm (cpt X x0 z) τ i.castSucc‖ ^ (-2 : ℤ) :=
    fun τ i => zpow_pos (norm_pos_iff.mpr (dmin_ne hz τ i.castSucc)) _
  unfold densF LD
  rw [Real.log_prod (fun τ _ => (Finset.prod_pos fun i _ => hp τ i).ne')]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Real.log_prod (fun i _ => (hp τ i).ne')]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Real.log_zpow]
  norm_num

theorem LD_contDiffAt {z : V (nd X)} (hz : z ∈ OmF X x0) : ContDiffAt ℝ ∞ (LD X x0) z := by
  have hd : ∀ (τ : X.Ψ) (i : Fin (r + 1)),
      ContDiffAt ℝ ∞ (fun w => Real.log ‖dmin X.Gm (cpt X x0 w) τ i‖) z := by
    intro τ i
    have hne := dmin_ne hz τ i
    have h1 : ContDiffAt ℝ ∞ (fun w => ‖dmin X.Gm (cpt X x0 w) τ i‖) z :=
      (contDiffAt_norm ℂ hne).comp z (cd_dmin X x0 τ i).contDiffAt
    exact h1.log (norm_ne_zero_iff.mpr hne)
  unfold LD
  exact ContDiffAt.sum fun τ _ => ContDiffAt.sum fun i _ => contDiffAt_const.mul (hd τ i.castSucc)

theorem logDens_contDiffAt {z : V (nd X)} (hz : z ∈ OmF X x0) :
    ContDiffAt ℝ ∞ (fun w => Real.log (densF X x0 w)) z := by
  refine (LD_contDiffAt hz).congr_of_eventuallyEq ?_
  filter_upwards [(isOpen_OmF X x0).mem_nhds hz] with w hw using log_densF hw

theorem densF_continuousOn : ContinuousOn (densF X x0) (OmF X x0) := by
  intro z hz
  have h := Real.continuous_exp.continuousAt.comp (logDens_contDiffAt hz).continuousAt
  refine (ContinuousAt.congr h ?_).continuousWithinAt
  filter_upwards [(isOpen_OmF X x0).mem_nhds hz] with w hw using Real.exp_log (densF_pos hw)

theorem rhF_contDiffAt {z : V (nd X)} (hz : z ∈ OmF X x0) : ContDiffAt ℝ ∞ (rhF X x0) z := by
  have hd : ∀ (τ : X.Ψ) (i : Fin (r + 1)),
      ContDiffAt ℝ ∞ (fun w => Real.log ‖dmin X.Gm (cpt X x0 w) τ i‖) z := by
    intro τ i
    have hne := dmin_ne hz τ i
    have h1 : ContDiffAt ℝ ∞ (fun w => ‖dmin X.Gm (cpt X x0 w) τ i‖) z :=
      (contDiffAt_norm ℂ hne).comp z (cd_dmin X x0 τ i).contDiffAt
    exact h1.log (norm_ne_zero_iff.mpr hne)
  unfold rhF
  exact (ContDiffAt.sum fun τ _ => hd τ _).neg

theorem ka_contDiffAt (bb : ℝ) {z : V (nd X)} (hz : z ∈ OmF X x0) :
    ContDiffAt ℝ ∞ (kaF X x0 bb) z := by
  unfold kaF
  exact Real.contDiff_exp.contDiffAt.comp z (contDiffAt_const.mul (rhF_contDiffAt hz))

theorem levi_rh_nonneg (hGrad : RhGradFStatement (E := E)) (hx0 : IsOrth X x0) {z : V (nd X)}
    (hz : z ∈ OmF X x0) (ξ : Fin (nd X) → ℂ) :
    0 ≤ (leviV (nd X) (fun w => ((rhF X x0 w : ℝ) : ℂ)) z ξ).re := by
  have hG := hGrad r X x0 hx0 z hz ξ
  by_cases hC : ((X.Ψ.card * min X.p0 (r - X.p0) : ℕ) : ℝ) = 0
  · have hwd : ∀ w ∈ OmF X x0, ∀ j,
        wd (nd X) j (fun w => ((rhF X x0 w : ℝ) : ℂ)) w = 0 := by
      intro w hw j
      have h := hGrad r X x0 hx0 w hw (Pi.single j 1)
      rw [hC, zero_mul] at h
      have h' := le_antisymm h (Complex.normSq_nonneg _)
      rw [Complex.normSq_eq_zero] at h'
      simpa [Pi.single_apply] using h'
    have hwdb : ∀ w ∈ OmF X x0, ∀ k,
        wdb (nd X) k (fun w => ((rhF X x0 w : ℝ) : ℂ)) w = 0 := by
      intro w hw k
      have hd : DifferentiableAt ℝ (rhF X x0) w := (rhF_contDiffAt hw).differentiableAt (by simp)
      have hf : ∀ v, fderiv ℝ (fun w => ((rhF X x0 w : ℝ) : ℂ)) w v =
          ((fderiv ℝ (rhF X x0) w v : ℝ) : ℂ) := by
        intro v
        have hh : HasFDerivAt (fun w => ((rhF X x0 w : ℝ) : ℂ))
            (Complex.ofRealCLM.comp (fderiv ℝ (rhF X x0) w)) w :=
          Complex.ofRealCLM.hasFDerivAt.comp w hd.hasFDerivAt
        rw [hh.fderiv]
        rfl
      have h0 := hwd w hw k
      simp only [wd, hf] at h0
      simp only [wdb, hf]
      set p := fderiv ℝ (rhF X x0) w (bas (nd X) k)
      set q := fderiv ℝ (rhF X x0) w (Complex.I • bas (nd X) k)
      have h2 : (p : ℂ) - Complex.I * (q : ℂ) = 0 := by
        rcases div_eq_zero_iff.mp h0 with h0 | h0
        · exact h0
        · norm_num at h0
      have hp : p = 0 := by
        have h3 := congrArg Complex.re h2
        simpa using h3
      have hq : q = 0 := by
        have h3 := congrArg Complex.im h2
        simpa using h3
      rw [hp, hq]
      simp
    have hL : leviV (nd X) (fun w => ((rhF X x0 w : ℝ) : ℂ)) z ξ = 0 := by
      unfold leviV
      refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun k _ => ?_
      have hev : wdb (nd X) k (fun w => ((rhF X x0 w : ℝ) : ℂ)) =ᶠ[𝓝 z] fun _ => (0 : ℂ) := by
        filter_upwards [(isOpen_OmF X x0).mem_nhds hz] with w hw using hwdb w hw k
      have hfd : fderiv ℝ (wdb (nd X) k (fun w => ((rhF X x0 w : ℝ) : ℂ))) z = 0 := by
        rw [hev.fderiv_eq]
        simp
      simp [wd, hfd]
    rw [hL]
    simp
  · have hCpos : (0 : ℝ) < ((X.Ψ.card * min X.p0 (r - X.p0) : ℕ) : ℝ) :=
      lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm hC)
    have h0 : ((X.Ψ.card * min X.p0 (r - X.p0) : ℕ) : ℝ) * 0 ≤
        ((X.Ψ.card * min X.p0 (r - X.p0) : ℕ) : ℝ) *
          (leviV (nd X) (fun w => ((rhF X x0 w : ℝ) : ℂ)) z ξ).re := by
      rw [mul_zero]
      exact le_trans (Complex.normSq_nonneg _) hG
    exact le_of_mul_le_mul_left h0 hCpos

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.OntoB
