import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExhaustFStatementPfC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FourierCoefficientDomain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExhaustStatementPfC

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.ExF

open NumberField Complex Matrix Topology Filter ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst
  ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.ExhA ReciprocityTheory.ChartRestriction.G.AR.Up.ExhB
  ReciprocityTheory.ChartRestriction.G.AR.Up.ExhC ReciprocityTheory.ChartRestriction.G.AR.Up.ExhD ReciprocityTheory.ChartRestriction.G.AR.Up.ExhE
open scoped ComplexConjugate ComplexOrder ContDiff

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem cd_nM (τ : X.Ψ) (a b : Fin r) : ContDiff ℂ ∞ fun z : V (nd X) => nM X z τ a b := by
  show ContDiff ℂ ∞ fun z : V (nd X) => nmat X z τ a b
  unfold nmat
  by_cases h : b < a
  · simp only [dif_pos h]
    first
      | exact (EuclideanSpace.proj (𝕜 := ℂ) _).contDiff
      | fun_prop
      | exact ((EuclideanSpace.proj (𝕜 := ℂ) _).contDiff).congr fun z => rfl
  · simp only [dif_neg h]
    exact contDiff_const

theorem unipotentFrame_inv_eq_adjugate (z : V (nd X)) (τ : X.Ψ) : (n1 X z τ)⁻¹ = (n1 X z τ).adjugate := by
  have hdet : (n1 X z τ).det = 1 := by
    rw [Matrix.det_of_lowerTriangular]
    · simp [n1, nM_diag]
    · intro i j hij
      have hij' : i < j := OrderDual.toDual_lt_toDual.1 hij
      exact nM_upper X z τ (show Fin.castLE X.p0_le i < Fin.castLE X.p0_le j from hij')
  rw [Matrix.inv_def, hdet]
  simp

private lemma cd_det_lemma {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra 𝕜 ℂ] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] {k : ℕ} {M : F → Matrix (Fin k) (Fin k) ℂ}
    (h : ∀ i j, ContDiff 𝕜 ∞ fun z => M z i j) : ContDiff 𝕜 ∞ fun z => (M z).det := by
  simp only [Matrix.det_apply, Units.smul_def, zsmul_eq_mul]
  exact ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun i _ => h _ _)

private lemma cd_adj_lemma_2 {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra 𝕜 ℂ] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] {k : ℕ} {M : F → Matrix (Fin k) (Fin k) ℂ}
    (h : ∀ i j, ContDiff 𝕜 ∞ fun z => M z i j) (i j : Fin k) :
    ContDiff 𝕜 ∞ fun z => (M z).adjugate i j := by
  simp only [Matrix.adjugate_apply]
  refine cd_det_lemma fun a b => ?_
  by_cases hab : a = j
  · simp only [Matrix.updateRow_apply, hab, if_true]
    exact contDiff_const
  · simp only [Matrix.updateRow_apply, hab, if_false]
    exact h a b

theorem cd_Zt (τ : X.Ψ) (a : Fin X.p0) (m : Fin (r - X.p0)) :
    ContDiff ℂ ∞ fun z : V (nd X) => Zt X z τ a m := by
  have hfun : (fun z : V (nd X) => Zt X z τ a m) =
      fun z => ∑ k, Wm X z τ m k * (n1 X z τ).adjugate k a := by
    funext z
    simp only [Zt, Matrix.transpose_apply, Matrix.mul_apply, unipotentFrame_inv_eq_adjugate]
  rw [hfun]
  refine ContDiff.sum fun k _ => ContDiff.mul ?_ ?_
  · show ContDiff ℂ ∞ fun z : V (nd X) => nM X z τ (qI X m) (Fin.castLE X.p0_le k)
    exact cd_nM X τ _ _
  · refine cd_adj_lemma_2 (M := fun z : V (nd X) => n1 X z τ) (fun i j => ?_) k a
    show ContDiff ℂ ∞ fun z : V (nd X) => nM X z τ (Fin.castLE X.p0_le i) (Fin.castLE X.p0_le j)
    exact cd_nM X τ _ _

theorem cd_Am_entry (τ : X.Ψ) (a c : Fin X.p0) :
    ContDiff ℝ ∞ fun z : V (nd X) => Am X z τ a c := by
  have hZ : ∀ a m, ContDiff ℝ ∞ fun z : V (nd X) => Zt X z τ a m :=
    fun a m => (cd_Zt X τ a m).restrict_scalars ℝ
  have hfun : (fun z : V (nd X) => Am X z τ a c) = fun z =>
      (1 : Matrix (Fin X.p0) (Fin X.p0) ℂ) a c - ∑ m, Zt X z τ a m * star (Zt X z τ c m) := by
    funext z
    simp only [Am, Matrix.sub_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [hfun]
  refine contDiff_const.sub (ContDiff.sum fun m _ => (hZ a m).mul ?_)
  first
    | exact (hZ c m).star
    | exact Complex.conjCLE.contDiff.comp (hZ c m)

theorem cd_detAm (τ : X.Ψ) : ContDiff ℝ ∞ fun z : V (nd X) => (Am X z τ).det := by
  exact cd_det_lemma (M := fun z : V (nd X) => Am X z τ) fun a c => cd_Am_entry X τ a c

theorem rhF_contDiffAt (x0 : Frame X.Ψ r) (ho : IsOrth X x0) {z : V (nd X)} (hz : z ∈ OmF X x0) : ContDiffAt ℝ ∞ (rhF X x0) z := by
  have hfun : rhF X x0 = fun w => -∑ τ, Real.log ‖(Am X w τ).det‖ := funext (rhF_eq_sum X x0 ho)
  have hpd := (mem_OmF_iff X x0 ho z).1 hz
  rw [hfun]
  refine (ContDiffAt.sum fun τ _ => ?_).neg
  have hne : (Am X z τ).det ≠ 0 := (hpd τ).det_pos.ne'
  have h1 : ContDiffAt ℝ ∞ (fun w : V (nd X) => (Am X w τ).det) z := (cd_detAm X τ).contDiffAt
  have h2 : ContDiffAt ℝ ∞ (fun w : V (nd X) => ‖(Am X w τ).det‖) z :=
    (contDiffAt_norm ℂ hne).comp z h1
  exact h2.log (norm_ne_zero_iff.2 hne)

theorem T_cd {n : ℕ} : ContDiff ℝ ∞ fun z : V n => Real.log (1 + ‖z‖ ^ 2) := by
  exact (contDiff_const.add (contDiff_norm_sq ℂ)).log fun z => by positivity

theorem eF_contDiffAt (x0 : Frame X.Ψ r) (ho : IsOrth X x0) {z : V (nd X)} (hz : z ∈ OmF X x0) : ContDiffAt ℝ ∞ (eF X x0) z := by
  exact (rhF_contDiffAt X x0 ho hz).add (T_cd (n := nd X)).contDiffAt

theorem isOpen_OmF (x0 : Frame X.Ψ r) : IsOpen (OmF X x0) := by
  have hc : Continuous fun z : V (nd X) => cpt X x0 z := by
    refine continuous_pi fun τ => continuous_pi fun a => continuous_pi fun b => ?_
    have hfun : (fun z : V (nd X) => cpt X x0 z τ a b) = fun z => ∑ k, x0 τ a k * nM X z τ k b := by
      funext z
      have h := congrFun (congrFun (mat_cpt X x0 z τ) a) b
      simpa [mat, Matrix.mul_apply] using h
    rw [hfun]
    exact continuous_finset_sum _ fun k _ => continuous_const.mul (cd_nM X τ k b).continuous
  have hmat : ∀ τ : X.Ψ, Continuous fun x : Frame X.Ψ r => mat x τ := fun τ =>
    continuous_pi fun a => continuous_pi fun b =>
      (continuous_apply b).comp ((continuous_apply a).comp (continuous_apply τ))
  have hdet : ∀ τ : X.Ψ, Continuous fun x : Frame X.Ψ r => (mat x τ).det :=
    fun τ => (hmat τ).matrix_det
  have hdmin : ∀ τ i, Continuous fun x : Frame X.Ψ r => dmin X.Gm x τ i := by
    intro τ i
    unfold dmin lminor
    refine Continuous.matrix_det ?_
    refine continuous_pi fun a => continuous_pi fun b => ?_
    simp only [Matrix.submatrix_apply, FD.gram, Matrix.of_apply, FD.hermC, FD.col, mat]
    fun_prop
  have hset : OmF X x0 = ⋂ τ : X.Ψ, ({z | (mat (cpt X x0 z) τ).det ≠ 0} ∩
      ⋂ i : Fin (r + 1), {z | 0 < psgn X.p0 i * (dmin X.Gm (cpt X x0 z) τ i).re}) := by
    ext z
    simp only [OmF, Set.mem_setOf_eq, X.mem_dom_iff, Set.mem_iInter, Set.mem_inter_iff]
  rw [hset]
  refine isOpen_iInter_of_finite fun τ => IsOpen.inter ?_ (isOpen_iInter_of_finite fun i => ?_)
  · exact isOpen_ne_fun ((hdet τ).comp hc) continuous_const
  · exact isOpen_lt continuous_const
      (continuous_const.mul (Complex.continuous_re.comp ((hdmin τ i).comp hc)))

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.ExF
