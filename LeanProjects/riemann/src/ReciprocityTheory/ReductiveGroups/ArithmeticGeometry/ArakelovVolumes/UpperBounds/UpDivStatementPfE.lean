import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.UpDivStatementPfD
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfH
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfE
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExhaustFStatementPfE
import ReciprocityTheory.L2DbarEstimates.LeviForms.LogNormSq
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.AApproxC

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

namespace UpDivE

open NumberField Complex Topology Filter ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates UpDivD
open scoped ContDiff

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
variable (X : Data E r) (Xa : ArchInM X) (x0 : Frame X.Ψ r) (bb : ℝ)

theorem w_hol (k : Fin Xa.N) : DifferentiableOn ℂ (fun z => Xa.w k (cpt X x0 z)) (OmF X x0) := by
  exact ReciprocityTheory.ChartRestriction.G.AR.Up.OntoB.hol_comp (X := X) (x0 := x0) (Xa.w_van k).1.1.1.1

theorem Sw_eq : Sw X Xa x0 = fun z => sqNorm fun k => Xa.w k (cpt X x0 z) := by
  funext z
  simp [Sw, sqNorm, Complex.sq_norm]

theorem logSw_cdAt {z : V (nd X)} (hz : z ∈ OmF X x0) :
    ContDiffAt ℝ ∞ (fun y => Real.log (Sw X Xa x0 y)) z := by
  have hopen := ReciprocityTheory.ChartRestriction.G.AR.Up.OntoB.isOpen_OmF (X := X) (x0 := x0)
  have hk : ∀ k, ContDiffAt ℝ ∞ (fun y => ‖Xa.w k (cpt X x0 y)‖ ^ 2) z := by
    intro k
    have hd := w_hol X Xa x0 k
    have h1 : ContDiffAt ℂ ∞ (fun y => Xa.w k (cpt X x0 y)) z :=
      ReciprocityTheory.ChartRestriction.G.AR.Up.HE.contDiffAt_of_punct hopen hd hz
    exact (h1.restrict_scalars ℝ).norm_sq ℝ
  have hS : ContDiffAt ℝ ∞ (Sw X Xa x0) z := by
    have : Sw X Xa x0 = fun y => ∑ k, ‖Xa.w k (cpt X x0 y)‖ ^ 2 := rfl
    rw [this]
    exact ContDiffAt.sum fun k _ => hk k
  have hpos : 0 < Sw X Xa x0 z := by
    obtain ⟨k, hk0⟩ := Xa.w_nz _ hz
    exact Finset.sum_pos' (fun k _ => by positivity) ⟨k, Finset.mem_univ _, pow_pos (norm_pos_iff.2 hk0) 2⟩
  exact hS.log hpos.ne'

theorem plurisubharmonicWeight_smooth : ContDiffOn ℝ ∞ (ph0 X Xa x0 bb) (OmF X x0) := by
  intro z hz
  have h1 := ReciprocityTheory.ChartRestriction.G.AR.Up.IW.phla_cpt_cdAt (X := X) x0 hz Xa.Fp
  have h2 := ReciprocityTheory.ChartRestriction.G.AR.Up.OntoB.logDens_contDiffAt (X := X) (x0 := x0) hz
  have h3 := logSw_cdAt X Xa x0 hz
  have h4 := ReciprocityTheory.ChartRestriction.G.AR.Up.OntoB.rhF_contDiffAt (X := X) (x0 := x0) hz
  have h := ((h1.sub h2).add ((contDiffAt_const (c := (1 / 2 : ℝ))).mul h3)).sub
    ((contDiffAt_const (c := bb)).mul h4)
  exact h.contDiffWithinAt

theorem levi_logSw_nonneg {z : V (nd X)} (hz : z ∈ OmF X x0) (ξ : Fin (nd X) → ℂ) :
    0 ≤ (leviV (nd X) (fun y => ((Real.log (Sw X Xa x0 y) : ℝ) : ℂ)) z ξ).re := by
  have hopen := ReciprocityTheory.ChartRestriction.G.AR.Up.OntoB.isOpen_OmF (X := X) (x0 := x0)
  simp only [Sw_eq X Xa x0]
  have hg : ∀ k, ContDiffAt ℂ 2 (fun y => Xa.w k (cpt X x0 y)) z := by
    intro k
    have hd := w_hol X Xa x0 k
    exact (ReciprocityTheory.ChartRestriction.G.AR.Up.HE.contDiffAt_of_punct hopen hd hz).of_le (by norm_cast)
  have hne : (fun k => Xa.w k (cpt X x0 z)) ≠ 0 := by
    obtain ⟨k, hk0⟩ := Xa.w_nz _ hz
    intro h
    exact hk0 (congrFun h k)
  have hl := leviLogNormSq (nd X) Xa.N (fun k y => Xa.w k (cpt X x0 y)) z ξ hg hne
  beta_reduce at hl
  rw [hl, Complex.ofReal_re]
  have hnn : ∀ {p : ℕ} (v : Fin p → ℂ), 0 ≤ sqNorm v := fun v =>
    Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
  exact div_nonneg (hnn _) (hnn _)

theorem leviForm_weight_nonneg {m : ℝ} (hbm : bb ≤ m) (ho : IsOrth X x0)
    (hmar : ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ,
      m * leviRh X x0 z ξ ≤ leviO X x0 (phla X Xa.Fp) z ξ - leviDens X x0 z ξ)
    {z : V (nd X)} (hz : z ∈ OmF X x0) (ξ : Fin (nd X) → ℂ) :
    0 ≤ (leviV (nd X) (fun w => ((ph0 X Xa x0 bb w : ℝ) : ℂ)) z ξ).re := by
  have hA := (IW.phla_cpt_cdAt X x0 hz Xa.Fp).of_le (by norm_cast : (2 : WithTop ℕ∞) ≤ ∞)
  have hB := (OntoB.logDens_contDiffAt hz).of_le (by norm_cast : (2 : WithTop ℕ∞) ≤ ∞)
  have hC := (logSw_cdAt X Xa x0 hz).of_le (by norm_cast : (2 : WithTop ℕ∞) ≤ ∞)
  have hD := (OntoB.rhF_contDiffAt hz).of_le (by norm_cast : (2 : WithTop ℕ∞) ≤ ∞)
  set u : Fin 4 → V (nd X) → ℝ := ![fun w => phla X Xa.Fp (cpt X x0 w),
    fun w => -1 * Real.log (densF X x0 w) + 0, fun w => 1 / 2 * Real.log (Sw X Xa x0 w) + 0,
    fun w => -bb * rhF X x0 w + 0] with hu
  have hu0 : u 0 = fun w => phla X Xa.Fp (cpt X x0 w) := rfl
  have hu1 : u 1 = fun w => -1 * Real.log (densF X x0 w) + 0 := rfl
  have hu2 : u 2 = fun w => 1 / 2 * Real.log (Sw X Xa x0 w) + 0 := rfl
  have hu3 : u 3 = fun w => -bb * rhF X x0 w + 0 := rfl
  have hcu : ∀ i, ContDiffAt ℝ 2 (u i) z := by
    intro i; fin_cases i
    · show ContDiffAt ℝ 2 (u 0) z; rw [hu0]; exact hA
    · show ContDiffAt ℝ 2 (u 1) z; rw [hu1]; exact (contDiffAt_const.mul hB).add contDiffAt_const
    · show ContDiffAt ℝ 2 (u 2) z; rw [hu2]; exact (contDiffAt_const.mul hC).add contDiffAt_const
    · show ContDiffAt ℝ 2 (u 3) z; rw [hu3]; exact (contDiffAt_const.mul hD).add contDiffAt_const
  have he : (fun w => ((ph0 X Xa x0 bb w : ℝ) : ℂ)) = fun w => ((∑ i, u i w : ℝ) : ℂ) := by
    funext w
    rw [Fin.sum_univ_four, hu0, hu1, hu2, hu3]
    unfold ph0
    push_cast; ring
  rw [he, leviV_ofReal_sum hcu, Complex.re_sum, Fin.sum_univ_four]
  have e1 := Y.leviV_const_mul (f := fun w => Real.log (densF X x0 w)) hB (-1) 0 ξ
  have e2 := Y.leviV_const_mul (f := fun w => Real.log (Sw X Xa x0 w)) hC (1 / 2) 0 ξ
  have e3 := Y.leviV_const_mul (f := fun w => rhF X x0 w) hD (-bb) 0 ξ
  rw [hu0, hu1, hu2, hu3, e1, e2, e3]
  have hm := hmar z hz ξ
  have hrh := ExF.levi_rhF_nonneg X x0 ho hz ξ
  have hlw := levi_logSw_nonneg X Xa x0 hz ξ
  unfold leviO leviM leviDens leviRh at hm
  simp only [Complex.re_ofReal_mul] at *
  have : (m - bb) * (leviV (nd X) (fun y => ((rhF X x0 y : ℝ) : ℂ)) z ξ).re ≥ 0 :=
    mul_nonneg (by linarith) hrh
  nlinarith

end UpDivE

end ReciprocityTheory.ChartRestriction.G.AR.Up
