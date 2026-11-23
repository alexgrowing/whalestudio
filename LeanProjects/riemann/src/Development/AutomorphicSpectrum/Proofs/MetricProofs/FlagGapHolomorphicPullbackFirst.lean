import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.HasStepCharts
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SelM
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsClosedSectionBoundary
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LinearIndependentMulSelM

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.CWeight

section Calc

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {N : ℕ}

def SmMat (M : E → Matrix (Fin N) (Fin N) ℂ) (w : E) : Prop :=
  ∀ a b, ContDiffAt ℝ ∞ (fun u => M u a b) w

theorem SmMat.mul {M M' : E → Matrix (Fin N) (Fin N) ℂ} {w : E} (h : SmMat M w) (h' : SmMat M' w) :
    SmMat (fun u => M u * M' u) w := by
  intro a b
  simp only [Matrix.mul_apply]
  exact ContDiffAt.sum fun c _ => (h a c).mul (h' c b)

theorem SmMat.conjTranspose {M : E → Matrix (Fin N) (Fin N) ℂ} {w : E} (h : SmMat M w) :
    SmMat (fun u => (M u)ᴴ) w := by
  intro a b
  simp only [Matrix.conjTranspose_apply]
  exact (Complex.conjCLE : ℂ ≃L[ℝ] ℂ).contDiff.contDiffAt.comp w (h b a)

theorem SmMat.minor {M : E → Matrix (Fin N) (Fin N) ℂ} {w : E} (h : SmMat M w) (I J : Finset (Fin N)) :
    ContDiffAt ℝ ∞ (fun u => minorIJ (M u) I J) w := by
  unfold minorIJ
  by_cases e : I.card = J.card
  · simp only [dif_pos e, Matrix.det_apply']
    refine ContDiffAt.sum fun σ _ => contDiffAt_const.mul ?_
    exact contDiffAt_prod fun i _ => h _ _
  · simp only [dif_neg e]
    exact contDiffAt_const

theorem contDiffAt_blockPot (j : ℕ) (i : Fin N) {G h : E → Matrix (Fin N) (Fin N) ℂ} {w : E}
    (hG : SmMat G w) (hh : SmMat h w) (hpos : (G w).PosDef) (hdet : (h w).det ≠ 0) :
    ContDiffAt ℝ ∞ (fun u => blockPot j i (G u) (h u)) w := by
  have hre : ∀ {f : E → ℂ}, ContDiffAt ℝ ∞ f w → 0 < f w →
      ContDiffAt ℝ ∞ (fun u => Real.log (f u).re) w := fun hf h0 =>
    (Complex.reCLM.contDiff.contDiffAt.comp w hf).log (Complex.lt_def.1 h0).1.ne'
  have hfac : ContDiffAt ℝ ∞ (fun u => detFac j i (G u)) w := by
    unfold detFac
    refine ContDiffAt.mul ?_ ?_
    · by_cases c : j ≤ (i : ℕ) + 1
      · simpa only [if_pos c] using hG.minor _ _
      · simpa only [if_neg c] using contDiffAt_const
    · by_cases c : (i : ℕ) + 1 = N
      · simpa only [if_pos c] using hG.minor _ _
      · simpa only [if_neg c] using contDiffAt_const
  have hfac0 : 0 < detFac j i (G w) := by
    unfold detFac
    refine mul_pos ?_ ?_
    · split_ifs
      · exact GramPot.minor_pos hpos _
      · exact zero_lt_one
    · split_ifs
      · exact GramPot.minor_pos hpos _
      · exact zero_lt_one
  unfold blockPot
  refine (contDiffAt_const.mul (hre hfac hfac0)).add ?_
  by_cases c : IsProperStep N j i
  · simp only [if_pos c]
    refine contDiffAt_const.mul (hre ((hh.conjTranspose.mul hG).mul hh |>.minor _ _) ?_)
    have hu : IsUnit (h w) := (Matrix.isUnit_iff_isUnit_det _).2 hdet.isUnit
    exact GramPot.minor_pos
      (hpos.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit hu)) _
  · simp only [if_neg c]
    exact contDiffAt_const

end Calc

section Chart

variable {e n : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

theorem contDiffAt_comp_holoMap {A : FinHolAtlas e X} {B : FinHolAtlas n Y} {pr : X → Y}
    (hp : HoloMap A B pr) {U : Set Y} (hU : IsOpen U) {f : Y → ℝ} (hf : B.SmoothOn U f)
    (c : Fin A.n) {w : Fin e → ℂ} (hw : w ∈ (A.chart c).target)
    (hwU : pr ((A.chart c).symm w) ∈ U) :
    ContDiffAt ℝ ∞ (fun u => f (pr ((A.chart c).symm u))) w := by
  obtain ⟨k, hk⟩ := B.cover (pr ((A.chart c).symm w))
  have h1 : ContDiffAt ℝ ∞ (f ∘ (B.chart k).symm) (B.chart k (pr ((A.chart c).symm w))) := by
    refine (hf k).contDiffAt
      (((B.chart k).isOpen_inter_preimage_symm hU).mem_nhds ⟨(B.chart k).map_source hk, ?_⟩)
    simpa [(B.chart k).left_inv hk] using hwU
  have h2 : ContDiffAt ℝ ∞ (B.chart k ∘ pr ∘ (A.chart c).symm) w :=
    (hp.2 c k w ⟨hw, hk⟩).contDiffAt.restrict_scalars ℝ
  refine (ContDiffAt.comp w h1 h2).congr_of_eventuallyEq ?_
  filter_upwards [((A.chart c).isOpen_inter_preimage_symm
    ((B.chart k).open_source.preimage hp.1)).mem_nhds ⟨hw, hk⟩] with u hu
  simp only [Function.comp_apply, (B.chart k).left_inv hu.2]

theorem contDiffAt_of_re_im {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {g : E → ℂ} {w : E}
    (h1 : ContDiffAt ℝ ∞ (fun u => (g u).re) w) (h2 : ContDiffAt ℝ ∞ (fun u => (g u).im) w) :
    ContDiffAt ℝ ∞ g w := by
  have e : g = fun u => (((g u).re : ℝ) : ℂ) + (((g u).im : ℝ) : ℂ) * Complex.I := by
    funext u
    exact (Complex.re_add_im _).symm
  rw [e]
  exact (Complex.ofRealCLM.contDiff.contDiffAt.comp w h1).add
    ((Complex.ofRealCLM.contDiff.contDiffAt.comp w h2).mul contDiffAt_const)

end Chart

theorem smoothOn_stepPh : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (p : Ψ × Fin N) (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)) (e : ℕ) (R : AnLogRes (mCoordIdeal (y ∘ v)) ⊤ e) (pr : R.X → BM.Rb.X) (hp : HoloMap R.A BM.Rb.A pr), HasStepCharts M BM p κ v R pr → IsPotential R.A (potOf R (fsHerm ιk fun k => M.dy p (κ k))) → R.A.SmoothOn (bdry (fun x y => BM.s (pr x) (pr y)))ᶜ (stepPh M BM p v R pr) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n BM p Kk _ ιk _ κ v e R pr hp hS hP c w hw
  refine ContDiffAt.contDiffWithinAt ?_
  obtain ⟨hwt, hwb⟩ := hw
  have hb : pr ((R.A.chart c).symm w) ∉ bdry BM.s := hwb
  obtain ⟨W, l, H, D, hWo, hyW, hWU, hWO, hH, hHd, hD, hD0, heq⟩ :=
    hS ((R.A.chart c).symm w) ((R.A.chart c).symm w) (R.mem_U _)
  have hcl : IsClosed (bdry BM.s) := isClosed_bdry_of_isSection _ _ _ _ _ BM.sec
  have hOo : IsOpen (W ∩ pr ⁻¹' (bdry BM.s)ᶜ) := hWo.inter (hcl.isOpen_compl.preimage hp.1)
  have hnhd : (R.A.chart c).target ∩ (R.A.chart c).symm ⁻¹' (W ∩ pr ⁻¹' (bdry BM.s)ᶜ) ∈ 𝓝 w :=
    ((R.A.chart c).isOpen_inter_preimage_symm hOo).mem_nhds ⟨hwt, hyW, hb⟩
  have hOb : IsOpen (BM.O l \ bdry BM.s) := (BM.O_open l).sdiff hcl
  have hmemO : pr ((R.A.chart c).symm w) ∈ BM.O l \ bdry BM.s := ⟨hWO _ hyW, hb⟩
  have hG : SmMat (fun u => BM.G l p.1 (pr ((R.A.chart c).symm u))) w := fun a b =>
    contDiffAt_of_re_im
      (contDiffAt_comp_holoMap hp hOb (BM.G_smooth l p.1 a b).1 c hwt hmemO)
      (contDiffAt_comp_holoMap hp hOb (BM.G_smooth l p.1 a b).2 c hwt hmemO)
  have hHm : SmMat (fun u => H ((R.A.chart c).symm u)) w := fun a b =>
    (hH a b c w ⟨hwt, hyW⟩).contDiffAt.restrict_scalars ℝ
  have hDm : ContDiffAt ℝ ∞ (fun u => D ((R.A.chart c).symm u)) w :=
    (hD c w ⟨hwt, hyW⟩).contDiffAt.restrict_scalars ℝ
  have hD1 : D ((R.A.chart c).symm w) ≠ 0 := hD0 _ hyW
  have hbp := contDiffAt_blockPot j p.2 hG hHm (BM.G_pos l p.1 _ hmemO).2 (hHd _ hyW).2
  have hlog : ContDiffAt ℝ ∞ (fun u => Real.log ‖D ((R.A.chart c).symm u)‖) w :=
    (hDm.norm ℝ hD1).log (norm_ne_zero_iff.2 hD1)
  have hpot : ContDiffAt ℝ ∞ (fun u => Real.log ((fsHerm ιk fun k => M.dy p (κ k)).h
      (R.lift ((R.A.chart c).symm w) ((R.A.chart c).symm u)))) w :=
    (hP.1 ((R.A.chart c).symm w) c).contDiffAt
      (((R.A.chart c).isOpen_inter_preimage_symm (R.isOpen_U _)).mem_nhds ⟨hwt, R.mem_U _⟩)
  refine ((hbp.add hlog).sub hpot).congr_of_eventuallyEq ?_
  filter_upwards [hnhd] with u hu
  have := heq _ hu.2.1 hu.2.2
  simp only [Function.comp_apply]
  linarith

end GlobalTheory.CompanionTheory.Ar.PB.CWeight
