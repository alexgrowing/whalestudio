import Mathlib
import Development.AbelianVarietyTheory.Definitions.UpperBounds.SumNormSqWPos
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.IntegrandAemeasurable
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OmFConnPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExhaustGPf
import ReciprocityTheory.L2DbarEstimates.LeviForms.LogNormSq

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.Up.DivUpPf

noncomputable section

theorem logSum_contDiffAt {n N : ℕ} {U : Set (V n)} (hU : IsOpen U) {g : Fin N → V n → ℂ}
    (hg : ∀ k, DifferentiableOn ℂ (g k) U) {z : V n} (hz : z ∈ U) (hne : ∃ k, g k z ≠ 0) :
    ContDiffAt ℝ ∞ (fun y => Real.log (∑ k, ‖g k y‖ ^ 2)) z := by
  have h : ContDiffAt ℝ ∞ (fun y => ∑ k, ‖g k y‖ ^ 2) z := by
    simp only [← Complex.normSq_eq_norm_sq]
    exact ContDiffAt.sum fun k _ => HE.normSq_contDiffAt (HE.contDiffAt_of_punct hU (hg k) hz)
  exact h.log (sum_normSq_pos hne).ne'

theorem logSum_levi_nonneg {n N : ℕ} {U : Set (V n)} (hU : IsOpen U) {g : Fin N → V n → ℂ}
    (hg : ∀ k, DifferentiableOn ℂ (g k) U) {z : V n} (hz : z ∈ U) (hne : ∃ k, g k z ≠ 0)
    (ξ : Fin n → ℂ) :
    0 ≤ (leviV n (fun y => ((Real.log (∑ k, ‖g k y‖ ^ 2) : ℝ) : ℂ)) z ξ).re := by
  obtain ⟨k, hk⟩ := hne
  have hne' : (fun i => g i z) ≠ 0 := fun h => hk (congrFun h k)
  have h := leviLogNormSq n N g z ξ
    (fun i => (HE.contDiffAt_of_punct hU (hg i) hz).of_le HE.two_le_inf) hne'
  simp only [← Complex.normSq_eq_norm_sq]
  have e : (fun y => ((Real.log (∑ k, Complex.normSq (g k y)) : ℝ) : ℂ)) =
      fun y => ((Real.log (sqNorm (fun i => g i y)) : ℝ) : ℂ) := rfl
  rw [e, h, Complex.ofReal_re]
  exact div_nonneg (Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _)
    (Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}

def smoothWt (Xa : ArchInM X) (x0 : Frame X.Ψ r) (bb : ℝ) (z : V (nd X)) : ℝ :=
  phla X Xa.Fp (cpt X x0 z) + ((-1) * Real.log (densF X x0 z) + ((-bb) * rhF X x0 z +
    (1 / 2) * Real.log (∑ k, ‖Xa.w k (cpt X x0 z)‖ ^ 2)))

theorem w_diffOn (Xa : ArchInM X) (x0 : Frame X.Ψ r) (k : Fin Xa.N) :
    DifferentiableOn ℂ (fun z => Xa.w k (cpt X x0 z)) (OmF X x0) :=
  OntoB.hol_comp X x0 (Xa.w_van k).1.1.1.1

theorem s_diffOn {Xa : ArchInM X} (Fl : FlatM X Xa) (x0 : Frame X.Ψ r) (k : Fin (nd X)) :
    DifferentiableOn ℂ (fun z => Fl.s k (cpt X x0 z)) (OmF X x0) :=
  OntoB.hol_comp X x0 (Fl.s_van k).1.1.1.1

theorem logw_contDiffAt (Xa : ArchInM X) (x0 : Frame X.Ψ r) {z : V (nd X)} (hz : z ∈ OmF X x0) :
    ContDiffAt ℝ ∞ (fun y => Real.log (∑ k, ‖Xa.w k (cpt X x0 y)‖ ^ 2)) z :=
  logSum_contDiffAt (g := fun k y => Xa.w k (cpt X x0 y)) (OntoB.isOpen_OmF X x0)
    (w_diffOn Xa x0) hz (Xa.w_nz _ hz)

theorem smoothWt_contDiffOn (Xa : ArchInM X) (x0 : Frame X.Ψ r) (bb : ℝ) :
    ContDiffOn ℝ ∞ (smoothWt Xa x0 bb) (OmF X x0) := fun _ hz =>
  ((IW.phla_cpt_cdAt X x0 hz Xa.Fp).add ((contDiffAt_const.mul (OntoB.logDens_contDiffAt hz)).add
    ((contDiffAt_const.mul (OntoB.rhF_contDiffAt hz)).add
      (contDiffAt_const.mul (logw_contDiffAt Xa x0 hz))))).contDiffWithinAt

theorem smoothWt_levi (Xa : ArchInM X) (x0 : Frame X.Ψ r) (bb : ℝ) {z : V (nd X)}
    (hz : z ∈ OmF X x0) (ξ : Fin (nd X) → ℂ)
    (hm : bb * leviRh X x0 z ξ ≤ leviO X x0 (phla X Xa.Fp) z ξ - leviDens X x0 z ξ) :
    0 ≤ (leviV (nd X) (fun w => ((smoothWt Xa x0 bb w : ℝ) : ℂ)) z ξ).re := by
  have h1 := (IW.phla_cpt_cdAt X x0 hz Xa.Fp).of_le HE.two_le_inf
  have h2 := (OntoB.logDens_contDiffAt hz).of_le HE.two_le_inf
  have h3 := (OntoB.rhF_contDiffAt hz).of_le HE.two_le_inf
  have h4 := (logw_contDiffAt Xa x0 hz).of_le HE.two_le_inf
  have h5 := logSum_levi_nonneg (g := fun k y => Xa.w k (cpt X x0 y)) (OntoB.isOpen_OmF X x0)
    (w_diffOn Xa x0) hz (Xa.w_nz _ hz) ξ
  unfold smoothWt
  rw [Y.LocalMaximumSecondDerivative.leviV_ofReal_add h1 ((contDiffAt_const.mul h2).add
      ((contDiffAt_const.mul h3).add (contDiffAt_const.mul h4))),
    Y.LocalMaximumSecondDerivative.leviV_ofReal_add (contDiffAt_const.mul h2)
      ((contDiffAt_const.mul h3).add (contDiffAt_const.mul h4)),
    Y.LocalMaximumSecondDerivative.leviV_ofReal_add (contDiffAt_const.mul h3) (contDiffAt_const.mul h4),
    Y.LocalMaximumSecondDerivative.leviV_ofReal_const_mul _ h2, Y.LocalMaximumSecondDerivative.leviV_ofReal_const_mul _ h3,
    Y.LocalMaximumSecondDerivative.leviV_ofReal_const_mul _ h4]
  simp only [Complex.add_re, Complex.re_ofReal_mul]
  unfold leviRh leviO leviM leviDens at hm
  linarith

theorem inAt_iff (Xa : ArchInM X) (Fl : FlatM X Xa) (x0 : Frame X.Ψ r) (bb : ℝ) (m : ℕ)
    (k0 : Fin (nd X)) (hnull : volume {y | y ∈ OmF X x0 ∧ Fl.s k0 (cpt X x0 y) = 0} = 0)
    (F : V (nd X) → ℂ) :
    InAt X x0 (Wdiv X Xa Fl m) bb F ↔
      ∫⁻ z in OmF X x0, ENNReal.ofReal (‖F z‖ ^ 2 *
        (∑ k, ‖Fl.s k (cpt X x0 z)‖ ^ 2) ^ (-((m : ℝ) - 1 / 2)) *
        Real.exp (-smoothWt Xa x0 bb z)) < ⊤ := by
  have hU := OntoB.isOpen_OmF X x0
  have hd : AEMeasurable (fun z => ENNReal.ofReal (densF X x0 z)) (volume.restrict (OmF X x0)) :=
    (OntoB.densF_continuousOn.aemeasurable hU.measurableSet).ennreal_ofReal
  unfold InAt muF
  rw [lintegral_withDensity_eq_lintegral_mul_non_measurable₀ _ hd
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine iff_of_eq (congrArg (· < ⊤) (lintegral_congr_ae ?_))
  have hae : ∀ᵐ z ∂(volume : Measure (V (nd X))), z ∈ OmF X x0 → Fl.s k0 (cpt X x0 z) ≠ 0 := by
    rw [ae_iff]
    refine measure_mono_null (fun z hz => ?_) hnull
    simpa using hz
  filter_upwards [ae_restrict_mem hU.measurableSet, ae_restrict_of_ae hae] with z hz hz'
  have hs : ∃ k, Fl.s k (cpt X x0 z) ≠ 0 := ⟨k0, hz' hz⟩
  have hsp : 0 < ∑ k, ‖Fl.s k (cpt X x0 z)‖ ^ 2 := sum_normSq_pos hs
  have hdp := OntoB.densF_pos hz
  have hka : 0 < kaF X x0 bb z := Real.exp_pos _
  simp only [Pi.mul_apply]
  rw [Wdiv_eq_exp Xa Fl m hz hs, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul hdp.le]
  congr 1
  rw [Real.rpow_def_of_pos hsp, kaF, div_eq_mul_inv, ← Real.exp_neg]
  conv_lhs => rw [← Real.exp_log hdp]
  rw [mul_assoc, ← Real.exp_add, mul_left_comm, ← Real.exp_add, mul_assoc, ← Real.exp_add]
  congr 2
  unfold Psdiv smoothWt
  ring

end

end GlobalTheory.Up.DivUpPf

namespace GlobalTheory.Up

open DivUpPf

theorem divUp_holds {E : Type} [Field E] [NumberField E] [IsCMField E] : DivUp (E := E) := by
  intro r X Xa Fl x0 ho bb hm ⟨k0, z0, hz0, hz0'⟩ F hF hI
  have hU := OntoB.isOpen_OmF X x0
  have hc := OmFConnStatement_holds r X x0 ho
  have hnull := HE.zeros_null hU (s_diffOn Fl x0 k0)
    (HE.hgn_of hU hc (s_diffOn Fl x0 k0) hz0 (fun h => hz0' h.self_of_nhds))
  obtain ⟨S, hS, -⟩ := exhaustG_holds r X x0 ho _ (s_diffOn Fl x0 k0)
  have hT : nd X ≤ Xa.T := by
    have h2 := Xa.n_ge
    have hT := Xa.T_ge
    nlinarith
  have hcast : ((Xa.T - nd X : ℕ) : ℝ) + (nd X : ℝ) = (Xa.T : ℝ) := by
    rw [Nat.cast_sub hT]; ring
  rw [inAt_iff Xa Fl x0 bb _ k0 hnull, ← hcast] at hI
  obtain ⟨H, hH, hFH⟩ := SkodaIter.iterated_division (nd X) Xa.n_ge (OmF X x0) hU hc
    (fun k z => Fl.s k (cpt X x0 z)) k0 (s_diffOn Fl x0) ⟨z0, hz0, hz0'⟩ ⟨S, hS⟩
    (smoothWt Xa x0 bb) (smoothWt_contDiffOn Xa x0 bb)
    (fun z hz ξ => smoothWt_levi Xa x0 bb hz ξ (hm z hz ξ)) (Xa.T - nd X) F hF hI
  exact ⟨H, fun α => ⟨(hH α).1, (inAt_iff Xa Fl x0 bb _ k0 hnull _).2 (hH α).2⟩, hFH⟩

end GlobalTheory.Up
