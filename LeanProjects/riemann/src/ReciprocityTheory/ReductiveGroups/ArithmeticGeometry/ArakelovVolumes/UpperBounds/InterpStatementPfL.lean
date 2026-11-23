import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.PnormInvStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfK
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExtFStatementPfB

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.IW

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def Wpsi {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) (ψ : Frame X.Ψ r → ℝ) (x : Frame X.Ψ r) : ℝ≥0∞ := by
  classical
  exact if x ∈ X.dom then ENNReal.ofReal (Real.exp (-(phla X la x + ψ x))) else 0

theorem metricW_of (hR : NfacRmulStatement (E := E)) (hLa : NfacLactStatement (E := E))
    (hO : OrthoStatement (E := E)) (hLU : LUStatement (E := E)) {r : ℕ} (X : Data E r) (la : Wt X.Ψ r)
    (ψ : Frame X.Ψ r → ℝ) (hψ : IsInvFn X ψ)
    (hψs : ∀ x0, IsOrth X x0 → ContDiffOn ℝ ∞ (fun z => ψ (cpt X x0 z)) (OmF X x0))
    (hψb : ∃ C : ℝ, ∀ x ∈ X.dom, ψ x ≤ C) :
    IsMetricW X la (Wpsi X la ψ) ∧ WLower X la (Wpsi X la ψ) := by
  classical

  have hlact1 : ∀ y : Frame X.Ψ r, lact (1 : GL (Fin r) E) y = y := by
    intro y; funext τ a c
    simp [lact, mat]
  have hψr : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, ψ (rmul x b) = ψ x := by
    intro x hx b hb
    have h := hψ 1 X.Γ.one_mem x hx b hb
    rwa [hlact1] at h
  have hψl : ∀ γ ∈ X.Γ, ∀ x ∈ X.dom, ψ (lact γ x) = ψ x := by
    intro γ hγ x hx
    have h := hψ γ hγ x hx (ExtFPf.oneF X) (ExtFPf.oneF_mem (X := X))
    rwa [ExtFPf.rmul_oneF] at h

  have hnpos : ∀ x ∈ X.dom, 0 < X.nfac la x := by
    intro x hx
    unfold ReciprocityTheory.ChartRestriction.G.FD.Data.nfac
    refine Finset.prod_pos fun τ _ => Finset.prod_pos fun i _ => Real.rpow_pos_of_pos ?_ _
    exact norm_pos_iff.mpr (div_ne_zero (ReciprocityTheory.ChartRestriction.G.FD.FlowCoefficientBounds.dmin_ne (X := X) hx τ _)
      (ReciprocityTheory.ChartRestriction.G.FD.FlowCoefficientBounds.dmin_ne (X := X) hx τ _))
  have hopen : IsOpen X.dom := ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientDomain.isOpen_dom (X := X)

  have hphr : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r,
      0 < ‖bchar la b‖ ∧ phla X la (rmul x b) = phla X la x + 2 * Real.log ‖bchar la b‖ := by
    intro x hx b hb
    have hn := hnpos x hx
    have h1 := hnpos (rmul x b) (OntoS.dom_rmul (X := X) hx hb)
    rw [hR r X la x hx b hb] at h1
    have hinv : 0 < ‖bchar la b‖⁻¹ := by
      by_contra hc
      push_neg at hc
      nlinarith
    refine ⟨inv_pos.mp hinv, ?_⟩
    unfold phla
    rw [hR r X la x hx b hb, Real.log_mul hinv.ne' hn.ne', Real.log_inv]
    ring
  have hphl : ∀ γ ∈ X.Γ, ∀ x ∈ X.dom, phla X la (lact γ x) = phla X la x := by
    intro γ hγ x hx
    unfold phla
    rw [hLa r X la γ hγ x hx]

  have hψc : ContinuousOn ψ X.dom := by
    intro x hx
    obtain ⟨x1, ho, b, hb, hxe⟩ := hO r X x hx
    obtain ⟨Δ, zOf, bOf, hΔ, -, hz, -, hdec, hcomp⟩ := hLU r X x1 ho
    have hn0 : nmat X (0 : V (nd X)) = ExtFPf.oneF X := by
      funext τ a c
      simp only [nmat, ExtFPf.oneF, Matrix.one_apply]
      split_ifs <;> first | rfl | (exfalso; subst_vars; exact lt_irrefl _ ‹_ < _›) | simp_all
    have hc0 : cpt X x1 0 = x1 := by
      unfold cpt
      rw [hn0, ExtFPf.rmul_oneF]
    have hΔx : Δ x ≠ 0 := by
      have h := (hcomp 0 (zero_mem_OmF (X := X) x1 ho) b hb).1
      rwa [hc0, ← hxe] at h
    have hUo : IsOpen {y | y ∈ X.dom ∧ Δ y ≠ 0} :=
      hopen.inter (isOpen_ne_fun hΔ.continuous continuous_const)
    have hmap : Set.MapsTo zOf {y | y ∈ X.dom ∧ Δ y ≠ 0} (OmF X x1) :=
      fun y hy => (hdec y hy.1 hy.2).1
    have hcomp' : ContinuousOn ((fun z => ψ (cpt X x1 z)) ∘ zOf) {y | y ∈ X.dom ∧ Δ y ≠ 0} :=
      (hψs x1 ho).continuousOn.comp hz.continuousOn hmap
    have heq : Set.EqOn ψ ((fun z => ψ (cpt X x1 z)) ∘ zOf) {y | y ∈ X.dom ∧ Δ y ≠ 0} := by
      intro y hy
      obtain ⟨hzy, hby, hye⟩ := hdec y hy.1 hy.2
      have hmem : cpt X x1 (zOf y) ∈ X.dom := hzy
      show ψ y = ψ (cpt X x1 (zOf y))
      exact (congrArg ψ hye).trans (hψr _ hmem _ hby)
    exact ((hcomp'.congr heq).continuousAt (hUo.mem_nhds ⟨hx, hΔx⟩)).continuousWithinAt
  have hphc : ContinuousOn (phla X la) X.dom := by
    show ContinuousOn (fun x => -2 * Real.log (X.nfac la x)) X.dom
    exact continuousOn_const.mul
      ((ExtFPf.nfac_contOn (X := X) la).log fun x hx => (hnpos x hx).ne')
  have hcont : ContinuousOn (fun x => ENNReal.ofReal (Real.exp (-(phla X la x + ψ x)))) X.dom :=
    ENNReal.continuous_ofReal.comp_continuousOn
      (Real.continuous_exp.comp_continuousOn (hphc.add hψc).neg)
  have hW : ∀ x ∈ X.dom, Wpsi X la ψ x = ENNReal.ofReal (Real.exp (-(phla X la x + ψ x))) := by
    intro x hx
    simp [Wpsi, hx]
  have hWeq : Wpsi X la ψ = X.dom.piecewise
      (fun x => ENNReal.ofReal (Real.exp (-(phla X la x + ψ x)))) (fun _ => 0) := by
    funext x
    by_cases hx : x ∈ X.dom <;> simp [Wpsi, Set.piecewise, hx]
  unfold IsMetricW WLower
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · rw [hWeq]
    exact ContinuousOn.measurable_piecewise hcont continuousOn_const hopen.measurableSet
  · intro x hx b hb
    obtain ⟨hB, hph⟩ := hphr x hx b hb
    rw [hW _ (OntoS.dom_rmul (X := X) hx hb), hW x hx, hph, hψr x hx b hb,
      ← ENNReal.ofReal_div_of_pos (pow_pos hB 2)]
    congr 1
    rw [show -(phla X la x + 2 * Real.log ‖bchar la b‖ + ψ x)
        = -(phla X la x + ψ x) - Real.log (‖bchar la b‖ ^ 2) by rw [Real.log_pow]; push_cast; ring,
      Real.exp_sub, Real.exp_log (pow_pos hB 2)]
  · intro γ hγ x hx
    rw [hW _ (OntoS.dom_lact (X := X) hγ hx), hW x hx, hphl γ hγ x hx, hψl γ hγ x hx]
  · obtain ⟨C, hC⟩ := hψb
    refine ⟨Real.exp (-C), Real.exp_pos _, fun x hx => ?_⟩
    rw [hW x hx, ← Real.exp_add]
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by linarith [hC x hx]))

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.IW
