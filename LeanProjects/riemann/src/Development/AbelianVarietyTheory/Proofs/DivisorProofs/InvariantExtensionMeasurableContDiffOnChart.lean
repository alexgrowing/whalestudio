import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.KaUnfoldPfC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfM
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.DifferentiableChart
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FirstMinimumInvariantContinuousPosOnFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormFactorAndDensityNearOneInFlagChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramChartSubFormEntryLe
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LUStatementPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfK
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfS
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.KaUnfoldPfA
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.PeakWeightSmooth

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem lact_inv_lact (X : Data E r) (γ : GL (Fin r) E) (y : Frame X.Ψ r) : lact γ⁻¹ (lact γ y) = y := by
  rw [KU.lact_lact X, inv_mul_cancel, KU.lact_one X]

theorem lact_lact_inv (X : Data E r) (γ : GL (Fin r) E) (y : Frame X.Ψ r) : lact γ (lact γ⁻¹ y) = y := by
  rw [KU.lact_lact X, mul_inv_cancel, KU.lact_one X]

theorem local_form (X : Data E r) (x : Frame X.Ψ r) (hx : IsOrth X x) (ρ R : ℝ) (η : V (nd X) → ℝ)
    (ψ : Frame X.Ψ r → ℝ) (hρR : ρ < R) (hR : ∀ z : V (nd X), ‖z‖ ≤ R → z ∈ OmF X x)
    (hψ : ∀ γ ∈ X.Γ, ∀ b ∈ Bor X.Ψ r, ∀ z : V (nd X), ‖z‖ ≤ R → ψ (lact γ (rmul (cpt X x z) b)) = η z)
    (h0 : ∀ y, (¬ ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, ∃ z : V (nd X), ‖z‖ ≤ ρ ∧ y = lact γ (rmul (cpt X x z) b)) →
      ψ y = 0)
    (hloc : ∀ y ∈ X.dom, (¬ ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, ∃ z : V (nd X), ‖z‖ ≤ ρ ∧
      y = lact γ (rmul (cpt X x z) b)) → ∀ᶠ y' in 𝓝 y, ¬ ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, ∃ z : V (nd X),
        ‖z‖ ≤ ρ ∧ y' = lact γ (rmul (cpt X x z) b))
    {y : Frame X.Ψ r} (hy : y ∈ X.dom) :
    (∀ᶠ y' in 𝓝 y, ψ y' = 0) ∨
    ∃ (γ : GL (Fin r) E) (zOf : Frame X.Ψ r → V (nd X)) (U : Set (Frame X.Ψ r)),
      IsOpen U ∧ lact γ⁻¹ y ∈ U ∧ DifferentiableOn ℂ zOf U ∧
      ∀ᶠ y' in 𝓝 y, ψ y' = η (zOf (lact γ⁻¹ y')) := by
  by_cases hS : ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, ∃ z : V (nd X), ‖z‖ ≤ ρ ∧ y = lact γ (rmul (cpt X x z) b)
  · right
    obtain ⟨γ, hγ, b, hb, z, hz, rfl⟩ := hS
    obtain ⟨Δ, zOf, bOf, hΔ, -, hzd, -, hsplit, hinv⟩ := lu_holds r X x hx
    have hUo : IsOpen {w | w ∈ X.dom ∧ Δ w ≠ 0} :=
      (IW.isOpen_dom X).inter (isOpen_ne_fun hΔ.continuous continuous_const)
    have hzO : z ∈ OmF X x := hR z (hz.trans hρR.le)
    have hmem : lact γ⁻¹ (lact γ (rmul (cpt X x z) b)) ∈ {w | w ∈ X.dom ∧ Δ w ≠ 0} := by
      rw [lact_inv_lact]
      exact ⟨OntoS.dom_rmul X hzO hb, (hinv z hzO b hb).1⟩
    refine ⟨γ, zOf, _, hUo, hmem, hzd, ?_⟩
    have hcont : ContinuousAt (fun y' => lact γ⁻¹ y') (lact γ (rmul (cpt X x z) b)) :=
      (KU.cont_lact X γ⁻¹).continuousAt
    have hU' : ∀ᶠ y' in 𝓝 (lact γ (rmul (cpt X x z) b)), lact γ⁻¹ y' ∈ {w | w ∈ X.dom ∧ Δ w ≠ 0} :=
      hcont.preimage_mem_nhds (hUo.mem_nhds hmem)
    have hzc : ContinuousAt (fun y' => zOf (lact γ⁻¹ y')) (lact γ (rmul (cpt X x z) b)) :=
      ContinuousAt.comp (f := fun y' => lact γ⁻¹ y')
        ((hzd.differentiableAt (hUo.mem_nhds hmem)).continuousAt) hcont
    have hval : zOf (lact γ⁻¹ (lact γ (rmul (cpt X x z) b))) = z := by
      rw [lact_inv_lact]; exact (hinv z hzO b hb).2.1
    have h2 : ‖zOf (lact γ⁻¹ (lact γ (rmul (cpt X x z) b)))‖ < R := by
      rw [hval]; exact lt_of_le_of_lt hz hρR
    have hnear : ∀ᶠ y' in 𝓝 (lact γ (rmul (cpt X x z) b)), ‖zOf (lact γ⁻¹ y')‖ < R :=
      hzc.norm.eventually_lt continuousAt_const h2
    filter_upwards [hU', hnear] with y' hy'U hy'n
    obtain ⟨hy'd, hy'Δ⟩ := hy'U
    obtain ⟨-, hbO, heq⟩ := hsplit _ hy'd hy'Δ
    have hy' : y' = lact γ (rmul (cpt X x (zOf (lact γ⁻¹ y'))) (bOf (lact γ⁻¹ y'))) := by
      rw [← heq, lact_lact_inv]
    conv_lhs => rw [hy']
    exact hψ γ hγ _ hbO _ hy'n.le
  · left
    filter_upwards [hloc y hy hS] with y' hy'
    exact h0 y' hy'

end GlobalTheory.PeakWeightSmooth

namespace GlobalTheory.PeakWeightSmooth

theorem measurable_and_contDiffOn : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x : Frame X.Ψ r) (ρ R : ℝ) (η : V (nd X) → ℝ) (ψ : Frame X.Ψ r → ℝ), IsOrth X x → ρ < R → (∀ z : V (nd X), ‖z‖ ≤ R → z ∈ OmF X x) → ContDiff ℝ ∞ η → (∀ γ ∈ X.Γ, ∀ b ∈ Bor X.Ψ r, ∀ z : V (nd X), ‖z‖ ≤ R → ψ (lact γ (rmul (cpt X x z) b)) = η z) → (∀ y, (¬ ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, ∃ z : V (nd X), ‖z‖ ≤ ρ ∧ y = lact γ (rmul (cpt X x z) b)) → ψ y = 0) → (∀ y ∈ X.dom, (¬ ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, ∃ z : V (nd X), ‖z‖ ≤ ρ ∧ y = lact γ (rmul (cpt X x z) b)) → ∀ᶠ y' in 𝓝 y, ¬ ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, ∃ z : V (nd X), ‖z‖ ≤ ρ ∧ y' = lact γ (rmul (cpt X x z) b)) → Measurable ψ ∧ ContDiffOn ℝ ∞ (fun w => ψ (cpt X x w)) (OmF X x) := by
  intro E _ _ _ r X x ρ R η ψ hx hρR hR hη hψ h0 hloc
  classical
  have hS_dom : ∀ y, (∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, ∃ z : V (nd X), ‖z‖ ≤ ρ ∧
      y = lact γ (rmul (cpt X x z) b)) → y ∈ X.dom := by
    rintro y ⟨γ, hγ, b, hb, z, hz, rfl⟩
    exact KU.lact_dom X hγ (OntoS.dom_rmul X (hR z (hz.trans hρR.le)) hb)
  have hcont : ∀ y ∈ X.dom, ContinuousAt ψ y := by
    intro y hy
    rcases local_form X x hx ρ R η ψ hρR hR hψ h0 hloc hy with h | ⟨γ, zOf, U, hUo, hyU, hzd, hev⟩
    · exact (continuousAt_const (y := (0 : ℝ))).congr (h.mono fun _ h => h.symm)
    · have : ContinuousAt (fun y' => η (zOf (lact γ⁻¹ y'))) y :=
        hη.continuous.continuousAt.comp (((hzd.differentiableAt (hUo.mem_nhds hyU)).continuousAt).comp
          (KU.cont_lact X γ⁻¹).continuousAt)
      exact this.congr (hev.mono fun _ h => h.symm)
  have hzero : ∀ y, y ∉ X.dom → ψ y = 0 := fun y hy => h0 y (fun h => hy (hS_dom y h))
  constructor
  · have heq : ψ = X.dom.piecewise ψ (fun _ => 0) := by
      funext y
      by_cases hy : y ∈ X.dom
      · simp [Set.piecewise, hy]
      · simp [Set.piecewise, hy, hzero y hy]
    rw [heq]
    exact ContinuousOn.measurable_piecewise (fun y hy => (hcont y hy).continuousWithinAt)
      continuousOn_const (IW.isOpen_dom X).measurableSet
  · intro w hw
    refine ContDiffAt.contDiffWithinAt ?_
    have hc : ContinuousAt (cpt X x) w := (IW.cpt_diff X x).continuous.continuousAt
    rcases local_form X x hx ρ R η ψ hρR hR hψ h0 hloc (y := cpt X x w) hw with
      h | ⟨γ, zOf, U, hUo, hyU, hzd, hev⟩
    · have h' : ∀ᶠ w' in 𝓝 w, ψ (cpt X x w') = 0 := hc.eventually h
      exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq h'
    · have hg : Differentiable ℂ (fun w' => lact γ⁻¹ (cpt X x w')) := by
        have e : (fun w' => lact γ⁻¹ (cpt X x w')) = cpt X (lact γ⁻¹ x) := by
          funext w'; rw [KU.cpt_lact]
        rw [e]; exact IW.cpt_diff X _
      have hN : (fun w' => lact γ⁻¹ (cpt X x w')) ⁻¹' U ∈ 𝓝 w :=
        hg.continuous.continuousAt.preimage_mem_nhds (hUo.mem_nhds hyU)
      have hΦd : DifferentiableOn ℂ (fun w' => zOf (lact γ⁻¹ (cpt X x w')))
          ((fun w' => lact γ⁻¹ (cpt X x w')) ⁻¹' U) :=
        hzd.comp hg.differentiableOn (fun _ h => h)
      have hΦ : ContDiffAt ℂ ∞ (fun w' => zOf (lact γ⁻¹ (cpt X x w'))) w :=
        GlobalTheory.SCV.contDiffAt_of_differentiableOn hΦd hN _
      have hev' : ∀ᶠ w' in 𝓝 w, ψ (cpt X x w') = η (zOf (lact γ⁻¹ (cpt X x w'))) := hc.eventually hev
      exact ((hη.contDiffAt).comp w (hΦ.restrict_scalars ℝ)).congr_of_eventuallyEq hev'

end GlobalTheory.PeakWeightSmooth
