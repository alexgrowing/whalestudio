import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExhaustFStatementPf
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.HoloSmooth
import ReciprocityTheory.L2DbarEstimates.LeviForms.LogNormSq

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open NumberField Topology Filter ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.FD
open scoped ContDiff

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace ExG

theorem two_le_inf : (2 : WithTop ℕ∞) ≤ ∞ := by
  first
    | exact WithTop.coe_le_coe.mpr le_top
    | exact (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤) : ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞))
    | decide
    | simp
    | norm_num

variable {r : ℕ} (X : Data E r)

private lemma isOpen_omF (x0 : Frame X.Ψ r) : IsOpen (OmF X x0) := by
  first
  | exact ExF.isOpen_OmF X x0
  | exact isOpen_OmF X x0
  | exact ExF.isOpen_Om X x0
  | exact (X.isOpen_dom).preimage (continuous_cpt X x0)
  | exact X.isOpen_dom.preimage (by unfold cpt; fun_prop)
  | exact X.dom_open.preimage (by unfold cpt; fun_prop)
  | exact X.hdom.preimage (by unfold cpt; fun_prop)

theorem isOpen_Om (x0 : Frame X.Ψ r) (g1 : V (nd X) → ℂ) (hg : DifferentiableOn ℂ g1 (OmF X x0)) :
    IsOpen {z | z ∈ OmF X x0 ∧ g1 z ≠ 0} := by
  have hO := isOpen_omF X x0
  exact hg.continuousOn.isOpen_inter_preimage hO isOpen_ne

theorem g_cd (x0 : Frame X.Ψ r) (g1 : V (nd X) → ℂ) (hg : DifferentiableOn ℂ g1 (OmF X x0))
    {z : V (nd X)} (hz : z ∈ OmF X x0) : ContDiffAt ℂ ∞ g1 z := by
  exact (contDiffOn_of_differentiableOn (nd X) g1 (OmF X x0) (isOpen_omF X x0) hg).contDiffAt
    ((isOpen_omF X x0).mem_nhds hz)

theorem inv_cd (x0 : Frame X.Ψ r) (g1 : V (nd X) → ℂ) (hg : DifferentiableOn ℂ g1 (OmF X x0))
    {z : V (nd X)} (hz : z ∈ OmF X x0) (hne : g1 z ≠ 0) :
    ContDiffAt ℝ ∞ (fun y => (‖g1 y‖ ^ 2)⁻¹) z := by
  have h1 : ContDiffAt ℝ ∞ g1 z := (g_cd X x0 g1 hg hz).restrict_scalars ℝ
  have h2 : ContDiffAt ℝ ∞ (fun y => ‖g1 y‖ ^ 2) z := (contDiff_norm_sq ℝ).contDiffAt.comp z h1
  exact h2.inv (pow_ne_zero 2 (norm_ne_zero_iff.mpr hne))

theorem levi_inv_nonneg (x0 : Frame X.Ψ r) (g1 : V (nd X) → ℂ) (hg : DifferentiableOn ℂ g1 (OmF X x0))
    {z : V (nd X)} (hz : z ∈ OmF X x0) (hne : g1 z ≠ 0) (ξ : Fin (nd X) → ℂ) :
    0 ≤ (leviV (nd X) (fun y => (((‖g1 y‖ ^ 2)⁻¹ : ℝ) : ℂ)) z ξ).re := by
  have hfun : (fun y => (((‖g1 y‖ ^ 2)⁻¹ : ℝ) : ℂ)) = fun y => ((Complex.normSq ((g1 y)⁻¹) : ℝ) : ℂ) := by
    funext y
    rw [Complex.normSq_inv, Complex.normSq_eq_norm_sq]
  have hcd : ContDiffAt ℂ 2 (fun y => (g1 y)⁻¹) z := ((g_cd X x0 g1 hg hz).of_le two_le_inf).inv hne
  rw [hfun, leviV_normSq_comp hcd ξ, Complex.ofReal_re]
  exact Complex.normSq_nonneg _

theorem isCompact_sub (x0 : Frame X.Ψ r) (ho : IsOrth X x0) (g1 : V (nd X) → ℂ)
    (hg : DifferentiableOn ℂ g1 (OmF X x0)) (a : ℝ) :
    IsCompact {z : V (nd X) | (z ∈ OmF X x0 ∧ g1 z ≠ 0) ∧ eF X x0 z + (‖g1 z‖ ^ 2)⁻¹ ≤ a} := by
  have hK := ExF.isCompact_subF X x0 ho a
  have hcont : ContinuousOn (fun z => ‖g1 z‖ ^ 2 * (a - eF X x0 z)) {z | z ∈ OmF X x0 ∧ eF X x0 z ≤ a} :=
    ((hg.continuousOn.norm.pow 2).mul (continuousOn_const.sub (fun z hz =>
      (ExF.eF_contDiffAt X x0 ho hz).continuousAt.continuousWithinAt))).mono (fun z hz => hz.1)
  have hcl := hcont.preimage_isClosed_of_isClosed hK.isClosed (isClosed_Ici (a := (1 : ℝ)))
  have hset : {z : V (nd X) | (z ∈ OmF X x0 ∧ g1 z ≠ 0) ∧ eF X x0 z + (‖g1 z‖ ^ 2)⁻¹ ≤ a} =
      {z | z ∈ OmF X x0 ∧ eF X x0 z ≤ a} ∩ (fun z => ‖g1 z‖ ^ 2 * (a - eF X x0 z)) ⁻¹' Set.Ici 1 := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_Ici]
    constructor
    · rintro ⟨⟨hzO, hz0⟩, hle⟩
      have hpos : 0 < ‖g1 z‖ ^ 2 := pow_pos (norm_pos_iff.mpr hz0) 2
      have hinv : 0 ≤ (‖g1 z‖ ^ 2)⁻¹ := inv_nonneg.mpr hpos.le
      refine ⟨⟨hzO, by linarith⟩, ?_⟩
      have hle' : (‖g1 z‖ ^ 2)⁻¹ ≤ a - eF X x0 z := by linarith
      calc (1 : ℝ) = ‖g1 z‖ ^ 2 * (‖g1 z‖ ^ 2)⁻¹ := (mul_inv_cancel₀ hpos.ne').symm
        _ ≤ ‖g1 z‖ ^ 2 * (a - eF X x0 z) := mul_le_mul_of_nonneg_left hle' hpos.le
    · rintro ⟨⟨hzO, _⟩, h1⟩
      have hz0 : g1 z ≠ 0 := by
        intro h0
        rw [h0, norm_zero] at h1
        norm_num at h1
      have hpos : 0 < ‖g1 z‖ ^ 2 := pow_pos (norm_pos_iff.mpr hz0) 2
      refine ⟨⟨hzO, hz0⟩, ?_⟩
      have hle' : (‖g1 z‖ ^ 2)⁻¹ ≤ a - eF X x0 z := by
        calc (‖g1 z‖ ^ 2)⁻¹ = (‖g1 z‖ ^ 2)⁻¹ * 1 := (mul_one _).symm
          _ ≤ (‖g1 z‖ ^ 2)⁻¹ * (‖g1 z‖ ^ 2 * (a - eF X x0 z)) :=
            mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hpos.le)
          _ = a - eF X x0 z := by field_simp
      linarith
  rw [hset]
  exact hK.of_isClosed_subset hcl Set.inter_subset_left

end ExG

private theorem leviV_ofReal_add_of_contDiffAt_two {n : ℕ} {F G : V n → ℝ} {y : V n} (hF : ContDiffAt ℝ 2 F y)
    (hG : ContDiffAt ℝ 2 G y) (ξ : Fin n → ℂ) :
    leviV n (fun v => ((F v + G v : ℝ) : ℂ)) y ξ =
      leviV n (fun v => (F v : ℂ)) y ξ + leviV n (fun v => (G v : ℂ)) y ξ := by
  have h := leviV_ofReal_sum (u := ![F, G]) (x := y) (fun i => by fin_cases i <;> simpa) ξ
  simpa [Fin.sum_univ_two] using h

theorem exhaustG_holds : ExhaustGStatement (E := E) := by
  intro r X x0 ho g1 hg
  have hU : IsOpen {z | z ∈ OmF X x0 ∧ g1 z ≠ 0} := ExG.isOpen_Om X x0 g1 hg
  have hLH : IsLocalHomeomorph (Subtype.val : {z | z ∈ OmF X x0 ∧ g1 z ≠ 0} → V (nd X)) :=
    hU.isOpenEmbedding_subtypeVal.isLocalHomeomorph
  have hf : ∀ z ∈ {z | z ∈ OmF X x0 ∧ g1 z ≠ 0},
      ContDiffAt ℝ ∞ (fun z => eF X x0 z + (‖g1 z‖ ^ 2)⁻¹) z := fun z hz =>
    (ExF.eF_contDiffAt X x0 ho hz.1).add (ExG.inv_cd X x0 g1 hg hz.1 hz.2)
  refine ⟨{ z := Subtype.val
            isLocalHomeomorph := hLH
            e := fun y => eF X x0 y.1 + (‖g1 y.1‖ ^ 2)⁻¹
            smooth_e := ?_
            levi_e := ?_
            isCompact_le := ?_ }, rfl, rfl⟩
  · intro ch hch
    have hts : ∀ y ∈ ch.target, ((ch.symm y : {z | z ∈ OmF X x0 ∧ g1 z ≠ 0}) : V (nd X)) = y := fun y hy => by
      rw [hch (ch.map_target hy)]
      exact ch.right_inv hy
    have hsub : ch.target ⊆ {z | z ∈ OmF X x0 ∧ g1 z ≠ 0} := fun y hy => by
      rw [← hts y hy]
      exact (ch.symm y).2
    have hcd : ContDiffOn ℝ ∞ (fun y => ((eF X x0 y + (‖g1 y‖ ^ 2)⁻¹ : ℝ) : ℂ)) ch.target :=
      fun y hy => (Complex.ofRealCLM.contDiff.contDiffAt.comp y (hf y (hsub hy))).contDiffWithinAt
    refine hcd.congr (fun y hy => ?_)
    simp only [Function.comp_apply, hts y hy]
  · intro x ξ
    obtain ⟨ch, hx, hch⟩ := hLH x
    have hchart : IsChart (nd X) Subtype.val ch := fun y _ => congrFun hch y
    rw [levi_eq_leviV (nd X) Subtype.val ch hchart _ x hx ξ]
    have htg : ch.target ∈ 𝓝 (x : V (nd X)) := by
      have h0 := ch.open_target.mem_nhds (ch.map_source hx)
      rwa [← congrFun hch x] at h0
    have hgerm : (fun y => (((fun y : {z | z ∈ OmF X x0 ∧ g1 z ≠ 0} => eF X x0 y.1 + (‖g1 y.1‖ ^ 2)⁻¹)
        (ch.symm y) : ℝ) : ℂ)) =ᶠ[𝓝 (x : V (nd X))]
        (fun y => ((eF X x0 y + (‖g1 y‖ ^ 2)⁻¹ : ℝ) : ℂ)) := by
      filter_upwards [htg] with y hy
      have hy' : ((ch.symm y : {z | z ∈ OmF X x0 ∧ g1 z ≠ 0}) : V (nd X)) = y := by
        rw [congrFun hch (ch.symm y)]
        exact ch.right_inv hy
      simp only [hy']
    rw [leviV_congr hgerm ξ]
    have hxO : (x : V (nd X)) ∈ OmF X x0 := x.2.1
    have h2 : (2 : WithTop ℕ∞) ≤ ∞ := ExG.two_le_inf
    have hE : ContDiffAt ℝ 2 (eF X x0) x := (ExF.eF_contDiffAt X x0 ho hxO).of_le h2
    have hI : ContDiffAt ℝ 2 (fun y => (‖g1 y‖ ^ 2)⁻¹) x :=
      (ExG.inv_cd X x0 g1 hg hxO x.2.2).of_le h2
    have hR : ContDiffAt ℝ 2 (rhF X x0) x := (ExF.rhF_contDiffAt X x0 ho hxO).of_le h2
    have hT : ContDiffAt ℝ 2 (fun z : V (nd X) => Real.log (1 + ‖z‖ ^ 2)) x := ExF.T_cd.contDiffAt.of_le h2
    rw [leviV_ofReal_add_of_contDiffAt_two hE hI ξ]
    have hEsplit : leviV (nd X) (fun v => (eF X x0 v : ℂ)) x ξ =
        leviV (nd X) (fun v => (rhF X x0 v : ℂ)) x ξ +
          leviV (nd X) (fun v => (Real.log (1 + ‖v‖ ^ 2) : ℂ)) x ξ :=
      leviV_ofReal_add_of_contDiffAt_two hR hT ξ
    rw [hEsplit, Complex.add_re, Complex.add_re]
    have h1 := ExF.levi_rhF_nonneg X x0 ho hxO ξ
    have h3 := ExF.leviT_nonneg (x : V (nd X)) ξ
    have h4 := ExG.levi_inv_nonneg X x0 g1 hg hxO x.2.2 ξ
    linarith
  · intro a
    rw [Subtype.isCompact_iff]
    convert ExG.isCompact_sub X x0 ho g1 hg a using 1
    ext z
    constructor
    · rintro ⟨⟨w, hw⟩, hle, rfl⟩
      exact ⟨hw, hle⟩
    · rintro ⟨hw, hle⟩
      exact ⟨⟨z, hw⟩, hle, rfl⟩

end ReciprocityTheory.ChartRestriction.G.AR.Up
