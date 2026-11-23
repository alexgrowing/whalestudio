import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfC

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

namespace UpDivA

open ReciprocityTheory.L2DbarEstimates MeasureTheory Topology ReciprocityTheory.ChartRestriction.G.AR.Up.HE
open scoped ContDiff ENNReal

variable {n : ℕ} {U : Set (V n)}

theorem holo_val {f : V n → ℂ} (hf : DifferentiableOn ℂ f U) :
    Holo n (Subtype.val : U → V n) (fun x => f x.1) := by
  intro e he
  have hsub : e.target ⊆ U := by
    intro y hy
    rw [← chart_z_symm n Subtype.val e he y hy]
    exact (e.symm y).2
  refine (hf.mono hsub).congr (fun y hy => ?_)
  show f (e.symm y).1 = f y
  rw [chart_z_symm n Subtype.val e he y hy]

theorem skoda_open (hU : IsOpen U) (S : EtaleStein n U) (hz : S.z = Subtype.val) {p : ℕ}
    (g : Fin p → V n → ℂ) (ph0 : V n → ℝ) (t : ℝ) (f : V n → ℂ) (hp : 2 ≤ p)
    (hg : ∀ i, DifferentiableOn ℂ (g i) U) (hnz : ∀ y ∈ U, ∃ i, g i y ≠ 0)
    (hph : ContDiffOn ℝ ∞ ph0 U)
    (hl : ∀ y ∈ U, ∀ ξ : Fin n → ℂ, 0 ≤ (leviV n (fun w => (ph0 w : ℂ)) y ξ).re)
    (ht : (p : ℝ) - 1 < t) (hf : DifferentiableOn ℂ f U)
    (hI : ∫⁻ y in U, ENNReal.ofReal (‖f y‖ ^ 2 * (∑ i, ‖g i y‖ ^ 2) ^ (-(t + 1)) * Real.exp (-ph0 y)) < ⊤) :
    ∃ hh : Fin p → V n → ℂ, (∀ i, DifferentiableOn ℂ (hh i) U) ∧
      (∀ y ∈ U, f y = ∑ i, g i y * hh i y) ∧
      ∫⁻ y in U, ENNReal.ofReal ((∑ i, ‖hh i y‖ ^ 2) * (∑ i, ‖g i y‖ ^ 2) ^ (-t) * Real.exp (-ph0 y)) ≤
        ENNReal.ofReal (t / (t - ((p : ℝ) - 1))) *
          ∫⁻ y in U, ENNReal.ofReal (‖f y‖ ^ 2 * (∑ i, ‖g i y‖ ^ 2) ^ (-(t + 1)) * Real.exp (-ph0 y)) := by
  classical
  have hzl : IsLocalHomeomorph (Subtype.val : U → V n) := hz ▸ S.isLocalHomeomorph
  have hemb : MeasurableEmbedding (Subtype.val : U → V n) := MeasurableEmbedding.subtype_coe hU.measurableSet
  have hvol : vol n (Subtype.val : U → V n) = (volume : Measure (V n)).comap Subtype.val := by
    ext A hA
    rw [vol_image n Subtype.val hzl Set.univ isOpen_univ Subtype.val_injective.injOn A hA (Set.subset_univ _),
      hemb.comap_apply]
  have htgt : ∀ (e : OpenPartialHomeomorph U (V n)), IsChart n Subtype.val e → e.target ⊆ U := by
    intro e he y hy
    rw [← chart_z_symm n Subtype.val e he y hy]
    exact (e.symm y).2
  have hleviC : ∀ (g₁ g₂ : V n → ℂ) (y : V n), g₁ =ᶠ[𝓝 y] g₂ → ∀ ξ, leviV n g₁ y ξ = leviV n g₂ y ξ := by
    intro g₁ g₂ y h ξ
    unfold leviV
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    rw [wd_congr (h := h.eventually_nhds.mono fun y' h' => wdb_congr (h := h'))]
  have hsm : SmoothR n S.z (fun x : U => ph0 x.1) := by
    rw [hz]
    intro e he
    have hc : ContDiffOn ℝ ∞ (fun y => ((ph0 y : ℝ) : ℂ)) U := Complex.ofRealCLM.contDiff.comp_contDiffOn hph
    refine (hc.mono (htgt e he)).congr (fun y hy => ?_)
    show ((ph0 (e.symm y).1 : ℝ) : ℂ) = ((ph0 y : ℝ) : ℂ)
    rw [chart_z_symm n Subtype.val e he y hy]
  have hlev : LeviNonneg n S.z (fun x : U => ph0 x.1) := by
    rw [hz]
    intro x ξ
    obtain ⟨e, he, hxe⟩ := exists_chart n Subtype.val hzl x
    rw [levi_eq_leviV n Subtype.val e he _ x hxe ξ]
    have heq : (fun y => ((ph0 (e.symm y).1 : ℝ) : ℂ)) =ᶠ[𝓝 x.1] fun y => ((ph0 y : ℝ) : ℂ) := by
      have hxt : x.1 ∈ e.target := by
        rw [he hxe]
        exact e.map_source hxe
      filter_upwards [e.open_target.mem_nhds hxt] with y hy
      rw [chart_z_symm n Subtype.val e he y hy]
    rw [hleviC _ _ _ heq ξ]
    exact hl x.1 x.2 ξ
  have hI' : ∫⁻ x, ENNReal.ofReal (‖f x.1‖ ^ 2 * (∑ i, ‖g i x.1‖ ^ 2) ^ (-(t + 1)) * Real.exp (-ph0 x.1)) ∂vol n S.z < ⊤ := by
    rw [hz, hvol, lintegral_subtype_comap hU.measurableSet
      (fun y => ENNReal.ofReal (‖f y‖ ^ 2 * (∑ i, ‖g i y‖ ^ 2) ^ (-(t + 1)) * Real.exp (-ph0 y)))]
    exact hI
  obtain ⟨hh, hhH, hhf, hhI⟩ := skoda n U S p (fun i x => g i x.1) (fun x => ph0 x.1) t (fun x => f x.1) hp
    (fun i => by rw [hz]; exact holo_val (hg i)) (fun x => hnz x.1 x.2) hsm hlev ht (by rw [hz]; exact holo_val hf) hI'
  refine ⟨fun i y => if h : y ∈ U then hh i ⟨y, h⟩ else 0, fun i y hy => ?_, fun y hy => ?_, ?_⟩
  · obtain ⟨e, he, hxe⟩ := exists_chart n Subtype.val hzl ⟨y, hy⟩
    have hH : DifferentiableOn ℂ (hh i ∘ e.symm) e.target := by
      have := hhH i
      rw [hz] at this
      exact this e he
    have hyt : y ∈ e.target := by
      have h1 : e ⟨y, hy⟩ = y := (he hxe).symm
      rw [← h1]
      exact e.map_source hxe
    have hD := (hH y hyt).differentiableAt (e.open_target.mem_nhds hyt)
    refine (hD.congr_of_eventuallyEq ?_).differentiableWithinAt
    filter_upwards [e.open_target.mem_nhds hyt] with w hw
    have hwU : w ∈ U := htgt e he hw
    rw [dif_pos hwU]
    show hh i ⟨w, hwU⟩ = hh i (e.symm w)
    congr 1
    exact Subtype.ext (chart_z_symm n Subtype.val e he w hw).symm
  · have := hhf ⟨y, hy⟩
    simpa [hy] using this
  · have hL : ∫⁻ y in U, ENNReal.ofReal ((∑ i, ‖(if h : y ∈ U then hh i ⟨y, h⟩ else 0)‖ ^ 2) *
        (∑ i, ‖g i y‖ ^ 2) ^ (-t) * Real.exp (-ph0 y)) =
        ∫⁻ x, ENNReal.ofReal ((∑ i, ‖hh i x‖ ^ 2) * (∑ i, ‖g i x.1‖ ^ 2) ^ (-t) * Real.exp (-ph0 x.1)) ∂vol n S.z := by
      rw [hz, hvol, ← lintegral_subtype_comap hU.measurableSet]
      refine lintegral_congr fun x => ?_
      simp [x.2]
    have hR : ∫⁻ y in U, ENNReal.ofReal (‖f y‖ ^ 2 * (∑ i, ‖g i y‖ ^ 2) ^ (-(t + 1)) * Real.exp (-ph0 y)) =
        ∫⁻ x, ENNReal.ofReal (‖f x.1‖ ^ 2 * (∑ i, ‖g i x.1‖ ^ 2) ^ (-(t + 1)) * Real.exp (-ph0 x.1)) ∂vol n S.z := by
      rw [hz, hvol, lintegral_subtype_comap hU.measurableSet
        (fun y => ENNReal.ofReal (‖f y‖ ^ 2 * (∑ i, ‖g i y‖ ^ 2) ^ (-(t + 1)) * Real.exp (-ph0 y)))]
    rw [hL, hR]
    exact hhI

end UpDivA

end ReciprocityTheory.ChartRestriction.G.AR.Up
