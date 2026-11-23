import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetMeasStatement
import ReciprocityTheory.L2DbarEstimates.NormFibrations.Hormander
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.MeasurableSetImageOfIsLocalHomeomorph
import ReciprocityTheory.L2DbarEstimates.LeviForms.EventuallyDifferentiableAtOfContDiffAt

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.OntoA

open ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter Set
open scoped ContDiff ENNReal ComplexConjugate

noncomputable section

variable {n : ℕ} {U : Set (V n)}

def gch (hU : IsOpen U) [Nonempty U] : OpenPartialHomeomorph U (V n) :=
  hU.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph Subtype.val

theorem gch_apply (hU : IsOpen U) [Nonempty U] (x : U) : gch hU x = x.1 := by
  simp [gch]

theorem gch_source (hU : IsOpen U) [Nonempty U] : (gch hU).source = univ := by
  simp [gch]

theorem gch_target (hU : IsOpen U) [Nonempty U] : (gch hU).target = U := by
  simp [gch, Subtype.range_coe]

theorem gch_isChart (hU : IsOpen U) [Nonempty U] : IsChart n (Subtype.val : U → V n) (gch hU) :=
  fun x _ => (gch_apply hU x).symm

theorem gch_symm (hU : IsOpen U) [Nonempty U] {y : V n} (hy : y ∈ U) :
    ((gch hU).symm y : V n) = y := by
  have h := (gch hU).right_inv (by rw [gch_target]; exact hy)
  rwa [gch_apply] at h

theorem val_lh (hU : IsOpen U) : IsLocalHomeomorph (Subtype.val : U → V n) :=
  hU.isOpenEmbedding_subtypeVal.isLocalHomeomorph

private theorem coe_symm_apply_of_isChart_val {e : OpenPartialHomeomorph U (V n)}
    (he : IsChart n (Subtype.val : U → V n) e) {y : V n} (hy : y ∈ e.target) :
    ((e.symm y : U) : V n) = y := by
  rw [he (e.map_target hy)]
  exact e.right_inv hy

theorem smooth_of (hU : IsOpen U) [Nonempty U] {f : V n → ℂ} (hf : ContDiffOn ℝ ∞ f U) :
    Smooth n (Subtype.val : U → V n) (fun x => f x.1) := by
  intro e he
  refine (hf.mono ?_).congr ?_
  · intro y hy
    rw [← coe_symm_apply_of_isChart_val he hy]
    exact (e.symm y).2
  · intro y hy
    simp only [Function.comp_apply]
    rw [coe_symm_apply_of_isChart_val he hy]

theorem smoothR_of (hU : IsOpen U) [Nonempty U] {f : V n → ℝ} (hf : ContDiffOn ℝ ∞ f U) :
    SmoothR n (Subtype.val : U → V n) (fun x => f x.1) := by
  have h2 : ContDiffOn ℝ ∞ (fun y => (f y : ℂ)) U := Complex.ofRealCLM.contDiff.comp_contDiffOn hf
  exact smooth_of hU h2

private theorem comp_chart_symm_eventuallyEq_of_mem_source {e : OpenPartialHomeomorph U (V n)}
    (he : IsChart n (Subtype.val : U → V n) e) {x : U} (hx : x ∈ e.source) (g : V n → ℂ) :
    ((fun y : U => g y.1) ∘ e.symm) =ᶠ[𝓝 x.1] g := by
  have hxt : (x : V n) ∈ e.target := by
    rw [he hx]
    exact e.map_source hx
  filter_upwards [e.open_target.mem_nhds hxt] with y hy
  simp only [Function.comp_apply, coe_symm_apply_of_isChart_val he hy]

private theorem db_val_eq_wdb_of_isOpen (hU : IsOpen U) [Nonempty U] (j : Fin n) (G : V n → ℂ) (x : U) :
    db n (Subtype.val : U → V n) j (fun y => G y.1) x = wdb n j G x.1 := by
  have h : ∃ e : OpenPartialHomeomorph U (V n), IsChart n (Subtype.val : U → V n) e ∧
      x ∈ e.source := ⟨gch hU, gch_isChart hU, by rw [gch_source]; trivial⟩
  unfold db
  rw [dif_pos h]
  exact wdb_congr (comp_chart_symm_eventuallyEq_of_mem_source (Classical.choose_spec h).1 (Classical.choose_spec h).2 G)

theorem dbarDot_eq (hU : IsOpen U) [Nonempty U] (F0 : V n → ℂ) (x : U) (ξ : Fin n → ℂ) :
    dbarDot n (Subtype.val : U → V n) (fun y => F0 y.1) x ξ = ∑ j, wdb n j F0 x.1 * conj (ξ j) := by
  unfold dbarDot
  simp only [db_val_eq_wdb_of_isOpen hU]

private theorem d_val_eq_wd_of_isOpen (hU : IsOpen U) [Nonempty U] (j : Fin n) (G : V n → ℂ) (x : U) :
    d n (Subtype.val : U → V n) j (fun y => G y.1) x = wd n j G x.1 := by
  have h : ∃ e : OpenPartialHomeomorph U (V n), IsChart n (Subtype.val : U → V n) e ∧
      x ∈ e.source := ⟨gch hU, gch_isChart hU, by rw [gch_source]; trivial⟩
  unfold d
  rw [dif_pos h]
  exact wd_congr (comp_chart_symm_eventuallyEq_of_mem_source (Classical.choose_spec h).1 (Classical.choose_spec h).2 G)

theorem levi_eq (hU : IsOpen U) [Nonempty U] (ph : V n → ℝ) (x : U) (ξ : Fin n → ℂ) :
    Levi n (Subtype.val : U → V n) (fun y => ph y.1) x ξ =
      leviV n (fun w => (ph w : ℂ)) x.1 ξ := by
  have hin : ∀ k, db n (Subtype.val : U → V n) k (fun y => ((ph y.1 : ℝ) : ℂ)) =
      fun y => wdb n k (fun w => (ph w : ℂ)) y.1 :=
    fun k => funext fun y => db_val_eq_wdb_of_isOpen hU k (fun w => (ph w : ℂ)) y
  unfold Levi leviV
  simp only [hin, d_val_eq_wd_of_isOpen hU]

private theorem vol_val_eq_comap_volume (hU : IsOpen U) :
    vol n (Subtype.val : U → V n) = Measure.comap Subtype.val (volume : Measure (V n)) := by
  have hmeas : MeasurableSet U := hU.measurableSet
  ext A hA
  rw [vol_apply n _ (val_lh hU) A hA,
    Measure.comap_apply _ Subtype.val_injective (fun s hs => MeasurableSet.subtype_image hmeas hs) _ hA]
  unfold volFun
  have hind : ∀ y, (((A ∩ Subtype.val ⁻¹' {y}).encard : ℕ∞) : ℝ≥0∞) =
      (Subtype.val '' A).indicator 1 y := by
    intro y
    by_cases hy : y ∈ Subtype.val '' A
    · obtain ⟨a, ha, rfl⟩ := hy
      have h1 : A ∩ Subtype.val ⁻¹' {(a : V n)} = {a} := by
        ext b
        simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
        constructor
        · rintro ⟨_, hb⟩
          exact Subtype.ext hb
        · rintro rfl
          exact ⟨ha, rfl⟩
      rw [h1, Set.encard_singleton]
      simp [Set.indicator_apply, Set.mem_image_of_mem _ ha]
    · have h1 : A ∩ Subtype.val ⁻¹' {y} = ∅ := by
        ext b
        simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
          Set.mem_empty_iff_false, iff_false, not_and]
        intro hb hby
        exact hy ⟨b, hb, hby⟩
      rw [h1, Set.encard_empty]
      simp [Set.indicator_apply, hy]
  simp_rw [hind]
  exact lintegral_indicator_one (MeasurableSet.subtype_image hmeas hA)

theorem horm_open (hU : IsOpen U) (S : EtaleStein n U) (hSz : S.z = Subtype.val)
    (ph : V n → ℝ) (F0 : V n → ℂ) (hr : V n → ℝ)
    (hph : ContDiffOn ℝ ∞ ph U) (hpsh : ∀ y ∈ U, ∀ ξ, 0 ≤ (leviV n (fun w => (ph w : ℂ)) y ξ).re)
    (hF0 : ContDiffOn ℝ ∞ F0 U) (hrc : ContinuousOn hr U) (hr0 : ∀ y ∈ U, 0 ≤ hr y)
    (hineq : ∀ y ∈ U, ∀ ξ : Fin n → ℂ,
      ‖∑ j, wdb n j F0 y * conj (ξ j)‖ ^ 2 ≤ hr y * (leviV n (fun w => (ph w : ℂ)) y ξ).re) :
    ∃ F : V n → ℂ, DifferentiableOn ℂ F U ∧
      ∫⁻ y in U, ENNReal.ofReal (‖F0 y - F y‖ ^ 2 * Real.exp (-ph y)) ≤
        ∫⁻ y in U, ENNReal.ofReal (hr y) * ENNReal.ofReal (Real.exp (-ph y)) := by
  rcases isEmpty_or_nonempty U with hE | hne
  · have hU0 : U = ∅ := Set.isEmpty_coe_sort.mp hE
    subst hU0
    exact ⟨0, differentiableOn_empty, by simp⟩
  have hmeas : MeasurableSet U := hU.measurableSet
  have hs1 : SmoothR n S.z (fun y => ph y.1) := by
    rw [hSz]
    exact smoothR_of hU hph
  have hs2 : LeviNonneg n S.z (fun y => ph y.1) := by
    rw [hSz]
    intro x ξ
    rw [levi_eq hU ph x ξ]
    exact hpsh x.1 x.2 ξ
  have hs3 : Smooth n S.z (fun y => F0 y.1) := by
    rw [hSz]
    exact smooth_of hU hF0
  have hs4 : Measurable (fun y : U => ENNReal.ofReal (hr y.1)) :=
    (hrc.restrict.measurable).ennreal_ofReal
  have hs5 : ∀ (x : U) (ξ : Fin n → ℂ),
      ENNReal.ofReal (‖dbarDot n S.z (fun y => F0 y.1) x ξ‖ ^ 2) ≤
        ENNReal.ofReal (hr x.1) * ENNReal.ofReal (Levi n S.z (fun y => ph y.1) x ξ).re := by
    rw [hSz]
    intro x ξ
    rw [dbarDot_eq hU, levi_eq hU, ← ENNReal.ofReal_mul (hr0 x.1 x.2)]
    exact ENNReal.ofReal_le_ofReal (hineq x.1 x.2 ξ)
  obtain ⟨F, hHolo, hint⟩ := ReciprocityTheory.L2DbarEstimates.hormander n U S (fun y => ph y.1) (fun y => F0 y.1)
    (fun y => ENNReal.ofReal (hr y.1)) hs1 hs2 hs3 hs4 hs5

  classical
  obtain ⟨F', hF'⟩ : ∃ F' : V n → ℂ, ∀ x : U, F' x.1 = F x :=
    ⟨fun y => if h : y ∈ U then F ⟨y, h⟩ else 0, fun x => by simp [x.2]⟩
  have hdiff : DifferentiableOn ℂ F' U := by
    have h1 := hHolo (gch hU) (hSz ▸ gch_isChart hU)
    rw [gch_target] at h1
    refine h1.congr ?_
    intro y hy
    have h2 : (gch hU).symm y = ⟨y, hy⟩ := Subtype.ext (gch_symm hU hy)
    simp only [Function.comp_apply, h2]
    exact hF' ⟨y, hy⟩
  refine ⟨F', hdiff, ?_⟩
  have L1 := lintegral_subtype_comap (μ := (volume : Measure (V n))) hmeas
    (fun y => ENNReal.ofReal (‖F0 y - F' y‖ ^ 2 * Real.exp (-ph y)))
  have L2 := lintegral_subtype_comap (μ := (volume : Measure (V n))) hmeas
    (fun y => ENNReal.ofReal (hr y) * ENNReal.ofReal (Real.exp (-ph y)))
  rw [← L1, ← L2, ← vol_val_eq_comap_volume hU]
  simpa only [wint, hF', hSz] using hint

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.OntoA
