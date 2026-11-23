import Mathlib
import GroundTheory.HeightsAndTheta.Heights.LocalDensities.Statements
import GroundTheory.HeightsAndTheta.Heights.LocalDensities.HypImp
import ReciprocityTheory.AnalyticForms.AnalyticCharts.Osgood
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.FourB

open MeasureTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M Filter Topology
open scoped ContDiff

namespace OpenSetChart

variable {D : ℕ} {M : Set (Fin D → ℂ)}

open scoped Classical in

def retract (x₀ : Fin D → ℂ) (hx₀ : x₀ ∈ M) (y : Fin D → ℂ) : M :=
  ⟨if y ∈ M then y else x₀, by split_ifs with h; exacts [h, hx₀]⟩

theorem retract_of_mem {x₀ : Fin D → ℂ} (hx₀ : x₀ ∈ M) {y : Fin D → ℂ} (hy : y ∈ M) :
    (retract x₀ hx₀ y : Fin D → ℂ) = y := by
  simp [retract, hy]

theorem measurable_retract (hM : IsOpen M) {x₀ : Fin D → ℂ} (hx₀ : x₀ ∈ M) :
    Measurable (retract x₀ hx₀) := by
  classical
  unfold retract
  exact (Measurable.ite hM.measurableSet measurable_id measurable_const).subtype_mk

def chart (hM : IsOpen M) (x₀ : Fin D → ℂ) (hx₀ : x₀ ∈ M) : OpenPartialHomeomorph M (Fin D → ℂ) where
  toFun := Subtype.val
  invFun := retract x₀ hx₀
  source := Set.univ
  target := M
  map_source' x _ := x.2
  map_target' _ _ := Set.mem_univ _
  left_inv' x _ := Subtype.ext (retract_of_mem hx₀ x.2)
  right_inv' _ hy := retract_of_mem hx₀ hy
  open_source := isOpen_univ
  open_target := hM
  continuousOn_toFun := continuous_subtype_val.continuousOn
  continuousOn_invFun := by
    rw [continuousOn_iff_continuous_domRestrict]
    convert (continuous_id : Continuous (id : M → M)) using 1
    funext y
    exact Subtype.ext (retract_of_mem hx₀ y.2)

theorem eventuallyEq_retract (hM : IsOpen M) {x₀ : Fin D → ℂ} (hx₀ : x₀ ∈ M) {y : Fin D → ℂ}
    (hy : y ∈ M) : (fun y' => (retract x₀ hx₀ y' : Fin D → ℂ)) =ᶠ[𝓝 y] id :=
  Filter.eventually_of_mem (hM.mem_nhds hy) fun _ hy' => retract_of_mem hx₀ hy'

def atlas (hM : IsOpen M) (x₀ : Fin D → ℂ) (hx₀ : x₀ ∈ M) : FinHolAtlas D M where
  n := 1
  chart _ := chart hM x₀ hx₀
  cover _ := ⟨0, Set.mem_univ _⟩
  holo _ _ := fun _ hy => analyticAt_id.congr (eventuallyEq_retract hM hx₀ hy.1).symm

def partition (hM : IsOpen M) (x₀ : Fin D → ℂ) (hx₀ : x₀ ∈ M) :
    ChartPartition (atlas hM x₀ hx₀) where
  χ _ _ := 1
  smooth _ := fun _ => contDiffOn_const
  nonneg _ _ := zero_le_one
  tsupport_subset _ := fun _ _ => Set.mem_univ _
  sum_eq_one _ := by
    show ∑ _j : Fin 1, (1 : ℝ) = 1
    simp

theorem maMeasure_univ (hM : IsOpen M) (x₀ : Fin D → ℂ) (hx₀ : x₀ ∈ M) (u : M → ℝ) :
    maMeasure (atlas hM x₀ hx₀) (fun _ => LocPot.ofFun u) Set.univ =
      ∫⁻ y in M, ENNReal.ofReal (maDens (fun _ y' => u (retract x₀ hx₀ y')) y) := by
  have hne : Nonempty (ChartPartition (atlas hM x₀ hx₀)) := ⟨partition hM x₀ hx₀⟩
  have : Subsingleton (Fin (atlas hM x₀ hx₀).n) := (inferInstance : Subsingleton (Fin 1))
  have hχ : ∀ j x, hne.some.χ j x = 1 := by
    intro j x
    have h := hne.some.sum_eq_one x
    rwa [Fintype.sum_subsingleton _ j] at h
  let j0 : Fin (atlas hM x₀ hx₀).n := ⟨0, Nat.zero_lt_one⟩
  have ht : ((atlas hM x₀ hx₀).chart j0).target = M := rfl
  have hm : Measurable ((atlas hM x₀ hx₀).chart j0).symm := measurable_retract hM hx₀
  rw [maMeasure, dif_pos hne, Fintype.sum_subsingleton _ j0,
    Measure.map_apply hm MeasurableSet.univ, Set.preimage_univ,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, ht]
  refine lintegral_congr fun y => ?_
  rw [hχ, one_mul]
  rfl

end OpenSetChart

open OpenSetChart

theorem maDens_congr_germ' {D : ℕ} {φ ψ : Fin D → (Fin D → ℂ) → ℝ} {y : Fin D → ℂ}
    (h : ∀ i, φ i =ᶠ[𝓝 y] ψ i) : maDens φ y = maDens ψ y := by
  have hH : ∀ i, hessC (φ i) y = hessC (ψ i) y := by
    intro i
    have h1 : fderiv ℝ (φ i) =ᶠ[𝓝 y] fderiv ℝ (ψ i) := (h i).fderiv
    unfold hessC
    rw [h1.fderiv_eq]
  unfold maDens
  simp only [hH]

theorem CoverMass2.of_fubiniStudyCoverMass (hA : FubiniStudyCoverMass.Statement) :
    IndefiniteRowSideFullHecke.FourB.CoverMass2.Statement := by
  intro D M Z z δ hB
  obtain ⟨hM, hZ, hz, hmaps, hcov, hfib⟩ := hB
  rcases M.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · have hZc : Zᶜ.Nonempty := by
      by_contra h
      rw [Set.not_nonempty_iff_eq_empty, Set.compl_empty_iff] at h
      rw [h, Measure.measure_univ_eq_zero] at hZ
      exact NeZero.ne (volume : Measure (Fin D → ℂ)) hZ
    obtain ⟨w, hw⟩ := hZc
    have h1 := hfib w hw
    have h0 : {x | x ∈ (∅ : Set (Fin D → ℂ)) ∧ z x = w} = ∅ := by simp
    rw [h0, Set.encard_empty] at h1
    have hδ : δ = 0 := by exact_mod_cast h1.symm
    subst hδ
    simp
  ·
    have hδ : δ ≠ 0 := by
      intro h0
      have h1 := hfib (z x₀) (hmaps hx₀)
      have hmem : x₀ ∈ {x | x ∈ M ∧ z x = z x₀} := ⟨hx₀, rfl⟩
      rw [h0, Nat.cast_zero, Set.encard_eq_zero] at h1
      rw [h1] at hmem
      exact hmem

    have hZcl : IsClosed Z := by
      rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
      intro w hw
      obtain ⟨-, U, hwU, hU, -, H, hH⟩ := hcov w hw
      obtain ⟨x, hxM, hxw⟩ : {x | x ∈ M ∧ z x = w}.Nonempty := by
        rw [← Set.encard_pos, hfib w hw]
        exact_mod_cast Nat.pos_of_ne_zero hδ
      let i : (fun x : M => z x) ⁻¹' {w} := ⟨⟨x, hxM⟩, hxw⟩
      refine ⟨U, fun v hv => ?_, hU, hwU⟩
      have h1 : v = z (H.symm (⟨v, hv⟩, i)).1 := by
        simpa using hH (H.symm (⟨v, hv⟩, i))
      rw [h1]
      exact hmaps (H.symm (⟨v, hv⟩, i)).1.2

    have han : ∀ i, AnalyticOnNhd ℂ (fun y => z y i) M := fun i =>
      ReciprocityTheory.AnForm.Osgood.osgood D M _ hM (differentiableOn_pi.1 hz i)
    let A := atlas hM x₀ hx₀
    let q : M → Fin D → ℂ := fun x => z x
    let u : M → ℝ := fun x => (1 / 2) * Real.log (1 + ∑ i, ‖q x i‖ ^ 2)
    have hsm : ContDiffOn ℝ ∞ (fun y => (1 / 2) * Real.log (1 + ∑ i, ‖z y i‖ ^ 2)) M := by
      refine contDiffOn_const.mul (ContDiffOn.log (contDiffOn_const.add (ContDiffOn.sum
        fun i _ => (contDiff_norm_sq ℝ).comp_contDiffOn
          (((han i).contDiffOn hM.uniqueDiffOn).restrict_scalars ℝ))) fun y _ => ?_)
      positivity
    have hu : A.Smooth u := by
      intro j
      refine (hsm.mono Set.inter_subset_left).congr fun y hy => ?_
      show u (retract x₀ hx₀ y) = _
      simp only [u, q, retract_of_mem hx₀ hy.1]
    have hHyp : FubiniStudyCoverMass.Hyp A (LocPot.ofFun u) q Set.univ Z δ := by
      refine ⟨isPotential_ofFun A u hu, isOpen_univ, ?_, ?_, ?_, hZcl, hZ,
        ⟨fun x _ => hmaps x.2, ?_⟩, ?_, ?_⟩
      · intro x
        refine ⟨Set.univ, isOpen_univ, Set.mem_univ _, 1, fun _ _ => 1,
          fun _ _ => analyticOnNhd_const, ?_⟩
        ext y
        simp
      · simp
      · intro i j y hy
        exact ((han i) y hy.1).congr
          (((eventuallyEq_retract hM hx₀ hy.1).fun_comp fun y' => z y' i).symm)
      · have hpre : (Set.univ : Set M) = (fun x : M => z x) ⁻¹' Zᶜ := by
          ext x
          simpa using hmaps x.2
        exact hcov.isCoveringMap_restrictPreimage.comp_homeomorph (Homeomorph.setCongr hpre)
      · intro w hw
        rw [← hfib w hw, ← Subtype.val_injective.encard_image]
        congr 1
        ext y
        simp [q, and_comm]
      · intro x y _
        refine ⟨Set.univ, isOpen_univ, Set.mem_univ _, 0, fun _ _ _ => analyticAt_const, ?_⟩
        intro v _
        simp [LocPot.ofFun, u]
    have key := (hA A (LocPot.ofFun u) q Set.univ Z δ hHyp).2
    rw [maMeasure_univ] at key
    rw [← key]
    refine setLIntegral_congr_fun hM.measurableSet fun y hy => ?_
    show ENNReal.ofReal (maDens _ y) = ENNReal.ofReal (maDens _ y)
    congr 1
    refine maDens_congr_germ' fun _ => ?_
    filter_upwards [hM.mem_nhds hy] with y' hy'
    simp only [u, q, retract_of_mem hx₀ hy']
    ring

end GroundTheory.Heights₂.Heights.FourB
