import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SameOrbitRefl
open MvPolynomial Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.Cj GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.Cj

theorem exists_holoMap_inverse_of_degree_one : ∀ {e : ℕ} {X Y : Type} [TopologicalSpace X] [T2Space X]
    [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] (A : FinHolAtlas e X) (B : FinHolAtlas e Y)
    (h : Y → X), HoloMap B A h → IsDegreeOff A B h 1 ∅ →
    ∃ g : X → Y, (∀ y, g (h y) = y) ∧ (∀ x, h (g x) = x) ∧ HoloMap A B g := by
  intro e X Y _ _ _ _ _ A B h hh hd
  obtain ⟨-, -, -, -, hfib, hdet⟩ := hd
  have hex : ∀ x, ∃ y, h ⁻¹' {x} = {y} := fun x => Set.ncard_eq_one.1 (hfib x (by simp))
  have hinj : Function.Injective h := by
    intro a b hab
    obtain ⟨c, hc⟩ := hex (h a)
    have ha : a ∈ h ⁻¹' {h a} := rfl
    have hb : b ∈ h ⁻¹' {h a} := hab.symm
    rw [hc] at ha hb
    exact ha.trans hb.symm
  have hsurj : Function.Surjective h := by
    intro x
    obtain ⟨c, hc⟩ := hex x
    have hcx : c ∈ h ⁻¹' {x} := by rw [hc]; rfl
    exact ⟨c, hcx⟩
  let E : Y ≃ X := Equiv.ofBijective h ⟨hinj, hsurj⟩
  have hEc : Continuous E := hh.1
  obtain ⟨g, hgE⟩ : ∃ g : X → Y, g = E.symm := ⟨_, rfl⟩
  have hgc : Continuous g := by
    rw [hgE]; exact hEc.homeoOfEquivCompactToT2.symm.continuous
  have hgh : ∀ y, g (h y) = y := fun y => by rw [hgE]; exact E.symm_apply_apply y
  have hhg : ∀ x, h (g x) = x := fun x => by rw [hgE]; exact E.apply_symm_apply x
  refine ⟨g, hgh, hhg, hgc, fun j k w hw => ?_⟩
  obtain ⟨hwt, hws⟩ := hw
  have hys : g ((A.chart j).symm w) ∈ (B.chart k).source := hws
  obtain ⟨v, hv⟩ : ∃ v, v = B.chart k (g ((A.chart j).symm w)) := ⟨_, rfl⟩
  have hvt : v ∈ (B.chart k).target := hv ▸ (B.chart k).map_source hys
  have hsv : (B.chart k).symm v = g ((A.chart j).symm w) := by
    rw [hv]; exact (B.chart k).left_inv hys
  have hhv : h ((B.chart k).symm v) ∈ (A.chart j).source := by
    rw [hsv, hhg]; exact (A.chart j).map_target hwt
  obtain ⟨T, hT⟩ : ∃ T : (Fin e → ℂ) → Fin e → ℂ, T = A.chart j ∘ h ∘ (B.chart k).symm := ⟨_, rfl⟩
  have hTa : AnalyticAt ℂ T v := by
    rw [hT]; exact hh.2 k j v ⟨hvt, hhv⟩
  have hTv : T v = w := by
    rw [hT]
    simp only [Function.comp_apply]
    rw [hsv, hhg]
    exact (A.chart j).right_inv hwt
  have hdet' : (fderiv ℂ T v).det ≠ 0 := by
    rw [hT]; exact hdet k j v hvt (by simp) hhv
  have hCe := ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero (fderiv ℂ T v) hdet'
  obtain ⟨Ce, hCedef⟩ : ∃ Ce, Ce = (fderiv ℂ T v).toContinuousLinearEquivOfDetNeZero hdet' := ⟨_, rfl⟩
  rw [← hCedef] at hCe
  have hstrict : HasStrictFDerivAt T (Ce : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ)) v := by
    rw [hCe]; exact hTa.hasStrictFDerivAt
  set F := hstrict.toOpenPartialHomeomorph T with hF
  have hFc : (F : (Fin e → ℂ) → (Fin e → ℂ)) = T := hstrict.toOpenPartialHomeomorph_coe
  have hus : v ∈ F.source := hstrict.mem_toOpenPartialHomeomorph_source
  have hsym : AnalyticAt ℂ F.symm w := by
    have h1 : AnalyticAt ℂ F.symm (F v) :=
      F.analyticAt_symm' (i := Ce) hus (by rw [hFc]; exact hTa) (by rw [hFc, hCe])
    rwa [hFc, hTv] at h1
  have hc2 : ContinuousAt (g ∘ (A.chart j).symm) w :=
    hgc.continuousAt.comp ((A.chart j).continuousAt_symm hwt)
  have hc : ContinuousAt (B.chart k ∘ g ∘ (A.chart j).symm) w :=
    ContinuousAt.comp (g := B.chart k) ((B.chart k).continuousAt hys) hc2
  have hus' : F.source ∈ nhds ((B.chart k ∘ g ∘ (A.chart j).symm) w) := by
    have : (B.chart k ∘ g ∘ (A.chart j).symm) w = v := hv.symm
    rw [this]; exact F.open_source.mem_nhds hus
  refine hsym.congr ?_
  filter_upwards [hc.preimage_mem_nhds hus',
    hc2.preimage_mem_nhds ((B.chart k).open_source.mem_nhds hys),
    (A.chart j).open_target.mem_nhds hwt] with w' h1 h2 h3
  have h2' : g ((A.chart j).symm w') ∈ (B.chart k).source := h2
  have e1 : T ((B.chart k ∘ g ∘ (A.chart j).symm) w') = w' := by
    rw [hT]
    simp only [Function.comp_apply]
    rw [(B.chart k).left_inv h2', hhg]
    exact (A.chart j).right_inv h3
  have e2 := F.left_inv h1
  rw [hFc, e1] at e2
  exact e2

end GlobalTheory.CompanionTheory.Ar.PB.Cj
