import Mathlib
import ReciprocityTheory.AnalyticForms.LeviForms.PullDominateStatement
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.TendstoLocallyUniformlyOnOfNhds
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.Giv

noncomputable section

theorem isOpen_compl_bdry {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X}
    {L : LocPot X} {s : X → X → ℂ} (hs : IsSection A L s) : IsOpen (bdry s)ᶜ := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  have hx0 : s x x ≠ 0 := hx
  obtain ⟨j, hj⟩ := A.cover x
  have hleft : (A.chart j).symm (A.chart j x) = x := (A.chart j).left_inv hj
  have hmem : A.chart j x ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' L.U x :=
    ⟨(A.chart j).map_source hj, by
      show (A.chart j).symm (A.chart j x) ∈ L.U x
      rw [hleft]; exact L.mem_U x⟩
  have hg : ContinuousAt (s x ∘ (A.chart j).symm) (A.chart j x) :=
    (hs.1 x j _ hmem).continuousAt
  have hne : (s x ∘ (A.chart j).symm) (A.chart j x) ≠ 0 := by
    simpa [Function.comp_apply, hleft] using hx0
  have h1 : ∀ᶠ y in 𝓝 x, (s x ∘ (A.chart j).symm) (A.chart j y) ≠ 0 :=
    ((A.chart j).continuousAt hj).eventually (hg.eventually_ne hne)
  have h2 : ∀ᶠ y in 𝓝 x, y ∈ (A.chart j).source := (A.chart j).open_source.mem_nhds hj
  have h3 : ∀ᶠ y in 𝓝 x, y ∈ L.U x := (L.isOpen_U x).mem_nhds (L.mem_U x)
  filter_upwards [h1, h2, h3] with y hy1 hy2 hy3
  have hsy : s x y ≠ 0 := by
    simpa [Function.comp_apply, (A.chart j).left_inv hy2] using hy1
  intro hb
  have hb0 : s y y = 0 := hb
  have heq := hs.2 x y y ⟨hy3, L.mem_U y⟩
  rw [hb0, norm_zero, zero_mul] at heq
  exact (mul_ne_zero (norm_ne_zero_iff.2 hsy) (Real.exp_ne_zero _)) heq

theorem regular_family_C2_pullback_of_open {e e' : ℕ} {X X' : Type} [TopologicalSpace X] [TopologicalSpace X']
    (A : FinHolAtlas e X) (A' : FinHolAtlas e' X') (h : X' → X) (hh : HoloMap A' A h)
    (s : X → X → ℂ) (ph : X → ℝ) (phT : ℝ → X → ℝ) (hO : IsOpen (bdry s)ᶜ)
    (hph : A.SmoothOn (bdry s)ᶜ ph)
    (hT : ∀ᶠ t in nhdsWithin 0 (Set.Ioi 0), A.Smooth (phT t))
    (hC : IsRegFamilyC2 A s ph phT) :
    IsRegFamilyC2 A' (fun x y => s (h x) (h y)) (ph ∘ h) (fun t => phT t ∘ h) := by
  have key := GroundTheory.Heights₂.Heights.AnalyticLimit.C2ConvergencePullback.proof A' A h hh (bdry s)ᶜ hO phT ph
    (ph ∘ h) hph (fun _ _ => rfl) hT (fun k K hK hKs => hC k K hKs hK)
  intro j K hKs hK
  exact key j K hK hKs

theorem regular_family_C2_pullback_of_section {e e' : ℕ} {X X' : Type} [TopologicalSpace X] [TopologicalSpace X']
    (A : FinHolAtlas e X) (A' : FinHolAtlas e' X') (h : X' → X) (hh : HoloMap A' A h)
    (L : LocPot X) (s : X → X → ℂ) (ph : X → ℝ) (phT : ℝ → X → ℝ) (hs : IsSection A L s)
    (hph : A.SmoothOn (bdry s)ᶜ ph)
    (hT : ∀ᶠ t in nhdsWithin 0 (Set.Ioi 0), A.Smooth (phT t))
    (hC : IsRegFamilyC2 A s ph phT) :
    IsRegFamilyC2 A' (fun x y => s (h x) (h y)) (ph ∘ h) (fun t => phT t ∘ h) :=
  regular_family_C2_pullback_of_open A A' h hh s ph phT (isOpen_compl_bdry hs) hph hT hC

end

end GlobalTheory.CompanionTheory.Ar.Giv
