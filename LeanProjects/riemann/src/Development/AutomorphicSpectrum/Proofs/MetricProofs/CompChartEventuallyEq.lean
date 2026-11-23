import Mathlib
import ReciprocityTheory.AnalyticForms.LeviForms.PullDominateStatement

open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.Giv

section PullPsh

variable {e e' : ℕ} {X X' : Type} [TopologicalSpace X] [TopologicalSpace X']

theorem comp_chart_eventuallyEq {A : FinHolAtlas e X} {A' : FinHolAtlas e' X'} {h : X' → X}
    (hh : HoloMap A' A h) (g : X → ℝ) (j : Fin A'.n) (k : Fin A.n) {t : Fin e' → ℂ}
    (ht : t ∈ (A'.chart j).target) (hk : h ((A'.chart j).symm t) ∈ (A.chart k).source) :
    (g ∘ h ∘ (A'.chart j).symm) =ᶠ[𝓝 t]
      (g ∘ (A.chart k).symm) ∘ (A.chart k ∘ h ∘ (A'.chart j).symm) := by
  have hc : ContinuousAt (h ∘ (A'.chart j).symm) t :=
    hh.1.continuousAt.comp ((A'.chart j).continuousAt_symm ht)
  have hmem : ∀ᶠ s in 𝓝 t, h ((A'.chart j).symm s) ∈ (A.chart k).source :=
    hc.preimage_mem_nhds ((A.chart k).open_source.mem_nhds hk)
  filter_upwards [hmem] with s hs
  simp only [Function.comp_apply, (A.chart k).left_inv hs]

theorem levi_pull_nonneg {A : FinHolAtlas e X} {A' : FinHolAtlas e' X'} {h : X' → X}
    (hh : HoloMap A' A h) (g : X → ℝ) (j : Fin A'.n) (k : Fin A.n) {t : Fin e' → ℂ}
    (ht : t ∈ (A'.chart j).target) (hk : h ((A'.chart j).symm t) ∈ (A.chart k).source)
    (hg : ContDiffAt ℝ 2 (g ∘ (A.chart k).symm) ((A.chart k ∘ h ∘ (A'.chart j).symm) t))
    (hn : ∀ v, 0 ≤ levi (g ∘ (A.chart k).symm) ((A.chart k ∘ h ∘ (A'.chart j).symm) t) v)
    (w : Fin e' → ℂ) : 0 ≤ levi (g ∘ h ∘ (A'.chart j).symm) t w := by
  rw [ReciprocityTheory.AnForm.levi_congr (comp_chart_eventuallyEq hh g j k ht hk) w,
    ReciprocityTheory.AnForm.levi_comp w (hh.2 j k t ⟨ht, hk⟩) hg]
  exact hn _

theorem chart_image_mem {A : FinHolAtlas e X} {A' : FinHolAtlas e' X'} {h : X' → X}
    (j : Fin A'.n) (k : Fin A.n) {t : Fin e' → ℂ}
    (hk : h ((A'.chart j).symm t) ∈ (A.chart k).source) :
    (A.chart k ∘ h ∘ (A'.chart j).symm) t ∈ (A.chart k).target ∧
      (A.chart k).symm ((A.chart k ∘ h ∘ (A'.chart j).symm) t) = h ((A'.chart j).symm t) := by
  exact ⟨(A.chart k).map_source hk, (A.chart k).left_inv hk⟩

theorem contDiffAt_of_smoothOn {A : FinHolAtlas e X} {U : Set X} (hU : IsOpen U) {f : X → ℝ}
    (hf : A.SmoothOn U f) (k : Fin A.n) {z : Fin e → ℂ} (hz : z ∈ (A.chart k).target)
    (hzU : (A.chart k).symm z ∈ U) : ContDiffAt ℝ ∞ (f ∘ (A.chart k).symm) z := by
  have ho : IsOpen ((A.chart k).target ∩ (A.chart k).symm ⁻¹' U) :=
    (A.chart k).continuousOn_symm.isOpen_inter_preimage (A.chart k).open_target hU
  exact (hf k).contDiffAt (ho.mem_nhds ⟨hz, hzU⟩)

theorem smoothOn_pull {A : FinHolAtlas e X} {A' : FinHolAtlas e' X'} {h : X' → X}
    (hh : HoloMap A' A h) {U : Set X} (hU : IsOpen U) {f : X → ℝ} (hf : A.SmoothOn U f) :
    A'.SmoothOn (h ⁻¹' U) (f ∘ h) := by
  intro j
  have key : ∀ t ∈ (A'.chart j).target ∩ (A'.chart j).symm ⁻¹' (h ⁻¹' U),
      ContDiffAt ℝ ∞ ((f ∘ h) ∘ (A'.chart j).symm) t := by
    rintro t ⟨ht, htU⟩
    obtain ⟨k, hk⟩ := A.cover (h ((A'.chart j).symm t))
    have hF : AnalyticAt ℂ (A.chart k ∘ h ∘ (A'.chart j).symm) t := hh.2 j k t ⟨ht, hk⟩
    have hF' : ContDiffAt ℂ ∞ (A.chart k ∘ h ∘ (A'.chart j).symm) t := hF.contDiffAt
    have hci := chart_image_mem (A := A) (A' := A') (h := h) j k hk
    have hzU : (A.chart k).symm ((A.chart k ∘ h ∘ (A'.chart j).symm) t) ∈ U := by
      rw [hci.2]; exact htU
    have hfk : ContDiffAt ℝ ∞ (f ∘ (A.chart k).symm) ((A.chart k ∘ h ∘ (A'.chart j).symm) t) :=
      contDiffAt_of_smoothOn hU hf k hci.1 hzU
    have hcomp : ContDiffAt ℝ ∞ ((f ∘ (A.chart k).symm) ∘ (A.chart k ∘ h ∘ (A'.chart j).symm)) t :=
      hfk.comp t (hF'.restrict_scalars ℝ)
    exact hcomp.congr_of_eventuallyEq (comp_chart_eventuallyEq hh f j k ht hk)
  intro t ht
  exact (key t ht).contDiffWithinAt

theorem isPsh_pull {A : FinHolAtlas e X} {A' : FinHolAtlas e' X'} {h : X' → X}
    (hh : HoloMap A' A h) {P : LocPot X} (hP : IsPotential A P) (hpsh : IsPsh A P) :
    IsPsh A' (P.pullback h hh.1) := by
  intro x j y hy w
  obtain ⟨k, hk⟩ := A.cover (h ((A'.chart j).symm y))
  have hci := chart_image_mem (A := A) (A' := A') (h := h) j k hk
  have hyP : h ((A'.chart j).symm y) ∈ P.U (h x) := hy.2
  have hzU : (A.chart k).symm ((A.chart k ∘ h ∘ (A'.chart j).symm) y) ∈ P.U (h x) := by
    rw [hci.2]; exact hyP
  have h2 : (2 : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
  have hg : ContDiffAt ℝ 2 (P.φ (h x) ∘ (A.chart k).symm)
      ((A.chart k ∘ h ∘ (A'.chart j).symm) y) :=
    (contDiffAt_of_smoothOn (P.isOpen_U (h x)) (hP.1 (h x)) k hci.1 hzU).of_le h2
  exact levi_pull_nonneg hh (P.φ (h x)) j k hy.1 hk hg (fun v => hpsh (h x) k _ ⟨hci.1, hzU⟩ v) w

theorem isPshOn_pull {A : FinHolAtlas e X} {A' : FinHolAtlas e' X'} {h : X' → X}
    (hh : HoloMap A' A h) {P : LocPot X} {U : Set X} {f : X → ℝ} (hU : IsOpen U)
    (hP : IsPotential A P) (hf : A.SmoothOn U f) (hpsh : IsPshOn A U (P + LocPot.ofFun f)) :
    IsPshOn A' (h ⁻¹' U) (P.pullback h hh.1 + LocPot.ofFun (f ∘ h)) := by
  intro x j y hy w
  obtain ⟨k, hk⟩ := A.cover (h ((A'.chart j).symm y))
  have hci := chart_image_mem (A := A) (A' := A') (h := h) j k hk
  have hyP : h ((A'.chart j).symm y) ∈ P.U (h x) := hy.2.1.1
  have hyU : h ((A'.chart j).symm y) ∈ U := hy.2.2
  have hzP : (A.chart k).symm ((A.chart k ∘ h ∘ (A'.chart j).symm) y) ∈ P.U (h x) := by
    rw [hci.2]; exact hyP
  have hzU : (A.chart k).symm ((A.chart k ∘ h ∘ (A'.chart j).symm) y) ∈ U := by
    rw [hci.2]; exact hyU
  have h2 : (2 : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
  have hg : ContDiffAt ℝ 2 ((fun z => P.φ (h x) z + f z) ∘ (A.chart k).symm)
      ((A.chart k ∘ h ∘ (A'.chart j).symm) y) :=
    ((contDiffAt_of_smoothOn (P.isOpen_U (h x)) (hP.1 (h x)) k hci.1 hzP).add
      (contDiffAt_of_smoothOn hU hf k hci.1 hzU)).of_le h2
  have hmem : (A.chart k ∘ h ∘ (A'.chart j).symm) y ∈
      (A.chart k).target ∩ (A.chart k).symm ⁻¹' ((P + LocPot.ofFun f).U (h x) ∩ U) :=
    ⟨hci.1, ⟨hzP, Set.mem_univ _⟩, hzU⟩
  exact levi_pull_nonneg hh (fun z => P.φ (h x) z + f z) j k hy.1 hk hg
    (fun v => hpsh (h x) k _ hmem v) w

theorem pullPsh : PullPshStatement := by
  intro e e' X X' _ _ A A' h hh P U f hU hP
  exact ⟨fun hf => smoothOn_pull hh hU hf, fun hpsh => isPsh_pull hh hP hpsh,
    fun hf hpsh => isPshOn_pull hh hU hP hf hpsh⟩

end PullPsh

end GlobalTheory.CompanionTheory.Ar.Giv
