import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FlagIndices
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Objects
import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Giv

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo
  GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ContDiff

namespace SecPot

section General

variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem holoOn_continuousOn' {A : FinHolAtlas e X} {W : Set X} {f : X → ℂ} (h : A.HoloOn W f) :
    ContinuousOn f W := by
  intro z hz
  obtain ⟨j, hj⟩ := A.cover z
  have h1 : (A.chart j).symm (A.chart j z) = z := (A.chart j).left_inv hj
  have hu : A.chart j z ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' W :=
    ⟨(A.chart j).map_source hj, by rw [Set.mem_preimage, h1]; exact hz⟩
  have hc : ContinuousAt (f ∘ (A.chart j).symm) (A.chart j z) := (h j _ hu).continuousAt
  have hc2 : ContinuousAt ((f ∘ (A.chart j).symm) ∘ (A.chart j)) z :=
    ContinuousAt.comp hc ((A.chart j).continuousAt hj)
  have hev : ((f ∘ (A.chart j).symm) ∘ (A.chart j)) =ᶠ[𝓝 z] f := by
    filter_upwards [(A.chart j).open_source.mem_nhds hj] with y hy
    simp [(A.chart j).left_inv hy]
  exact (hc2.congr hev).continuousWithinAt

end General

section Model

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P : Ideal (MRing ι)} {d : ℕ}

structure LocSec (M : CxModel P d) (U : Set M.Xc) (s : M.Xc → (Σ k, ι k) → ℂ) : Prop where
  isOpen : IsOpen U
  sec : ∀ y ∈ U, s y ∈ mcPts P ∧ M.proj (s y) = y
  holo : ∀ p, M.atlas.HoloOn U fun y => s y p

theorem locSec_sections (M : CxModel P d) (x : M.Xc) :
    LocSec M (M.sections x).choose (M.sections x).choose_spec.2.2.choose :=
  ⟨(M.sections x).choose_spec.1, (M.sections x).choose_spec.2.2.choose_spec.1,
    (M.sections x).choose_spec.2.2.choose_spec.2⟩

theorem smoothOn_log_sec {M : CxModel P d} {U : Set M.Xc} {s : M.Xc → (Σ k, ι k) → ℂ}
    (hs : LocSec M U s) {B : HermLine ι} (hB : IsSmoothHerm B) :
    M.atlas.SmoothOn U (fun y => Real.log (B.h (s y))) := by
  intro j y hy
  have hσ : ContDiffAt ℝ ∞ (fun y' => s ((M.atlas.chart j).symm y')) y :=
    contDiffAt_pi.2 fun p => ((hs.holo p j y hy).contDiffAt (n := ∞)).restrict_scalars ℝ
  have hm := (hs.sec _ hy.2).1.1
  have hn : {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} ∈ 𝓝 (s ((M.atlas.chart j).symm y)) := by
    refine IsOpen.mem_nhds ?_ hm
    simp only [Set.setOf_forall, Set.setOf_exists]
    exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
      isOpen_ne_fun (continuous_apply _) continuous_const
  have h1 : ContDiffAt ℝ ∞ (fun y' => Real.log (B.h (s ((M.atlas.chart j).symm y')))) y :=
    ((hB.contDiffAt hn).comp y hσ).log (B.pos _ hm).ne'
  exact h1.contDiffWithinAt

theorem exists_re_holo_sections {M : CxModel P d} {U U' : Set M.Xc} {s s' : M.Xc → (Σ k, ι k) → ℂ}
    (hs : LocSec M U s) (hs' : LocSec M U' s') (B : HermLine ι) {y₀ : M.Xc} (hy : y₀ ∈ U)
    (hy' : y₀ ∈ U') :
    ∃ W : Set M.Xc, IsOpen W ∧ y₀ ∈ W ∧ ∃ G : M.Xc → ℂ, M.atlas.HoloOn W G ∧
      ∀ z ∈ W ∩ U ∩ U', Real.log (B.h (s z)) - Real.log (B.h (s' z)) = (G z).re := by
  classical
  have hz := (hs.sec y₀ hy).1
  have hz' := (hs'.sec y₀ hy').1
  choose i hi using hz'.1
  obtain ⟨c₀, hc₀, hcz⟩ := (M.fibre _ hz' _ hz).1 (by rw [(hs.sec y₀ hy).2, (hs'.sec y₀ hy').2])
  have hn0 : ∀ k, s y₀ ⟨k, i k⟩ ≠ 0 := fun k => by
    rw [hcz]
    exact mul_ne_zero (hc₀ k) (hi k)

  let r : K → ℂ := fun k => s y₀ ⟨k, i k⟩ / s' y₀ ⟨k, i k⟩
  have hr : ∀ k, r k ≠ 0 := fun k => div_ne_zero (hn0 k) (hi k)
  let q : K → M.Xc → ℂ := fun k z => s z ⟨k, i k⟩ / s' z ⟨k, i k⟩ / r k
  have hO : IsOpen (U ∩ U') := hs.isOpen.inter hs'.isOpen
  let W : Set M.Xc := {z | z ∈ U ∩ U' ∧ ∀ k, s' z ⟨k, i k⟩ ≠ 0 ∧ q k z ∈ Complex.slitPlane}
  have hW : IsOpen W := by
    refine isOpen_iff_mem_nhds.mpr fun z hz => ?_
    have hn : ∀ k, ContinuousAt (fun z => s z ⟨k, i k⟩) z := fun k =>
      ((holoOn_continuousOn' (hs.holo _)).mono Set.inter_subset_left).continuousAt (hO.mem_nhds hz.1)
    have hd : ∀ k, ContinuousAt (fun z => s' z ⟨k, i k⟩) z := fun k =>
      ((holoOn_continuousOn' (hs'.holo _)).mono Set.inter_subset_right).continuousAt (hO.mem_nhds hz.1)
    filter_upwards [hO.mem_nhds hz.1, eventually_all.mpr fun k => (hd k).eventually_ne (hz.2 k).1,
      eventually_all.mpr fun k => (((hn k).div (hd k) (hz.2 k).1).div_const _).eventually_mem
        (Complex.isOpen_slitPlane.mem_nhds (hz.2 k).2)] with w h1 h2 h3
    exact ⟨h1, fun k => ⟨h2 k, h3 k⟩⟩
  have hyW : y₀ ∈ W := by
    refine ⟨⟨hy, hy'⟩, fun k => ⟨hi k, ?_⟩⟩
    have : q k y₀ = 1 := div_self (hr k)
    rw [this]
    exact Complex.one_mem_slitPlane
  let G : M.Xc → ℂ := fun z => ∑ k, ((B.a k : ℝ) : ℂ) *
    (Complex.log (q k z) + ((Real.log ‖r k‖ : ℝ) : ℂ))
  refine ⟨W, hW, hyW, G, fun j u hu => ?_, fun z hz => ?_⟩
  · have hzW : (M.atlas.chart j).symm u ∈ W := hu.2
    have hterm : ∀ k, AnalyticAt ℂ (fun u' => ((B.a k : ℝ) : ℂ) *
        (Complex.log (q k ((M.atlas.chart j).symm u')) + ((Real.log ‖r k‖ : ℝ) : ℂ))) u := by
      intro k
      have hn : AnalyticAt ℂ (fun u' => s ((M.atlas.chart j).symm u') ⟨k, i k⟩) u :=
        hs.holo _ j u ⟨hu.1, hzW.1.1⟩
      have hd : AnalyticAt ℂ (fun u' => s' ((M.atlas.chart j).symm u') ⟨k, i k⟩) u :=
        hs'.holo _ j u ⟨hu.1, hzW.1.2⟩
      have hq : AnalyticAt ℂ (fun u' => q k ((M.atlas.chart j).symm u')) u :=
        (hn.div hd (hzW.2 k).1).div analyticAt_const (hr k)
      have hl : AnalyticAt ℂ (Complex.log ∘ fun u' => q k ((M.atlas.chart j).symm u')) u :=
        AnalyticAt.comp (f := fun u' => q k ((M.atlas.chart j).symm u'))
          (analyticAt_clog (hzW.2 k).2) hq
      exact analyticAt_const.mul (hl.add analyticAt_const)
    exact Finset.analyticAt_fun_sum _ fun k _ => hterm k
  · have hzW : z ∈ W := hz.1.1
    have hm := (hs.sec z hzW.1.1).1
    have hm' := (hs'.sec z hzW.1.2).1
    obtain ⟨c, hc, hcy⟩ := (M.fibre _ hm' _ hm).1
      (by rw [(hs.sec z hzW.1.1).2, (hs'.sec z hzW.1.2).2])
    have hpos : 0 < B.h (s' z) := B.pos _ hm'.1
    have hprod : (∏ k, ‖c k‖ ^ B.a k) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.mpr (hc k))
    have hterm : ∀ k, Real.log ‖q k z‖ + Real.log ‖r k‖ = Real.log ‖c k‖ := by
      intro k
      have hck : s z ⟨k, i k⟩ = c k * s' z ⟨k, i k⟩ := by rw [hcy]; rfl
      have hqz : q k z = c k / r k := by
        simp only [q]
        rw [hck, mul_div_assoc, div_self (hzW.2 k).1, mul_one]
      rw [hqz, norm_div, Real.log_div (norm_ne_zero_iff.mpr (hc k)) (norm_ne_zero_iff.mpr (hr k))]
      ring
    have hsm : B.h (s z) = (∏ k, ‖c k‖ ^ B.a k) * B.h (s' z) := by
      rw [hcy]
      exact B.smul c _ hc
    rw [hsm, Real.log_mul hprod hpos.ne', add_sub_cancel_right,
      Real.log_prod fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.mpr (hc k))]
    simp only [G, Complex.re_sum, Complex.re_ofReal_mul, Complex.add_re, Complex.log_re,
      Complex.ofReal_re]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hterm k, Real.log_zpow]

def potOfSections (M : CxModel P d) (B : HermLine ι) : LocPot M.Xc where
  U x := (M.sections x).choose
  isOpen_U x := (M.sections x).choose_spec.1
  mem_U x := (M.sections x).choose_spec.2.1
  φ x y := Real.log (B.h ((M.sections x).choose_spec.2.2.choose y))

end Model

end SecPot

open SecPot in

theorem exists_potential_of_smoothHerm :
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ) (M : CxModel P n) (B : HermLine ι), IsSmoothHerm B → ∃ Φ : LocPot M.Xc, IsPotential M.atlas Φ ∧ ∀ x, ∀ y₀ ∈ (Φ).U x ∩ Set.univ, ∃ U : Set M.Xc, IsOpen U ∧ y₀ ∈ U ∧ U ⊆ (Φ).U x ∩ Set.univ ∧ ∃ s : M.Xc → (Σ k, ι k) → ℂ, (∀ y' ∈ U, s y' ∈ mcPts (P) ∧ M.proj (s y') = y') ∧ (∀ p, M.atlas.HoloOn U fun y' => s y' p) ∧ ∃ G : M.Xc → ℂ, M.atlas.HoloOn U G ∧ ∀ y' ∈ U, (Φ).φ x y' - (fun z => Real.log (B.h z)) (s y') = (G y').re := by
  intro K _ ι _ P n M B hB
  refine ⟨potOfSections M B, ⟨fun x => smoothOn_log_sec (locSec_sections M x) hB, ?_⟩, ?_⟩
  · intro x x' y hy
    exact exists_re_holo_sections (locSec_sections M x) (locSec_sections M x') B hy.1 hy.2
  · intro x y₀ hy
    have hs := locSec_sections M x
    refine ⟨_, hs.isOpen, hy.1, fun z hz => ⟨hz, Set.mem_univ _⟩, _, hs.sec, hs.holo, fun _ => 0,
      fun j u _ => analyticAt_const, fun y' _ => ?_⟩
    simp [potOfSections]

end GlobalTheory.CompanionTheory.Ar.Giv
