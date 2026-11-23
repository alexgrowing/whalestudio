import Mathlib
import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
import ReciprocityTheory.AnalyticForms.LeviForms.TailCutA
import ReciprocityTheory.AnalyticForms.PotentialTheory.AnalyticSubsetChartLocal
import ReciprocityTheory.AnalyticForms.PotentialTheory.PotentialContDiffAt
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LoglogQuotNonneg
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ConvergenceStatementHoldsStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalDensityInclusionExclusionStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedDensityNonnegOffNullSetStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ZeroWeightRegularFamilyStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularFamilyEventuallySmoothPshStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PshAddPshPotentialOnOpenStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExpandMIntStatement
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.Giv.SignedConv

theorem zero_member {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (Θ L : LocPot X)
    (s : X → X → ℂ) (C₅ C t₁ : ℝ) (hΘ : IsPotential A Θ) (hΘp : IsPosPot A Θ)
    (hs : ∀ y, logNormSec L s y ≤ 0) (hC₅ : 0 ≤ C₅) (hC : 0 ≤ C) (ht₁ : 0 < t₁)
    (hte : t₁ ≤ Real.exp (-Real.exp 1)) :
    IsSingWeight A L s (LocPot.ofFun 0) 0 C₅ ∧
      IsRegFamily A Θ L s (LocPot.ofFun 0) 0 (fun _ => 0) C t₁ ∧ IsRegFamilyC2 A s 0 (fun _ => 0) :=
  GlobalTheory.T.zero_weight_regular_family A Θ L s C₅ C t₁ hΘ hΘp hs hC₅ hC ht₁ hte

theorem eventually_isPsh {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (Θ L : LocPot X) (s : X → X → ℂ) (th : LocPot X) (ph : X → ℝ) (phT : ℝ → X → ℝ) (C t₀ : ℝ)
    (hΘ : IsPotential A Θ) (hΘp : IsPosPot A Θ) (hth : IsPotential A th)
    (hF : IsRegFamily A Θ L s th ph phT C t₀) :
    ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), A.Smooth (phT t) ∧ IsPsh A (th + LocPot.ofFun (phT t) + Θ) :=
  GlobalTheory.T.regular_family_eventually_smooth_psh A Θ L s th ph phT C t₀ hΘ hΘp hth hF

theorem isPshOn_add_psh {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (U : Set X)
    (P : LocPot X) (f : X → ℝ) (Θ : LocPot X) (hU : IsOpen U) (hP : IsPotential A P)
    (hΘ : IsPotential A Θ) (hf : A.SmoothOn U f) (hPf : IsPshOn A U (P + LocPot.ofFun f))
    (hΘp : IsPsh A Θ) : IsPshOn A U (P + LocPot.ofFun f + Θ) :=
  GlobalTheory.T.psh_add_psh_potential_on_open A U P f Θ hU hP hΘ hf hPf hΘp

theorem expand_mInt {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (A : FinHolAtlas e X) (U : Set X) (P : Fin e → LocPot X) (f : Fin e → X → ℝ) (Θ : LocPot X)
    (g : X → ℝ) (hU : IsOpen U) (hnull : ∀ j, volume ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Uᶜ) = 0)
    (hP : ∀ i, IsPotential A (P i)) (hΘ : IsPotential A Θ) (hf : ∀ i, A.SmoothOn U (f i))
    (hT : ∀ T : Finset (Fin e), MIntegrable A (fun i => (if i ∈ T then P i else LocPot.ofFun 0) +
      LocPot.ofFun (if i ∈ T then f i else 0) + Θ) g) :
    MIntegrable A (fun i => P i + LocPot.ofFun (f i)) g ∧
      mInt A (fun i => P i + LocPot.ofFun (f i)) g = ∑ T : Finset (Fin e), (-1 : ℝ) ^ (e - T.card) *
        mInt A (fun i => (if i ∈ T then P i else LocPot.ofFun 0) +
          LocPot.ofFun (if i ∈ T then f i else 0) + Θ) g :=
  GlobalTheory.T.mixed_integral_inclusion_exclusion_alt A U P f Θ g hU hnull hP hΘ hf hT

theorem isPsh_of_isPosPot {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (Θ : LocPot X) (h : IsPosPot A Θ) : IsPsh A Θ := by
  intro x j y hy w
  by_cases hw : w = 0
  · subst hw; rw [levi_zero]
  · exact (h x j y hy w hw).le

theorem isPshOn_of_isPsh {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (U : Set X) (P : LocPot X) (h : IsPsh A P) : IsPshOn A U P :=
  fun x j y hy w => h x j y ⟨hy.1, hy.2.1⟩ w

theorem smoothOn_of_smooth {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (U : Set X) (f : X → ℝ) (h : A.Smooth f) : A.SmoothOn U f :=
  fun j => (h j).mono (Set.inter_subset_inter_right _ (Set.preimage_mono (Set.subset_univ U)))

theorem isSingWeight_abs {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (L : LocPot X) (s : X → X → ℂ) (th : LocPot X) (ph : X → ℝ) (C₅ : ℝ)
    (hs : ∀ y, logNormSec L s y ≤ 0) (h : IsSingWeight A L s th ph C₅) :
    IsSingWeight A L s th ph |C₅| := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, h2, h3, fun y hy => ?_⟩
  obtain ⟨a, b⟩ := h4 y hy
  have hr : 1 ≤ Real.log (rW L s y) := by
    have h5 := rW_ge L s hs y
    have h6 := Real.log_le_log (Real.exp_pos 1) h5
    rwa [Real.log_exp] at h6
  have h7 := mul_nonneg (sub_nonneg.2 (le_abs_self C₅)) (le_trans zero_le_one hr)
  exact ⟨by nlinarith, b.trans (le_abs_self _)⟩

theorem chart_null {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (L : LocPot X)
    (s : X → X → ℂ) {n : ℕ} (m : Fin n → ℕ) (W : Fin n → Set X) (hS : IsSection A L s)
    (hSNC : IsSNC A L s m W) (j : Fin A.n) :
    volume ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (bdry s)ᶜᶜ) = 0 := by
  rw [compl_compl]
  have hAn : A.IsAnalyticSubset (bdry s) := by
    intro x
    refine ⟨L.U x, L.isOpen_U x, L.mem_U x, 1, fun _ => s x, fun _ => hS.1 x, ?_⟩
    ext z
    constructor
    · rintro ⟨hz, hzU⟩
      exact ⟨hzU, fun _ => (LeviFormBoundaryTopology.bdry_iff hS hzU).1 hz⟩
    · rintro ⟨hzU, hz⟩
      exact ⟨(LeviFormBoundaryTopology.bdry_iff hS hzU).2 (hz 0), hzU⟩
  have := analyticNull A (bdry s) hAn (LeviFormBoundaryTopology.interior_bdry_eq_empty hS hSNC) j
  rwa [Set.inter_comm, (A.chart j).image_source_inter_eq'] at this

theorem convergenceSigned : ConvergenceSignedStatement := by
  intro e X _ _ _ _ _ A Θ L s n m W hΘ hΘp hL hS hSNC hs th ph phT C₅ C t₀ hSW hRF hC2 g gT C₆
    hgc hgb hlim
  have hΘpsh : IsPsh A Θ := isPsh_of_isPosPot A Θ hΘp
  have hUo : IsOpen (bdry s)ᶜ := (LeviFormBoundaryTopology.isClosed_bdry hS).isOpen_compl
  have hnull := chart_null A L s m W hS hSNC
  have hmem : ∀ T : Finset (Fin e),
      (∀ i, IsSingWeight A L s (if i ∈ T then th i else LocPot.ofFun 0)
        (if i ∈ T then ph i else 0) |C₅|) ∧
      (∀ i, IsRegFamily A Θ L s (if i ∈ T then th i else LocPot.ofFun 0)
        (if i ∈ T then ph i else 0) (fun t => if i ∈ T then phT i t else 0) |C|
        (min t₀ (Real.exp (-Real.exp 1)))) ∧
      (∀ i, IsRegFamilyC2 A s (if i ∈ T then ph i else 0) (fun t => if i ∈ T then phT i t else 0)) := by
    intro T
    have hz : ∀ i : Fin e, IsSingWeight A L s (LocPot.ofFun 0) 0 |C₅| ∧
        IsRegFamily A Θ L s (LocPot.ofFun 0) 0 (fun _ => 0) |C| (min t₀ (Real.exp (-Real.exp 1))) ∧
        IsRegFamilyC2 A s 0 (fun _ => 0) := fun i =>
      zero_member A Θ L s |C₅| |C| _ hΘ hΘp hs (abs_nonneg _) (abs_nonneg _)
        (lt_min (hRF i).1 (Real.exp_pos _)) (min_le_right _ _)
    refine ⟨fun i => ?_, fun i => ?_, fun i => ?_⟩ <;> by_cases hi : i ∈ T <;>
      simp only [hi, ↓reduceIte]
    · exact isSingWeight_abs A L s _ _ _ hs (hSW i)
    · exact (hz i).1
    · exact isRegFamily_mono A Θ L s (th i) (ph i) (phT i) C t₀ |C| _ hΘ hΘpsh (hSW i).1 hs (hRF i)
        le_rfl (lt_min (hRF i).1 (Real.exp_pos _)) (min_le_left _ _) (min_le_right _ _)
    · exact (hz i).2.1
    · exact hC2 i
    · exact (hz i).2.2
  have hconv := fun T : Finset (Fin e) => GlobalTheory.T.convergence_statement_holds A Θ L s m W hΘ hΘp hL hS hSNC hs
    (fun i => if i ∈ T then th i else LocPot.ofFun 0) (fun i => if i ∈ T then ph i else 0)
    (fun i t => if i ∈ T then phT i t else 0) |C₅| |C| _ (hmem T).1 (hmem T).2.1 (hmem T).2.2
    g gT C₆ hgc hgb hlim
  have hgcont : ContinuousOn g (bdry s)ᶜ := hlim.continuousOn (Eventually.of_forall hgc).frequently
  have hlimT := fun T : Finset (Fin e) => GlobalTheory.T.mInt_eq_integral_maMeasure A (bdry s)ᶜ
    (fun i => if i ∈ T then th i else LocPot.ofFun 0) (fun i => if i ∈ T then ph i else 0) Θ hUo hnull
    (fun i => ((hmem T).1 i).1) hΘ hΘpsh (fun i => ((hmem T).1 i).2.1)
    (fun i => isPshOn_add_psh A _ _ _ Θ hUo ((hmem T).1 i).1 hΘ ((hmem T).1 i).2.1
      ((hmem T).1 i).2.2.1 hΘpsh) g hgcont (hconv T).2.2.1
  have hexpL := expand_mInt A (bdry s)ᶜ th ph Θ g hUo hnull (fun i => (hSW i).1) hΘ
    (fun i => (hSW i).2.1) (fun T => (hlimT T).1)
  refine ⟨hexpL.1, ?_⟩
  rw [hexpL.2]
  have htend : Tendsto (fun t => ∑ T : Finset (Fin e), (-1 : ℝ) ^ (e - T.card) *
      ∫ y, gT t y ∂maMeasure A (fun i => (if i ∈ T then th i else LocPot.ofFun 0) +
        LocPot.ofFun (if i ∈ T then phT i t else 0) + Θ)) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (∑ T : Finset (Fin e), (-1 : ℝ) ^ (e - T.card) *
        mInt A (fun i => (if i ∈ T then th i else LocPot.ofFun 0) +
          LocPot.ofFun (if i ∈ T then ph i else 0) + Θ) g)) := by
    refine tendsto_finsetSum _ fun T _ => ?_
    rw [(hlimT T).2]
    exact ((hconv T).2.2.2.2).const_mul _
  refine htend.congr' ?_
  have hev : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), (∀ i, A.Smooth (phT i t)) ∧
      ∀ T : Finset (Fin e), (∀ i, A.Smooth (if i ∈ T then phT i t else 0) ∧
        IsPsh A ((if i ∈ T then th i else LocPot.ofFun 0) +
          LocPot.ofFun (if i ∈ T then phT i t else 0) + Θ)) ∧
        Integrable (gT t) (maMeasure A (fun i => (if i ∈ T then th i else LocPot.ofFun 0) +
          LocPot.ofFun (if i ∈ T then phT i t else 0) + Θ)) := by
    refine (eventually_all.2 fun i => ?_).and (eventually_all.2 fun T => ?_)
    · exact (eventually_isPsh A Θ L s (th i) (ph i) (phT i) C t₀ hΘ hΘp (hSW i).1 (hRF i)).mono
        fun t ht => ht.1
    · refine (eventually_all.2 fun i => ?_).and (hconv T).2.2.2.1
      exact eventually_isPsh A Θ L s _ _ _ _ _ hΘ hΘp ((hmem T).1 i).1 ((hmem T).2.1 i)
  filter_upwards [hev] with t ht
  have hmt := fun T : Finset (Fin e) => GlobalTheory.T.mInt_eq_integral_maMeasure A (bdry s)ᶜ
    (fun i => if i ∈ T then th i else LocPot.ofFun 0) (fun i => if i ∈ T then phT i t else 0) Θ hUo hnull
    (fun i => ((hmem T).1 i).1) hΘ hΘpsh (fun i => smoothOn_of_smooth A _ _ ((ht.2 T).1 i).1)
    (fun i => isPshOn_of_isPsh A _ _ ((ht.2 T).1 i).2) (gT t) (hgc t) (ht.2 T).2
  rw [(expand_mInt A (bdry s)ᶜ th (fun i => phT i t) Θ (gT t) hUo hnull (fun i => (hSW i).1) hΘ
    (fun i => smoothOn_of_smooth A _ _ (ht.1 i)) (fun T => (hmt T).1)).2]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [(hmt T).2]

end GlobalTheory.CompanionTheory.Ar.Giv.SignedConv
