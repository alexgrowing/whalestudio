import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SignedConvergenceStatementHolds
open MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB

namespace PositivityTheory.Xgp.sq_limit

open GlobalTheory.CompanionTheory.Ar.Giv GlobalTheory.CompanionTheory.Ar.Giv.SignedConv ReciprocityTheory.AnForm.M.FinHolAtlas

theorem continuousOn_logNormSec {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (L : LocPot X) (v : X → X → ℂ) (hL : IsPotential A L) (hv : IsSection A L v) :
    ContinuousOn (logNormSec L v) (bdry v)ᶜ := by
  intro y hy
  refine ContinuousAt.continuousWithinAt ?_
  have hy' : v y y ≠ 0 := hy
  have h1 : ContinuousAt (v y) y := LeviFormBoundaryTopology.continuousAt_of_holoOn A (hv.1 y) (L.mem_U y)
  have h2 : ContinuousAt (L.φ y) y :=
    LeviFormBoundaryTopology.continuousAt_of_smoothOn A (L.isOpen_U y) (hL.1 y) (L.mem_U y)
  have h3 : ContinuousAt (fun z => Real.log (‖v y z‖ * Real.exp (-L.φ y z))) y := by
    refine ContinuousAt.log (h1.norm.mul (Real.continuous_exp.continuousAt.comp h2.neg)) ?_
    exact mul_ne_zero (norm_ne_zero_iff.2 hy') (Real.exp_pos _).ne'
  refine h3.congr ?_
  filter_upwards [(L.isOpen_U y).mem_nhds (L.mem_U y)] with z hz
  unfold logNormSec
  rw [hv.2 y z z ⟨hz, L.mem_U z⟩]

theorem smoothOn_mono {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    {U V : Set X} {f : X → ℝ} (hUV : U ⊆ V) (h : A.SmoothOn V f) : A.SmoothOn U f :=
  fun j => (h j).mono (Set.inter_subset_inter_right _ (Set.preimage_mono hUV))

theorem isPshOn_mono {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    {U V : Set X} {P : LocPot X} (hUV : U ⊆ V) (h : IsPshOn A V P) : IsPshOn A U P :=
  fun x j y hy w => h x j y ⟨hy.1, hy.2.1, hUV hy.2.2⟩ w

theorem unifIntSigned (hU : UnifIntStatement) {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X]
    [T2Space X] (A : FinHolAtlas e X) (Θ L : LocPot X) (s : X → X → ℂ) {n : ℕ}
    (m : Fin n → ℕ) (W : Fin n → Set X) (hΘ : IsPotential A Θ) (hΘp : IsPosPot A Θ)
    (hL : IsPotential A L) (hS : IsSection A L s) (hSNC : IsSNC A L s m W)
    (hs : ∀ y, logNormSec L s y ≤ 0) (L' : LocPot X) (v : X → X → ℂ) (Dg : Set X)
    (hL' : IsPotential A L') (hv : IsSection A L' v) (hvS : IsSNC A L' v ![1] ![Dg])
    (hsv : IsSNC A (L + L') (fun x y => s x y * v x y) (Fin.snoc m 1) (Fin.snoc W Dg))
    (hvn : ∀ y, logNormSec L' v y ≤ 0)
    (th : Fin e → LocPot X) (ph : Fin e → X → ℝ) (phT : Fin e → ℝ → X → ℝ) (C₅ C t₀ : ℝ)
    (hSW : ∀ i, IsSingWeight A L s (th i) (ph i) C₅)
    (hRF : ∀ i, IsRegFamily A Θ L s (th i) (ph i) (phT i) C t₀)
    (hC2 : ∀ i, IsRegFamilyC2 A s (ph i) (phT i)) :
    MIntegrable A (fun i => th i + LocPot.ofFun (ph i)) (logNormSec L' v) ∧
      (∀ᶠ t in 𝓝[>] (0 : ℝ), MIntegrable A (fun i => th i + LocPot.ofFun (phT i t)) (logNormSec L' v)) ∧
      Tendsto (fun t => mInt A (fun i => th i + LocPot.ofFun (phT i t)) (logNormSec L' v)) (𝓝[>] 0)
        (𝓝 (mInt A (fun i => th i + LocPot.ofFun (ph i)) (logNormSec L' v))) := by
  letI : MeasurableSpace X := borel X
  haveI : BorelSpace X := ⟨rfl⟩
  set g := logNormSec L' v with hg
  have hΘpsh : IsPsh A Θ := isPsh_of_isPosPot A Θ hΘp
  set U : Set X := (bdry s)ᶜ ∩ (bdry v)ᶜ with hUdef
  have hUo : IsOpen U := (LeviFormBoundaryTopology.isClosed_bdry hS).isOpen_compl.inter
    (LeviFormBoundaryTopology.isClosed_bdry hv).isOpen_compl
  have hUs : U ⊆ (bdry s)ᶜ := Set.inter_subset_left
  have hnull : ∀ j, volume ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Uᶜ) = 0 := by
    intro j
    rw [hUdef, Set.compl_inter, Set.preimage_union, Set.inter_union_distrib_left]
    exact measure_union_null (chart_null A L s m W hS hSNC j) (chart_null A L' v _ _ hv hvS j)
  have hgc : ContinuousOn g U := (continuousOn_logNormSec A L' v hL' hv).mono Set.inter_subset_right
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
  have hconv : ∀ T : Finset (Fin e),
      Integrable g (maMeasure A (fun i => (if i ∈ T then th i else LocPot.ofFun 0) +
        LocPot.ofFun (if i ∈ T then ph i else 0) + Θ)) ∧
      (∀ᶠ t in 𝓝[>] (0 : ℝ), Integrable g (maMeasure A (fun i => (if i ∈ T then th i else LocPot.ofFun 0) +
        LocPot.ofFun (if i ∈ T then phT i t else 0) + Θ))) ∧
      Tendsto (fun t => ∫ y, g y ∂maMeasure A (fun i => (if i ∈ T then th i else LocPot.ofFun 0) +
        LocPot.ofFun (if i ∈ T then phT i t else 0) + Θ)) (𝓝[>] 0)
        (𝓝 (∫ y, g y ∂maMeasure A (fun i => (if i ∈ T then th i else LocPot.ofFun 0) +
          LocPot.ofFun (if i ∈ T then ph i else 0) + Θ))) := by
    intro T
    obtain ⟨h1, h2, h3⟩ := hU A Θ L s m W hΘ hΘp hL hS hSNC hs L' v Dg hL' hv hvS hsv hvn
      (fun i => if i ∈ T then th i else LocPot.ofFun 0) (fun i => if i ∈ T then ph i else 0)
      (fun i t => if i ∈ T then phT i t else 0) |C₅| |C| _ (hmem T).1 (hmem T).2.1 (hmem T).2.2
    refine ⟨integrable_neg_iff.1 h1, h2.mono fun t ht => integrable_neg_iff.1 ht, ?_⟩
    simp only [integral_neg] at h3
    simpa only [neg_neg] using h3.neg
  have hlimT := fun T : Finset (Fin e) => GlobalTheory.T.mInt_eq_integral_maMeasure A U
    (fun i => if i ∈ T then th i else LocPot.ofFun 0) (fun i => if i ∈ T then ph i else 0) Θ hUo hnull
    (fun i => ((hmem T).1 i).1) hΘ hΘpsh (fun i => smoothOn_mono A hUs ((hmem T).1 i).2.1)
    (fun i => isPshOn_add_psh A _ _ _ Θ hUo ((hmem T).1 i).1 hΘ (smoothOn_mono A hUs ((hmem T).1 i).2.1)
      (isPshOn_mono A hUs ((hmem T).1 i).2.2.1) hΘpsh) g hgc (hconv T).1
  have hexpL := expand_mInt A U th ph Θ g hUo hnull (fun i => (hSW i).1) hΘ
    (fun i => smoothOn_mono A hUs (hSW i).2.1) (fun T => (hlimT T).1)
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), (∀ i, A.Smooth (phT i t)) ∧
      ∀ T : Finset (Fin e), (∀ i, A.Smooth (if i ∈ T then phT i t else 0) ∧
        IsPsh A ((if i ∈ T then th i else LocPot.ofFun 0) +
          LocPot.ofFun (if i ∈ T then phT i t else 0) + Θ)) ∧
        Integrable g (maMeasure A (fun i => (if i ∈ T then th i else LocPot.ofFun 0) +
          LocPot.ofFun (if i ∈ T then phT i t else 0) + Θ)) := by
    refine (eventually_all.2 fun i => ?_).and (eventually_all.2 fun T => ?_)
    · exact (eventually_isPsh A Θ L s (th i) (ph i) (phT i) C t₀ hΘ hΘp (hSW i).1 (hRF i)).mono
        fun t ht => ht.1
    · refine (eventually_all.2 fun i => ?_).and (hconv T).2.1
      exact eventually_isPsh A Θ L s _ _ _ _ _ hΘ hΘp ((hmem T).1 i).1 ((hmem T).2.1 i)
  have hreg : ∀ᶠ t in 𝓝[>] (0 : ℝ), MIntegrable A (fun i => th i + LocPot.ofFun (phT i t)) g ∧
      ∑ T : Finset (Fin e), (-1 : ℝ) ^ (e - T.card) *
        ∫ y, g y ∂maMeasure A (fun i => (if i ∈ T then th i else LocPot.ofFun 0) +
          LocPot.ofFun (if i ∈ T then phT i t else 0) + Θ) =
        mInt A (fun i => th i + LocPot.ofFun (phT i t)) g := by
    filter_upwards [hev] with t ht
    have hmt := fun T : Finset (Fin e) => GlobalTheory.T.mInt_eq_integral_maMeasure A U
      (fun i => if i ∈ T then th i else LocPot.ofFun 0) (fun i => if i ∈ T then phT i t else 0) Θ hUo hnull
      (fun i => ((hmem T).1 i).1) hΘ hΘpsh (fun i => smoothOn_of_smooth A _ _ ((ht.2 T).1 i).1)
      (fun i => isPshOn_of_isPsh A _ _ ((ht.2 T).1 i).2) g hgc (ht.2 T).2
    have hx := expand_mInt A U th (fun i => phT i t) Θ g hUo hnull (fun i => (hSW i).1) hΘ
      (fun i => smoothOn_of_smooth A _ _ (ht.1 i)) (fun T => (hmt T).1)
    refine ⟨hx.1, ?_⟩
    rw [hx.2]
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [(hmt T).2]
  refine ⟨hexpL.1, hreg.mono fun t ht => ht.1, ?_⟩
  rw [hexpL.2]
  refine Tendsto.congr' (hreg.mono fun t ht => ht.2) ?_
  refine tendsto_finsetSum _ fun T _ => ?_
  rw [(hlimT T).2]
  exact ((hconv T).2.2).const_mul _

theorem singular_part (hI : Inputs) {d : ℕ} {σ : Type} [Fintype σ] {SY : AnSys (d + 1) σ} {a₀ : σ}
    {ε : σ → ℤ} (Q : AnSq SY a₀ ε) (w : Fin (d + 2) → Option σ) :
    MIntegrable Q.SW.A (fun r => Q.SW.potH (w r)) (logNormSec Q.L' Q.v) ∧
      (∀ᶠ t in 𝓝[>] (0 : ℝ), MIntegrable Q.SW.A (fun r => Q.SW.potT (w r) t) (logNormSec Q.L' Q.v)) ∧
      Tendsto (fun t => mInt Q.SW.A (fun r => Q.SW.potT (w r) t) (logNormSec Q.L' Q.v)) (𝓝[>] 0)
        (𝓝 (mInt Q.SW.A (fun r => Q.SW.potH (w r)) (logNormSec Q.L' Q.v))) :=
  unifIntSigned hI.unifInt Q.SW.A Q.SW.Θ Q.SW.L Q.SW.s Q.SW.m Q.SW.W Q.SW.potΘ Q.SW.posΘ Q.SW.potL
    Q.SW.sec Q.SW.snc Q.SW.norm_le Q.L' Q.v Q.Dg Q.potL' Q.secv Q.sncv Q.sncsv Q.normv
    (fun r => Q.SW.th (w r)) (fun r => Q.SW.ph (w r)) (fun r => Q.SW.phT (w r)) Q.SW.C₅ Q.SW.C Q.SW.t₀
    (fun r => Q.SW.sing (w r)) (fun r => Q.SW.reg (w r)) (fun r => Q.SW.c2 (w r))

end PositivityTheory.Xgp.sq_limit
