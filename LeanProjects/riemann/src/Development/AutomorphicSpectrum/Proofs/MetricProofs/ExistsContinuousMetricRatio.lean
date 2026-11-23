import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PositionPot
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import Development.AutomorphicSpectrum.Proofs.MetricProofs.VerticalFactorSmoothHermitianMetricStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Cusp.Descent

open ReciprocityTheory.AnForm.M

section General
variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]

theorem holoOn_continuousOn {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X} {U : Set X}
    {f : X → ℂ} (hU : IsOpen U) (h : A.HoloOn U f) : ContinuousOn f U := by
  intro t ht
  obtain ⟨j, hj⟩ := A.cover t
  have h1 : AnalyticAt ℂ (f ∘ (A.chart j).symm) (A.chart j t) :=
    h j _ ⟨(A.chart j).map_source hj, by simpa [(A.chart j).left_inv hj] using ht⟩
  have h2 : ContinuousAt ((f ∘ (A.chart j).symm) ∘ A.chart j) t :=
    ContinuousAt.comp h1.continuousAt ((A.chart j).continuousAt hj)
  have h3 : ((f ∘ (A.chart j).symm) ∘ A.chart j) =ᶠ[𝓝 t] f := by
    filter_upwards [(A.chart j).open_source.mem_nhds hj] with u hu
    simp [(A.chart j).left_inv hu]
  exact (h2.congr h3).continuousWithinAt

theorem exists_continuous_descent {P : Ideal (MRing J)} {d : ℕ} (M : CxModel P d)
    (F : ((Σ k, J k) → ℂ) → ℝ) (hF : ContinuousOn F {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0})
    (hinv : ∀ (c : K → ℂ), (∀ k, c k ≠ 0) → ∀ z ∈ mcPts P, F (torusSmul c z) = F z) :
    ∃ κ : M.Xc → ℝ, Continuous κ ∧ ∀ z ∈ mcPts P, κ (M.proj z) = F z := by
  choose r hr hpr using M.surj
  have key : ∀ z ∈ mcPts P, F (r (M.proj z)) = F z := by
    intro z hz
    obtain ⟨c, hc, e⟩ := (M.fibre _ (hr _) z hz).1 (hpr _)
    calc F (r (M.proj z)) = F (torusSmul c (r (M.proj z))) := (hinv c hc _ (hr _)).symm
      _ = F z := by rw [← e]
  refine ⟨fun x => F (r x), ?_, key⟩
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨U, hU, hx, s, hs, hh⟩ := M.sections x
  have hsc : ContinuousOn s U := continuousOn_pi.2 fun p => holoOn_continuousOn hU (hh p)
  have hcomp : ContinuousOn (F ∘ s) U := hF.comp hsc fun y hy => (hs y hy).1.1
  refine (hcomp.continuousAt (hU.mem_nhds hx)).congr ?_
  filter_upwards [hU.mem_nhds hx] with y hy
  have h := key (s y) (hs y hy).1
  rw [(hs y hy).2] at h
  exact h.symm

theorem log_h_torusSmul (A : HermLine J) {c : K → ℂ} (hc : ∀ k, c k ≠ 0) {z : (Σ k, J k) → ℂ}
    (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    Real.log (A.h (torusSmul c z)) = (∑ k, (A.a k : ℝ) * Real.log ‖c k‖) + Real.log (A.h z) := by
  have h1 : A.h (torusSmul c z) = (∏ k, ‖c k‖ ^ A.a k) * A.h z := A.smul c z hc
  have h2 : ∀ k, ‖c k‖ ^ A.a k ≠ 0 := fun k => zpow_ne_zero _ (norm_ne_zero_iff.mpr (hc k))
  rw [h1, Real.log_mul (Finset.prod_ne_zero_iff.mpr fun k _ => h2 k) (A.pos z hz).ne',
    Real.log_prod (fun k _ => h2 k)]
  simp only [Real.log_zpow]

theorem log_h_continuousOn {A : HermLine J} (hA : IsSmoothHerm A) :
    ContinuousOn (fun z => Real.log (A.h z)) {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} :=
  ContinuousOn.log hA.continuousOn fun z hz => (A.pos z hz).ne'

end General

theorem logDiff_descends : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W) (Hd : HodgeData D) (M : XModel D) (S : LogLogRegularisationSetting M D.Xo (muLine Hd)) (B : ℕ) (Nb : HermLine J), IsSmoothHerm Nb → Nb.a = muTwDeg Hd B → ∃ κ : M.Xc → ℝ, Continuous κ ∧ ∀ z ∈ mcPts (mCoordIdeal D.y), κ (M.proj z) = Real.log (Nb.h z) - Real.log (S.ref.h z) - ∑ p ∈ D.SB B, Real.log (D.vertFactor p z) := by
  intro K _ J _ II Ψ _ Ω _ _ W _ _ D Hd M S B Nb hNb hdeg
  have hA : ∀ p, ∃ A : HermLine J, p ∈ D.SB B → A.a = D.vdeg p ∧ IsSmoothHerm A ∧
      ∀ z ∈ mcPts (mCoordIdeal D.y), A.h z = D.vertFactor p z := by
    intro p
    by_cases hp : p ∈ D.SB B
    · obtain ⟨A, h1, h2, -, h3⟩ :=
        (GlobalTheory.T.vertical_factor_smooth_hermitian_metric K J II Ψ Ω W D p (Finset.mem_of_mem_filter p hp)).1
      exact ⟨A, fun _ => ⟨h1, h2, h3⟩⟩
    · exact ⟨S.ref, fun h => absurd h hp⟩
  choose A hA using hA
  have hdegk : ∀ k, (Nb.a k : ℝ) = (S.ref.a k : ℝ) + ∑ p ∈ D.SB B, ((A p).a k : ℝ) := by
    intro k
    have href : S.ref.a = Hd.aMu := S.ref_deg
    have hs : ∑ p ∈ D.SB B, (A p).a k = ∑ p ∈ D.SB B, D.vdeg p k :=
      Finset.sum_congr rfl fun p hp => by rw [(hA p hp).1]
    have : Nb.a k = S.ref.a k + ∑ p ∈ D.SB B, (A p).a k := by
      rw [hdeg, href, hs]
      simp [muTwDeg, Finset.sum_apply]
    rw [this]
    push_cast
    rfl
  obtain ⟨κ, hκ, hκe⟩ := exists_continuous_descent M
    (fun z => Real.log (Nb.h z) - Real.log (S.ref.h z) - ∑ p ∈ D.SB B, Real.log ((A p).h z))
    (((log_h_continuousOn hNb).sub (log_h_continuousOn S.ref_smooth)).sub
      (continuousOn_finset_sum _ fun p hp => log_h_continuousOn (hA p hp).2.1))
    (by
      intro c hc z hz
      have hb := hz.1
      simp only [log_h_torusSmul _ hc hb, Finset.sum_add_distrib]
      rw [Finset.sum_comm (s := D.SB B)]
      simp only [hdegk, add_mul, Finset.sum_add_distrib, Finset.sum_mul]
      ring)
  refine ⟨κ, hκ, fun z hz => ?_⟩
  rw [hκe z hz]
  congr 1
  exact Finset.sum_congr rfl fun p hp => by rw [(hA p hp).2.2 z hz]

end GlobalTheory.CompanionTheory.Ar.Cusp.Descent
