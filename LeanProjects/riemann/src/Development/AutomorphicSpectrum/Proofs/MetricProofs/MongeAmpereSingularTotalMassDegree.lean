import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsTwiceDifferentiableAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.CompRightEqZero
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem AnSys.eventually_mInt_potT {e : ℕ} {σ : Type} (S : AnSys e σ) (w : Fin e → σ) :
    ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      mInt S.A (fun i => S.potT (w i) t) (fun _ => 1) = S.degNum w := by
  have hsm : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), ∀ i, S.A.Smooth (S.phT (w i) t) := by
    refine Filter.eventually_all.2 fun i => ?_
    obtain ⟨h0, -, hreg⟩ := S.reg (w i)
    filter_upwards [Ioc_mem_nhdsGT h0] with t ht
    exact (hreg t ht.1 ht.2).1
  filter_upwards [hsm] with t ht
  exact massIndep S.A (fun i => S.th (w i)) (fun i => S.phT (w i) t)
    (fun i => (S.sing (w i)).1) ht

theorem AnSys.abs_one_le_log_rW {e : ℕ} {σ : Type} (S : AnSys e σ) (y : S.X) :
    |(1 : ℝ)| ≤ 1 * Real.log (rW S.L S.s y) := by
  have h : Real.exp 1 ≤ rW S.L S.s y := by
    have := S.norm_le y
    unfold rW
    linarith
  have h1 : (1 : ℝ) ≤ Real.log (rW S.L S.s y) :=
    (Real.le_log_iff_exp_le (lt_of_lt_of_le (Real.exp_pos 1) h)).2 h
  simpa using h1

theorem AnSys.mIntegrable_potH_and_mInt_eq_degNum :
    ConvergenceSignedStatement → ∀ (e : ℕ) (σ : Type) (S : AnSys e σ) (w : Fin e → σ),
      MIntegrable S.A (fun i => S.potH (w i)) (fun _ => 1) ∧
        mInt S.A (fun i => S.potH (w i)) (fun _ => 1) = S.degNum w := by
  intro hC e σ S w
  letI : MeasurableSpace S.X := borel S.X
  haveI : BorelSpace S.X := ⟨rfl⟩
  have hlim := hC S.A S.Θ S.L S.s S.m S.W S.potΘ S.posΘ S.potL S.sec S.snc S.norm_le
    (fun i => S.th (w i)) (fun i => S.ph (w i)) (fun i => S.phT (w i)) S.C₅ S.C S.t₀
    (fun i => S.sing (w i)) (fun i => S.reg (w i)) (fun i => S.c2 (w i))
    (fun _ => 1) (fun _ _ => 1) 1 (fun _ => continuousOn_const)
    (fun _ y _ => S.abs_one_le_log_rW y)
    (TendstoUniformlyOn.tendstoLocallyUniformlyOn (by
      refine Metric.tendstoUniformlyOn_iff.2 fun ε hε => ?_
      exact Filter.Eventually.of_forall fun _ _ _ => by simpa using hε))
  refine ⟨hlim.1, ?_⟩
  have hT : Tendsto (fun t => mInt S.A (fun i => S.potT (w i) t) (fun _ => 1))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (mInt S.A (fun i => S.potH (w i)) (fun _ => 1))) :=
    hlim.2
  have hc : Tendsto (fun t => mInt S.A (fun i => S.potT (w i) t) (fun _ => 1))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (S.degNum w)) :=
    tendsto_const_nhds.congr' ((S.eventually_mInt_potT w).mono fun _ h => h.symm)
  exact tendsto_nhds_unique hT hc

end GlobalTheory.CompanionTheory.Ar.PB
