import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrT
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.OmAtSmulRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramAtPosDef
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntPull
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AnalyticOnNhdOfDifferentiableVc
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

noncomputable section

namespace GlobalTheory.EntireJetUniq

open Formalism.L2.KerInert.PullbackComparison in

theorem eq_of_applyAt0_monomial_eq : ∀ {D : D7} {N N' : ℕ} (Φ Ψ : Formalism.MainNotions.TaylorLogMetric.VC D N N' → ℂ), Differentiable ℂ Φ → Differentiable ℂ Ψ → (∀ k : Formalism.MainNotions.GL3Theta.Idx D N N' →₀ ℕ, Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) Φ = Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) Ψ) → Φ = Ψ := by
  intro D N N' Φ Ψ hΦ hΨ h
  classical
  have aΦ := GlobalTheory.analyticOnNhd_of_differentiable_vc Φ hΦ
  have aΨ := GlobalTheory.analyticOnNhd_of_differentiable_vc Ψ hΨ
  have hmono : ∀ (k : Formalism.MainNotions.GL3Theta.Idx D N N' →₀ ℕ) (G : Formalism.MainNotions.TaylorLogMetric.VC D N N' → ℂ),
      Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) G =
        (k.prod fun _ n => (n.factorial : ℂ)) * Formalism.MainNotions.TaylorLogMetric.taylor D G k := by
    intro k G
    unfold Formalism.MainNotions.GL3Theta.applyAt0
    rw [MvPolynomial.support_monomial, if_neg one_ne_zero, Finset.sum_singleton, MvPolynomial.coeff_monomial,
      if_pos rfl, one_mul]
  have ht : ∀ α : Formalism.MainNotions.TaylorLogMetric.Mono D N N', Formalism.MainNotions.TaylorLogMetric.taylor D Φ α = Formalism.MainNotions.TaylorLogMetric.taylor D Ψ α := by
    intro α
    have h1 := h α
    rw [hmono, hmono] at h1
    have hne : (α.prod fun _ n => (n.factorial : ℂ)) ≠ 0 := by
      rw [Finsupp.prod]
      exact Finset.prod_ne_zero_iff.2 fun _ _ => Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
    exact mul_left_cancel₀ hne h1
  have hd : ∀ (n : ℕ) (z : Formalism.MainNotions.TaylorLogMetric.VC D N N'),
      iteratedFDeriv ℂ n Φ 0 (fun _ => z) = iteratedFDeriv ℂ n Ψ 0 (fun _ => z) := by
    intro n z
    rw [iter_expand, iter_expand]
    refine Finset.sum_congr rfl fun κ _ => ?_
    rw [iter_eq_taylor D Φ aΦ κ (ak D κ) (toMultiset_ak D κ).symm,
      iter_eq_taylor D Ψ aΨ κ (ak D κ) (toMultiset_ak D κ).symm, ht]
  obtain ⟨p, r, hp⟩ := aΦ 0 (Set.mem_univ _)
  obtain ⟨q, s, hq⟩ := aΨ 0 (Set.mem_univ _)
  refine aΦ.eq_of_eventuallyEq aΨ (z₀ := 0) ?_
  have hball : Metric.eball (0 : Formalism.MainNotions.TaylorLogMetric.VC D N N') (min r s) ∈ nhds 0 :=
    Metric.eball_mem_nhds 0 (lt_min hp.r_pos hq.r_pos)
  filter_upwards [hball] with y hy
  have hy1 : y ∈ Metric.eball (0 : Formalism.MainNotions.TaylorLogMetric.VC D N N') r :=
    Metric.eball_subset_eball (min_le_left _ _) hy
  have hy2 : y ∈ Metric.eball (0 : Formalism.MainNotions.TaylorLogMetric.VC D N N') s :=
    Metric.eball_subset_eball (min_le_right _ _) hy
  have s1 := hp.hasSum_iteratedFDeriv hy1
  have s2 := hq.hasSum_iteratedFDeriv hy2
  simp only [zero_add] at s1 s2
  simp only [hd] at s1
  exact s1.unique s2

end GlobalTheory.EntireJetUniq
