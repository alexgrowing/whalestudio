import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaSeriesDataHypothesesBelowMaximalLevel
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.FrecAt
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.MovDXiAtRecStep
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.LocalClassDataOfTrivialStabilizers
import Formalism.LocalToGlobal.GlobalTheory.BaseLatticeSelfDual
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.RepComb
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AnalyticOnNhdOfDifferentiableVc
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TranslateEntireAlgebraic
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open Formalism.L2.KerInert.RepComb Formalism.L2.Th1.H

namespace GlobalTheory

theorem kerTh_entire_algCoef : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ), TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → TaylorLogMetric.IsChi D χ → ∀ {a b : ℕ} (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ) (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (Ξ : Formalism.L2.Col.HomE D.host.E a b → ℂ) (S : Finset ℕ), TaylorLogMetric.admitted D a b N N' → SNum S cl → (∀ x, IntOff S (Ξ x)) → Differentiable ℂ (kerTh B χ SS cl N N' Ξ) ∧ TaylorLogMetric.CoefIn D (kerTh B χ SS cl N N' Ξ) TaylorLogMetric.Qbar := by
  intro D cc δ B χ hcc hδ hχ a b SS cl N N' Ξ S hA hS hΞ
  have hL := lattice_integral_of_facts D.host.E D.what₂.Tau a b (fun τ => TaylorLogMetric.embT D τ) δ D.host.d
    (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹ (Formalism.L2.PairingIndexBounds.F.aaOf D cc) N N' (laFacts_of_adm B hcc hδ hA)
  have hLFG := period_lattice_finitely_generated D.host.E D.what₂.Tau a b (fun τ => TaylorLogMetric.embT D τ) δ (Formalism.L2.PairingIndexBounds.F.aaOf D cc) N N' hA.2.2.2.1
    hA.2.2.1.2.1 (aaOf_fg cc)
  obtain ⟨hi1, hi2, hi3⟩ := finite_index_of_fg D.host.E D.what₂.Tau a b (fun τ => TaylorLogMetric.embT D τ) δ (Formalism.L2.PairingIndexBounds.F.aaOf D cc) SS N N'
    cl hS.1 hLFG
  obtain ⟨n, r, t, hr, ht, hΘ⟩ := theta_coset_kernel D.host.E D.what₂.Tau a b (fun τ => TaylorLogMetric.embT D τ) δ D.host.d
    (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹ (Formalism.L2.PairingIndexBounds.F.aaOf D cc) SS N N' cl S Ξ (B.eNat χ a b N N') hL hi1 hi2 hi3 hS hΞ
  have hfun : kerTh B χ SS cl N N' Ξ =
      fun z => ∑ k, r k * TaylorLogMetric.U D B.tor (t k) (B.eNat χ a b N N') z := by
    funext z
    simp only [Formalism.L2.KerInert.RepComb.U_eq_opU]
    exact congrFun hΘ z
  rw [hfun]
  refine entire_algCoef_comb D r _ (fun k => (hr k).1) fun k => ?_
  obtain ⟨m, hm, hmt⟩ := ht k
  exact TwV.translate_entire_algebraic D cc δ B χ hcc hδ hχ a b N N' hA (t k) ⟨m, hm.1, lambda_in_lattice_pair cc δ N N' hmt⟩

end GlobalTheory
