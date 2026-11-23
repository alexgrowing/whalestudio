import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsoluteThetaIntegralLeContinuousSeminorm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LintegralFundamentalDomainLeOfMeetsOrbits
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.AbsThetaQuot.absThetaInt_le_setLIntegral_of_cover : ∀ (D : D7) (V : HSp D) (n : ℕ) (ν : Measure (GA D V)), ν.IsHaarMeasure → ∀ φ : Mx D V.rank n → ℂ, Continuous φ → ∀ S : Set (GA D V), MeasurableSet S → (∀ g, ∃ γ ∈ GQ V, ∃ s ∈ S, g = γ * s) → GlobalTheory.SiegelFormula.absThetaInt V ν φ ≤ ∫⁻ g in S, GlobalTheory.SiegelFormula.absTheta V φ g ∂ν := by
  intro D V n ν hν φ hφ S hS hcov
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  have hScov : ∀ g, ∃ γ ∈ GQ V, γ * g ∈ S := fun g => by
    obtain ⟨γ, hγ, s, hs, e⟩ := hcov g
    refine ⟨γ⁻¹, inv_mem hγ, ?_⟩
    rw [e, inv_mul_cancel_left]
    exact hs
  have hleft := GlobalTheory.SiegelFormula.leftInv_absTheta V φ
  have e1 : GlobalTheory.SiegelFormula.absThetaInt V ν φ =
      ∫⁻ g in GlobalTheory.AutomorphicL2Unitary.stdDom (GQ V), GlobalTheory.SiegelFormula.absTheta V φ g ∂ν := by
    rw [GlobalTheory.SiegelFormula.absThetaInt, GlobalTheory.AutomorphicL2Unitary.autMeasure, GlobalTheory.AutomorphicL2Unitary.quotMeasure,
      lintegral_map (GlobalTheory.AbsThetaSemi.measurable_descend_absTheta V hφ) GlobalTheory.AutomorphicL2Unitary.measurable_mk]
    exact lintegral_congr fun g => hleft.descend_mk g
  rw [e1]
  exact GlobalTheory.lintegral_fundamentalDomain_le_of_meets_orbits (GQ V) ν
    (GlobalTheory.AutomorphicL2Unitary.isFundamentalDomain_stdDom (GQ V) ν) hS hScov
    (GlobalTheory.AbsThetaSemi.measurable_absTheta V hφ) (fun γ hγ g => hleft γ hγ g)
