import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalBoundaryMetricData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightFamilyExistsOfWeightsT2
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.CoeNonzeroLocusCanonicalEqComplRange

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TopologicalSpace Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.ShFam
open scoped ContDiff

namespace GlobalTheory.ShFam

theorem exists_isDivNorm_of_isProjOver {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {d : ℕ}
    (R : AnRead p σ d) (C : Closeds Y) (hp : IsProjOver p)
    (hC : ReciprocityTheory.AnForm.R.FinalTheorems.EffCartier (Scheme.IdealSheafData.vanishingIdeal C)) : ∃ n, IsDivNorm R C n := by
  obtain ⟨D, hD⟩ := EffCartierData.exists_idealSheaf_eq hC
  obtain ⟨φ, hφ⟩ := Weight.exists_isSmooth_of_isProjOver hp R D.lb D.isLB_lb
  have := CxPts.compactSpace σ hp
  have hs := secVal_mem (p := p) (σ := σ) D.canonical
  have hc : Continuous (φ.nsq (secVal p σ D.canonical)) :=
    hφ.continuous_nsq ⟨hs, fun i => R.holoOn_ev _ _⟩
  obtain ⟨M, hM⟩ := (isCompact_range hc).bddAbove
  have hM' : ∀ y, φ.nsq (secVal p σ D.canonical) y ≤ Real.exp M := fun y =>
    (hM ⟨y, rfl⟩).trans (by linarith [Real.add_one_le_exp M])
  have h0 : ∀ y, 0 ≤ φ.nsq (secVal p σ D.canonical) y * Real.exp (-M) := fun y =>
    mul_nonneg (φ.nsq_nonneg _ y) (Real.exp_pos _).le
  refine ⟨fun y => √(φ.nsq (secVal p σ D.canonical) y * Real.exp (-M)), fun y => ⟨Real.sqrt_nonneg _, ?_⟩,
    fun y => ?_⟩
  · refine Real.sqrt_le_one.2 ?_
    rw [Real.exp_neg, ← div_eq_mul_inv]
    exact (div_le_one (Real.exp_pos _)).2 (hM' y)
  · obtain ⟨i, hi⟩ := D.exists_mem (y.1 (IsLocalRing.closedPoint ℂ))
    obtain ⟨V, hy, hV⟩ := EffCartierData.exists_affine_le hi
    refine ⟨V, _, fun z => φ.φ i z + M, mem_ptsIn.2 hy, hD ▸ D.ideal_idealSheaf V i hV,
      fun j => ((hφ i).mono (ptsIn_mono hV) j).add contDiffOn_const, fun z hz => ?_⟩
    rw [Real.sq_sqrt (h0 z), φ.nsq_eq hs (i := i) (ptsIn_mono hV hz), ev_res hV hz, neg_add, Real.exp_add,
      _root_.mul_assoc]
    rfl

theorem exists_isDivNorm (k : Type) [Field k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (d : ℕ) [SmoothOfRelativeDimension d p]
    (σ : k →+* ℂ) (C : Closeds Y) (hp : IsProjOver p)
    (hC : ReciprocityTheory.AnForm.R.FinalTheorems.EffCartier (Scheme.IdealSheafData.vanishingIdeal C)) :
    ∃ n, IsDivNorm (AnRead.all p σ d) C n :=
  exists_isDivNorm_of_isProjOver _ C hp hC

end GlobalTheory.ShFam
