import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsTestZero
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CompanionTheory.SmoothRep
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.SmoothRep

theorem convR_lift_splitCentre_mul (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ)
    (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (f : GA E a → ℂ)
    (F : L2 (latticeGL E a) μ) (hF : F ∈ L2cusp μ) (t : ℝ) (x : GA E a) :
    convR μ f (lift (latticeGL E a) F) (splitCentre E a t * x) =
      convR μ f (lift (latticeGL E a) F) x := by
  have hR := R_splitCentre (μ := μ) t hF
  have h1 := GlobalTheory.AutomorphicL2Unitary.lift_R (Γ := latticeGL E a) (μ := μ) (splitCentre E a t) F
  rw [hR] at h1
  have h2 := (measurePreserving_mul_left μ x).quasiMeasurePreserving.ae_eq h1
  unfold convR
  refine integral_congr_ae ?_
  filter_upwards [h2] with y hy
  have e : splitCentre E a t * x * y = x * y * splitCentre E a t := by
    rw [splitCentre_comm t x, mul_assoc, splitCentre_comm t y, ← mul_assoc]
  rw [e]
  exact congrArg (f y * ·) hy.symm

end GlobalTheory.CompanionTheory.SmoothRep
