import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrthogonalHaarMeasure
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open Ad3.R (G2 Jd md KA lc)
open scoped NumberField.AdeleRing ValuativeRel
open GlobalTheory.CompanionTheory.GL2Factorization
open GlobalTheory.CompanionTheory.GL2Factorization.Abs

noncomputable section

namespace GlobalTheory.CompanionTheory.GL2Factorization.Abs.OrthogonalTorusIntegral

theorem val_emb : MeasurableEmbedding (Units.val : ℝˣ → ℝ) := by
  refine ⟨fun _ _ h => Units.ext h, comap_measurable _, ?_⟩
  rintro _ ⟨B, hB, rfl⟩
  have : Units.val '' (Units.val ⁻¹' B : Set ℝˣ) = B ∩ {0}ᶜ := by
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨hu, by simp⟩
    · rintro ⟨hx, hx0⟩
      exact ⟨Units.mk0 x hx0, hx, rfl⟩
  rw [this]
  exact hB.inter (measurableSet_singleton _).compl

theorem sigmaFinite_mulR : SigmaFinite mulR := by
  set nu : Measure ℝ := volume.withDensity fun x : ℝ => ENNReal.ofReal |x|⁻¹ with hnu
  have hs : SigmaFinite nu := SigmaFinite.withDensity_ofReal _
  have hmap : Measure.map (Units.val : ℝˣ → ℝ) mulR = nu.restrict (Set.range Units.val) :=
    val_emb.map_comap nu
  refine SigmaFinite.of_map _ val_emb.measurable.aemeasurable ?_
  rw [hmap]
  infer_instance

instance : SFinite mulR := by
  haveI := sigmaFinite_mulR
  infer_instance

instance : SFinite rho := by
  unfold rho
  infer_instance

end GlobalTheory.CompanionTheory.GL2Factorization.Abs.OrthogonalTorusIntegral
