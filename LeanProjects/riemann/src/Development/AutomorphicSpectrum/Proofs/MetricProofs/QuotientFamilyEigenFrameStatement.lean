import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.QuotientFamilyEigenFrame
import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quotient_family_eigen_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g g' : ℕ) (Λ Λ' : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] [AddCommGroup Λ'] [Module (𝓞 E) Λ'] (R : RiemLat E g Λ) (R' : RiemLat E g' Λ') (q : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)) (I : Submodule (𝓞 E) Λ) (s : 𝓞 E →+* ℂ) (r k : ℕ) (v : Fin r → Λ) (x : Fin k → Fin g → ℂ), IsIsoSub R.form I → IsNzFamily I r v → LinearMap.ker q = Submodule.span ℂ (R.P '' I) → (∀ y z, (∀ u ∈ I, R.ip (R.P u) y = 0) → R'.ip (q y) (q z) = R.ip y z) → (∀ j, x j ∈ eigSp R.B s) → (R.gram (Fin.append (fun a => eigComp R.B s (R.P (v a))) x)).det = (R.gram (fun a => eigComp R.B s (R.P (v a)))).det * (R'.gram (fun j => q (x j))).det := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.SchurGram.gram_append_eq | exact GlobalTheory.CompanionTheory.Ar.Cusp.SchurGram.gram_append_eq | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.SchurGram.gram_append_eq <;> assumption)
