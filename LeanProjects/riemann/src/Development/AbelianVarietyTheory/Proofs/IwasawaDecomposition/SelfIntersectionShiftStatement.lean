import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SelfIntersectionShift
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ArBirational
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.self_intersection_shift : GlobalTheory.Published.ArCalc → GlobalTheory.Published.ArDegree → ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (M : TrueGeo.Model Y) (L : HermLB M.p) (Δ : Y.Dv) (r : (L.B.pull M.j).ι → Y.Fnˣ), Presents Δ (L.B.pull M.j) r → ∀ (t : (𝓞 F →+* ℂ) → ℝ) (ht : ∀ σ, t ((starRingEnd ℂ).comp σ) = t σ) (a : ℝ), (haveI := M.ar.isIntegral; L.IsSelfInter a) → (haveI := M.ar.isIntegral; (L.shift t ht).IsSelfInter (a + ((Y.dim : ℝ) + 1) * (Y.inter (fun _ => Δ) : ℝ) * ∑ σ : F →+* ℂ, t (σ.comp (algebraMap (𝓞 F) F)))) := by
  first | exact @GlobalTheory.ModelShift.isSelfInter_shift_model | exact GlobalTheory.ModelShift.isSelfInter_shift_model | (intros; apply GlobalTheory.ModelShift.isSelfInter_shift_model <;> assumption)
