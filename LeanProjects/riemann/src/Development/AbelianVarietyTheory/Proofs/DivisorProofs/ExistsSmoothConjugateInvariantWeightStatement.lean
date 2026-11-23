import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothConjugateInvariantWeight
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CombinedAdelicMetricIdentityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducedOfPositiveNorms
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_smooth_conjugate_invariant_weight : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (Mb : Adl (cxSt F) Y) (ι : Type) [Fintype ι] (ρ : ι → Adl (cxSt F) Y) (t : ι → ℝ) (g : ∀ σ : F →+* ℂ, Pts Y σ → ℝ), IsComb Mb ρ t g → (∀ σ, (cxSt F).mSmooth Y σ Mb.D (Mb.m σ)) → ∀ (M : TrueGeo.Model Y) (L : ι → HermLB M.p) (m : ℕ+), (∀ i, (ρ i).Induced M (L i) m 0) → ∃ w : ∀ σ : 𝓞 F →+* ℂ, CxPts M.p σ → ℝ, (∀ σ y, CInfAt (w σ) y) ∧ ∀ (σ : F →+* ℂ) (y : Pts Y σ) (y' : CxPts M.p (σ.comp (algebraMap (𝓞 F) F))), y'.1 = y.1 ≫ M.j → w _ y' = 2 * g σ y := by
  first | exact @GlobalTheory.ModelTwistLift.exists_smooth_lift | exact GlobalTheory.ModelTwistLift.exists_smooth_lift | (intros; apply GlobalTheory.ModelTwistLift.exists_smooth_lift <;> assumption)
