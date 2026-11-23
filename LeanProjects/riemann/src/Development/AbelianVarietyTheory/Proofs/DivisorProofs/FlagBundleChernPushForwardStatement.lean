import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleChernPushForward
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGradedRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingOnRegularFlagged
open NumberField MvPolynomial CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula Formalism.L2.Pj GlobalTheory GlobalTheory.ArInt GlobalTheory.VB GlobalTheory.CovTest GlobalTheory.FlagPoly GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.TwoLat GlobalTheory.OrthFilt GlobalTheory.VdmRec GlobalTheory.MixDens GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Published
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_bundle_chern_push_forward : Hypotheses2 → RegularAlteration → ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (e D : ℕ), IsArithVar q e → IsArithVar p D → ∀ (π : Y ⟶ B) (w : π ≫ q = p) (ι : Type) [Fintype ι] (E : ι → B.Modules) (r : ι → ℕ) (h : ∀ a, VMetric q (E a) (r a)) (H : ∀ a, (h a).IsCInf) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)), IsFlagBundle π E r fl → ∀ (κ μ : Type) [Fintype κ] [Fintype μ] (L : κ → HermLB p) (A : μ → HermLB q) (x : (Σ a, Fin (r a)) → κ) (y : μ → κ), (∀ z, (L (x z)).Isometric (VMetric.grLB (fl z.1) z.2 ((H z.1).pull π w))) → (∀ m, (L (y m)).Isometric ((A m).pull π w)) → ∀ (Φ : MvPolynomial μ ℝ →ₗ[ℝ] ℝ) (Ψ : MvPolynomial κ ℝ →ₗ[ℝ] ℝ), IsArFun A e Φ → IsArFun L D Ψ → ∀ P : MvPolynomial μ ℝ, P.IsHomogeneous (e + 1) → Ψ (rename x (vdm r) * rename y P) = (∏ a, ((r a).factorial : ℝ)) * Φ P := by
  first | exact @GlobalTheory.VdmProj.vdm_mul_pull | exact GlobalTheory.VdmProj.vdm_mul_pull | (intros; apply GlobalTheory.VdmProj.vdm_mul_pull <;> assumption)
