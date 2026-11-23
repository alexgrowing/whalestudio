import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleChernHeight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGradedRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingOnRegularFlagged
open NumberField MvPolynomial CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula Formalism.L2.Pj GlobalTheory GlobalTheory.ArInt GlobalTheory.VB GlobalTheory.CovTest GlobalTheory.FlagPoly GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.TwoLat GlobalTheory.OrthFilt GlobalTheory.VdmRec GlobalTheory.MixDens GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Published
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_bundle_chern_height : Hypotheses2 → ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (e D : ℕ), IsArithVar q (e + 1) → IsArithVar p (D + 1) → ∀ (π : Y ⟶ B) (w : π ≫ q = p) (ι : Type) [Fintype ι] (E : ι → B.Modules) (r : ι → ℕ) (h : ∀ a, VMetric q (E a) (r a)) (H : ∀ a, (h a).IsCInf) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)), IsFlagBundle π E r fl → ∀ (κ μ : Type) [Fintype κ] [Fintype μ] (L : κ → HermLB p) (A : μ → HermLB q) (x : (Σ a, Fin (r a)) → κ) (y : μ → κ), (∀ z, (L (x z)).Isometric (VMetric.grLB (fl z.1) z.2 ((H z.1).pull π w))) → (∀ m, (L (y m)).Isometric ((A m).pull π w)) → ∀ P : MvPolynomial μ ℝ, P.IsHomogeneous e → ∀ (I : Type) [Fintype I] (c : I → ℝ) (n : I → κ → ℤ), ∑ j, c j • lin (fun i => (n j i : ℝ)) ^ D = rename x (vdm r) * rename y P → ∀ a, ∑ j, c j * bcPair ((h a).pull π w) (fl a) (comb L (n j)) D = 0 := by
  first | exact @GlobalTheory.BigCell.sum_bcPair_vdm_eq_zero | exact GlobalTheory.BigCell.sum_bcPair_vdm_eq_zero | (intros; apply GlobalTheory.BigCell.sum_bcPair_vdm_eq_zero <;> assumption)
