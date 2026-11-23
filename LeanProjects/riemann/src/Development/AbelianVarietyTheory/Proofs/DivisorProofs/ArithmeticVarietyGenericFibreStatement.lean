import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticVarietyGenericFibre
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open MvPolynomial GlobalTheory.CovTop GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithmetic_variety_generic_fibre : ArCalc → ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d e : ℕ), IsArithVar q d → (∀ b : B, IsRegularLocalRing (B.presheaf.stalk b)) → IsArithVar p (d + e) → ∀ (f : Y ⟶ B) (w : f ≫ q = p) (G : Scheme.{0}) (j : G ⟶ Y) (s : G ⟶ Sp B.functionField), IsPullback j s f (B.fromSpecStalk (genericPoint B)) → ∀ (L : Fin e → HermLB p) (κ : Type) [Fintype κ] (A : κ → HermLB q) (Φ : MvPolynomial κ ℝ →ₗ[ℝ] ℝ) (Ψ : MvPolynomial (Fin e ⊕ κ) ℝ →ₗ[ℝ] ℝ), IsArFun A d Φ → IsArFun (Sum.elim L fun a => (A a).pull f w) (d + e) Ψ → ∀ P : MvPolynomial κ ℝ, P.IsHomogeneous (d + 1) → Ψ ((∏ i : Fin e, MvPolynomial.X (Sum.inl i)) * rename Sum.inr P) = (letI := algebraΓOfHom s; (interNum B.functionField (structureModule G) (fun i => (L i).B.pull j) : ℝ)) * Φ P := by
  first | exact @GlobalTheory.FibreProj.arFun_mul_pull | exact GlobalTheory.FibreProj.arFun_mul_pull | (intros; apply GlobalTheory.FibreProj.arFun_mul_pull <;> assumption)
