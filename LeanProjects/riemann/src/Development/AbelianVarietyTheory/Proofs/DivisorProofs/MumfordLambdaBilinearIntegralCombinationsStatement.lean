import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordLambdaBilinearIntegralCombinations
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinProdIsGen
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mumfordLambda_bilinear_integral_combinations : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (T : Over (Spec (CommRingCat.of R))) {r : ℕ} (p : Fin r → (T ⟶ D.toPre.P.A)) (m n : Fin r → ℤ), ∃ t : LB.Gen (LB.LinComb D.toPre.P.L (Sum.elim (GlobalTheory.PolDeg.lamPts (∏ k, p k ^ m k) (∏ l, p l ^ n l)) (fun q : (Fin r × Fin r) × Fin 4 => GlobalTheory.PolDeg.lamPts (p q.1.1) (p q.1.2) q.2)) (Sum.elim Oε (fun q : (Fin r × Fin r) × Fin 4 => -(m q.1.1 * n q.1.2 * Oε q.2)))), t.IsGen ∧ ∀ (ρ : TK R ⟶ T) (y : Fin r → D.toPre.X), (∀ k, ρ ≫ p k = toUnit (TK R) ≫ D.toPre.c (y k)) → ∀ (z : (TK R).left) (J : ((TK R).left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι), Good D.toPre.P.L z J → val t ρ.left z J = (val (D.toPre.tau (∑ k, m k • y k) (∑ l, n l • y l)) (𝟙 _) z J)⁻¹ * ∏ k, ∏ l, val (D.toPre.tau (y k) (y l)) (𝟙 _) z J ^ (m k * n l) := by
  first | exact @GlobalTheory.MumBil.lam_bilin | exact GlobalTheory.MumBil.lam_bilin | (intros; apply GlobalTheory.MumBil.lam_bilin <;> assumption)
