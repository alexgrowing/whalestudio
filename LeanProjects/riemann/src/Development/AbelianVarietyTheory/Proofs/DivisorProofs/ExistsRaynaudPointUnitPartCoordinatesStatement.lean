import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRaynaudPointUnitPartCoordinates
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_raynaudPoint_unitPart_coordinates : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (m : ℕ) (t : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ Q.X), Q.TauBimult → (∀ i, t i ≠ 0) → ∀ (n : Q.X → Fin m → ℕ), (∀ χ i, gam i χ χ = 2 * n χ i) → ∀ (ψ₀ : ∀ χ : Q.X, LB.Gen (LB.LinComb Q.P.L (K := PUnit) (fun _ => (Q.c χ).left) fun _ => -1)), (∀ χ, (ψ₀ χ).IsGen) → (∀ χ (Z : Scheme.{0}) (r : Z ⟶ (TK R).left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → (val (Q.psi χ) r z J).val = cst (r ≫ jK R) z (∏ i, t i ^ n χ i) * (val (ψ₀ χ) (r ≫ jK R) z J).val) → ∀ mu : Q.X, ∃ xp : 𝟙_ (Over (Sp R)) ⟶ Y.H, xp ≫ Y.q = Q.c mu ∧ ∀ (Z : Scheme.{0}) (g : Z ⟶ (TK R).left) (χ : Q.X) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → cst (g ≫ jK R) z (∏ i, t i ^ n (mu + χ) i) * (val ((Y.Φ (Over.mk (g ≫ jK R)) (toUnit _ ≫ xp)).s χ) (𝟙 Z) z J).val = cst (g ≫ jK R) z (∏ i, t i ^ (n mu i + n χ i)) * (val (Q.tau mu χ) g z J).val := by
  first | exact @GlobalTheory.UnitPartPt.exists_unitPartPt | exact GlobalTheory.UnitPartPt.exists_unitPartPt | (intros; apply GlobalTheory.UnitPartPt.exists_unitPartPt <;> assumption)
