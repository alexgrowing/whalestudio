import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralShiftOfGeneratorUpToConst
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatOperatorShiftDivMonomial
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integralShift_of_generator_up_to_const : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (y : Q.X) (N : ℕ) (c : R) (uR : LB.Gen (LB.LinComb Q.P.L (Sum.elim (Q.famφB (0 + N • y)) (fun i => (lift (toUnit Q.P.A ≫ Q.c y) (𝟙 Q.P.A) ≫ μ[Q.P.A]).left ≫ Q.famφB 0 i)) (DegPre.deltaε N))), uR.IsGen → (∀ (u : LB.Gen (LB.LinComb Q.P.L (DegPre.deltaφ Q (FractionRing R) N 0 y) (DegPre.deltaε N))), u.IsGen → LB.Gen.Corr Q.P.L _ _ _ _ (LB.pullGen Q.P.L _ _ u (DegPre.zF Q (FractionRing R)).left) (DegPre.famMult Q (FractionRing R) N y 0) → ∀ (z : (DegPre.BF Q (FractionRing R)).left) (J : ((DegPre.BF Q (FractionRing R)).left ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → (val u (𝟙 _) z J).val = gs ((DegPre.prB Q (FractionRing R)).left ≫ Q.P.A.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c) * (val uR (DegPre.prB Q (FractionRing R)).left z J).val) → ∃ (w : ∀ (z : Q.P.A.left) (J : (Q.P.A.left ⟶ Q.P.A.left) → Q.P.L.ι), (Q.P.A.left.presheaf.stalk z)ˣ) (Sh : Q.SecB N 0 → Q.SecB N (0 + N • y)), ∀ x : Q.SecB N 0, (∀ (z : Q.P.A.left) (J : (Q.P.A.left ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → sval (Sh x) (𝟙 _) z J = sval x (lift (toUnit Q.P.A ≫ Q.c y) (𝟙 Q.P.A) ≫ μ[Q.P.A]).left z J * (w z J).val) ∧ ∃ x₁ : Q.SecB N (0 + N • y), ShiftEq Q N y 0 x x₁ 0 x₁ ∧ ∀ (Z : Scheme.{0}) (X : Z ⟶ Q.P.A.left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → sval x₁ X z J = gs (X ≫ Q.P.A.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c) * sval (Sh x) X z J := by
  first | exact @GlobalTheory.IntegralShift.exists_shift_of_gen | exact GlobalTheory.IntegralShift.exists_shift_of_gen | (intros; apply GlobalTheory.IntegralShift.exists_shift_of_gen <;> assumption)
