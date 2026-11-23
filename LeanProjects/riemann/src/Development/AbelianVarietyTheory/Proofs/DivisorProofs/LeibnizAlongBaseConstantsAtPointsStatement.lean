import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeibnizAlongBaseConstantsAtPoints
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
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leibniz_along_baseConstants_at_points : ∀ {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] {n : ℕ} {X : Scheme.{0}} (m : G.left ⟶ X) (L : LB X), L.IsLB → ∀ (v : Fin n → TanM (𝟙 (Sp R)) G) (dd : Fin n → Fld G.left), (∀ a, IsInv G (v a) (dd a)) → ∀ (D : Derivation ℤ R R) (h : Heat G m L dd ⇑D) (k : ℕ) (a b : R) (ρ τ ρ' τ' : SecM m L k), (∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (J : (Z ⟶ X) → L.ι), Good L z J → gs r z ⊤ (scal G.hom a) * sval ρ r z J = gs r z ⊤ (scal G.hom b) * sval τ r z J) → h.Acts k ρ ρ' → h.Acts k τ τ' → ∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (J : (Z ⟶ X) → L.ι), Good L z J → gs r z ⊤ (scal G.hom a) * sval ρ' r z J + gs r z ⊤ (scal G.hom (2 * (k : R) * D a)) * sval ρ r z J = gs r z ⊤ (scal G.hom b) * sval τ' r z J + gs r z ⊤ (scal G.hom (2 * (k : R) * D b)) * sval τ r z J := by
  first | exact @GlobalTheory.Heat.Heat.acts_const_at_points | exact GlobalTheory.Heat.Heat.acts_const_at_points | (intros; apply GlobalTheory.Heat.Heat.acts_const_at_points <;> assumption)
