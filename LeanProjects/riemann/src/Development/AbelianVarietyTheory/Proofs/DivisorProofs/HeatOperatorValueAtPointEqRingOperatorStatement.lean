import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatOperatorValueAtPointEqRingOperator
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heatOperator_value_at_point_eq_ringOperator : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (X : Scheme.{0}) (m : G.left ⟶ X) (L : LB X) (n : ℕ) (dd : Fin n → Fld G.left) (D : R → R) (h : Heat G m L dd D) (i0 : h.J) (Ω : Type) [CommRing Ω] (φ : R →+* Ω) (x : Sp Ω ⟶ G.left), x ≫ G.hom = spMap φ → ∀ (δ : Fin n → Derivation ℤ Ω Ω), (∀ a O f, ⊤ ≤ x ⁻¹ᵁ O → valR x O (dd a O f) = δ a (valR x O f)) → ∀ (dΩ : Derivation ℤ Ω Ω), ⊤ ≤ x ⁻¹ᵁ h.W i0 → (∀ O f, O ≤ h.W i0 → ⊤ ≤ x ⁻¹ᵁ O → valR x O (h.d i0 O f) = dΩ (valR x O f)) → (∀ r, dΩ (φ r) = φ (D r)) ∧ ∀ (k : ℕ) (τ τ' : SecM m L k), h.Acts k τ τ' → valR x (h.W i0) (rsT (τ'.f fun _ => h.j i0) (h.W i0)) = ringOp ⇑dΩ (fun a => ⇑(δ a)) (φ.mapMatrix h.Θ) (fun a => φ (h.u a)) (valR x _ (h.p i0)) (valR x _ (h.p' i0)) k (valR x (h.W i0) (rsT (τ.f fun _ => h.j i0) (h.W i0))) := by
  first | exact @GlobalTheory.HeatPointValue.value_acts | exact GlobalTheory.HeatPointValue.value_acts | (intros; apply GlobalTheory.HeatPointValue.value_acts <;> assumption)
