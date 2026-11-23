import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDerivationFibreProductAffineCompatible
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
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
theorem _root_.GlobalTheory.T.exists_derivation_fibreProduct_affine_compatible : ∀ (Z Z' X X' : Scheme.{0}) (p : Z ⟶ X) (p' : Z' ⟶ X') (φ : Z' ⟶ Z) (g : X' ⟶ X), IsPullback φ p' p g → ∀ (U : X.affineOpens) (U' : X'.affineOpens) (hU : U'.1 ≤ g ⁻¹ᵁ U.1) (D : Derivation ℤ Γ(X, U.1) Γ(X, U.1)) (D' : Derivation ℤ Γ(X', U'.1) Γ(X', U'.1)), (∀ r, D' ((g.appLE U.1 U'.1 hU).hom r) = (g.appLE U.1 U'.1 hU).hom (D r)) → ∀ (O : Z.affineOpens) (hO : O.1 ≤ p ⁻¹ᵁ U.1) (δ : Derivation ℤ Γ(Z, O.1) Γ(Z, O.1)), (∀ r, δ ((p.appLE U.1 O.1 hO).hom r) = (p.appLE U.1 O.1 hO).hom (D r)) → ∃ δ' : Derivation ℤ Γ(Z', φ ⁻¹ᵁ O.1 ⊓ p' ⁻¹ᵁ U'.1) Γ(Z', φ ⁻¹ᵁ O.1 ⊓ p' ⁻¹ᵁ U'.1), (∀ r, δ' ((p'.appLE U'.1 _ inf_le_right).hom r) = (p'.appLE U'.1 _ inf_le_right).hom (D' r)) ∧ ∀ f, δ' ((φ.appLE O.1 _ inf_le_left).hom f) = (φ.appLE O.1 _ inf_le_left).hom (δ f) := by
  first | exact @GlobalTheory.FibreDer.exists_der_fibre | exact GlobalTheory.FibreDer.exists_der_fibre | (intros; apply GlobalTheory.FibreDer.exists_der_fibre <;> assumption)
