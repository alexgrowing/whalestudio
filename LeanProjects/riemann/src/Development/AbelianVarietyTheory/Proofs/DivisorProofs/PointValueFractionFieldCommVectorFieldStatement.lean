import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointValueFractionFieldCommVectorField
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResV
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
theorem _root_.GlobalTheory.T.pointValue_fractionField_comm_vectorField : ∀ (X : Scheme.{0}) (Ω : Type) [CommRing Ω] [IsDomain Ω] [IsLocalRing Ω] (x : Sp Ω ⟶ X) (dd : Fld X) (δ : Derivation ℤ Ω Ω) (δL : Derivation ℤ (FractionRing Ω) (FractionRing Ω)), IsField ⊤ dd → (∀ (O : X.Opens) (f : Γ(X, O)), ⊤ ≤ x ⁻¹ᵁ O → valR x O (dd O f) = δ (valR x O f)) → (∀ ω, δL (algebraMap Ω (FractionRing Ω) ω) = algebraMap Ω (FractionRing Ω) (δ ω)) → ∀ (O : X.Opens) (f : Γ(X, O)), ⊤ ≤ (spMap (algebraMap Ω (FractionRing Ω)) ≫ x) ⁻¹ᵁ O → valR (spMap (algebraMap Ω (FractionRing Ω)) ≫ x) O (dd O f) = δL (valR (spMap (algebraMap Ω (FractionRing Ω)) ≫ x) O f) := by
  first | exact @GlobalTheory.GenericVal.valR_generic | exact GlobalTheory.GenericVal.valR_generic | (intros; apply GlobalTheory.GenericVal.valR_generic <;> assumption)
