import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreimageEqOfAgreeOnClosedFibreDualNumbers
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConnK
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
theorem _root_.GlobalTheory.T.preimage_eq_of_agree_on_closedFibre_dualNumbers : ∀ (k : Type) [Field k] (X B : Scheme.{0}) (h : B ⟶ Sp (DualNumber k)) (π₁ π₂ : B ⟶ X), (∀ (Z : Scheme.{0}) (x : Z ⟶ B) (y : Z ⟶ Sp k), x ≫ h = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → ∀ W : X.Opens, π₁ ⁻¹ᵁ W = π₂ ⁻¹ᵁ W := by
  first | exact @GlobalTheory.LogKS.preimage_eq_of_agree_closedFibre | exact GlobalTheory.LogKS.preimage_eq_of_agree_closedFibre | (intros; apply GlobalTheory.LogKS.preimage_eq_of_agree_closedFibre <;> assumption)
