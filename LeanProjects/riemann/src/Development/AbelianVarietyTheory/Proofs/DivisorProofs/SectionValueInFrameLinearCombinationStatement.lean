import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionValueInFrameLinearCombination
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
theorem _root_.GlobalTheory.T.sectionValueInFrame_linearCombination : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) (L : LB G.left) (Ω : Type) [CommRing Ω] (φ : R →+* Ω) (x' : Sp Ω ⟶ G.left), x' ≫ G.hom = spMap φ → ∀ (g : GlobalTheory.RayEv.Transport.Frame L (x' ≫ 𝟙 G.left)) (k : ℕ) (σ₁ σ₂ : SecM (𝟙 G.left) L k) (ω₁ ω₂ : Ω) (a b : R), IsValue (𝟙 _) L x' g k σ₁ ω₁ → IsValue (𝟙 _) L x' g k σ₂ ω₂ → ∃ σ : SecM (𝟙 G.left) L k, IsValue (𝟙 _) L x' g k σ (φ a * ω₁ + φ b * ω₂) := by
  first | exact @GlobalTheory.Heat.exists_isValue_lin | exact GlobalTheory.Heat.exists_isValue_lin | (intros; apply GlobalTheory.Heat.exists_isValue_lin <;> assumption)
