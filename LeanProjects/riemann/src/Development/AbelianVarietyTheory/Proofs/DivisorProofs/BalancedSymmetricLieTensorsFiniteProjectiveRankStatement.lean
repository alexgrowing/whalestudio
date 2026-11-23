import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BalancedSymmetricLieTensorsFiniteProjectiveRank
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigRank
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
theorem _root_.GlobalTheory.T.balancedSymmetricLieTensors_finite_projective_rank : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (F : IntermediateField ℚ ℂ) (hF : ∀ (τ : E →+* ℂ) (a : E), τ a ∈ F) (R : Type) [CommRing R] (iF : F →+* R) (n : ℕ) (A : 𝓞 E → Matrix (Fin n) (Fin n) R), A 1 = 1 → (∀ a b, A (a + b) = A a + A b) → (∀ a b, A (a * b) = A a * A b) → Module.Finite R (balanced H.bar A) ∧ Module.Projective R (balanced H.bar A) ∧ ∀ (m : Ideal R) [m.IsMaximal], 2 * Module.finrank (R ⧸ m) ((R ⧸ m) ⊗[R] balanced H.bar A) = ∑ τ : E →+* ℂ, GlobalTheory.BalProj.eigRank (algebraMap R m.ResidueField) A (GlobalTheory.BalProj.embR F hF iF τ) * GlobalTheory.BalProj.eigRank (algebraMap R m.ResidueField) A (GlobalTheory.BalProj.embR F hF iF (NumberField.ComplexEmbedding.conjugate τ)) := by
  first | exact @GlobalTheory.BalProj.Alg.balanced_finite_projective_rank | exact GlobalTheory.BalProj.Alg.balanced_finite_projective_rank | (intros; apply GlobalTheory.BalProj.Alg.balanced_finite_projective_rank <;> assumption)
