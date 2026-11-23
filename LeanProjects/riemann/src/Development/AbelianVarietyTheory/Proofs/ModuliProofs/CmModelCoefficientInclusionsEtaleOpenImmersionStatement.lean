import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmModelCoefficientInclusionsEtaleOpenImmersion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
theorem _root_.GlobalTheory.T.cmModelCoefficient_inclusions_etale_openImmersion : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S S' A A' e : ℕ), 0 < S' → 0 < A' → S ∣ S' → A ∣ A' → (∃ b : RZ H S A →+* RZ H S' A', IsInc (RZ H S A).subtype (RZ H S' A').subtype b) ∧ ∀ b : RZ H S A →+* RZ H S' A', IsInc (RZ H S A).subtype (RZ H S' A').subtype b → (S = S' → A' ∣ S ^ e → IsFinite (spMap b) ∧ Etale (spMap b) ∧ Surjective (spMap b)) ∧ (A = A' → IsOpenImmersion (spMap b) ∧ ∀ x : Sp (RZ H S A), x ∈ Set.range (spMap b) ↔ (S' : RZ H S A) ∉ x.asIdeal) := by
  first | exact @GlobalTheory.BaseRing.inclusion_RZ | exact GlobalTheory.BaseRing.inclusion_RZ | (intros; apply GlobalTheory.BaseRing.inclusion_RZ <;> assumption)
