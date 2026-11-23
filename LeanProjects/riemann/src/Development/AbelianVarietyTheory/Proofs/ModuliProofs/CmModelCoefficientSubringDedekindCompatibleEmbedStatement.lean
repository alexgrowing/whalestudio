import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmModelCoefficientSubringDedekindCompatibleEmbed
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
theorem _root_.GlobalTheory.T.cmModelCoefficientSubring_dedekind_compatible_embedding : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (S e : ℕ), 0 < S → l.A ∣ S ^ e → (∃ β : RZ H S l.A →+* KA l, IsInc (RZ H S l.A).subtype (KA l).val.toRingHom β) ∧ Algebra.FiniteType ℤ (RZ H S l.A) ∧ ∀ β : RZ H S l.A →+* KA l, IsInc (RZ H S l.A).subtype (KA l).val.toRingHom β → IsDedFrac β := by
  first | exact @GlobalTheory.BaseRing.isDedFrac_RZ | exact GlobalTheory.BaseRing.isDedFrac_RZ | (intros; apply GlobalTheory.BaseRing.isDedFrac_RZ <;> assumption)
