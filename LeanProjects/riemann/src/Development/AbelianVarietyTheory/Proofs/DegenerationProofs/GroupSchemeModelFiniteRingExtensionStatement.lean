import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GroupSchemeModelFiniteRingExtension
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.GenericFiberGluing.SemistableCompleteSplit
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.groupScheme_model_finite_ring_extension : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (K : Type) [Field K] [Algebra V K] [IsFractionRing V K] (A : Over (Spec (CommRingCat.of K))) [GrpObj A] (K' : Type) [Field K'] [Algebra K K'] [FiniteDimensional K K'] (V' : Type) [CommRing V'] [IsDomain V'] [Algebra V V'] [Algebra V' K'] [IsFractionRing V' K'], (algebraMap V' K').comp (algebraMap V V') = (algebraMap K K').comp (algebraMap V K) → ∀ (G : Over (Spec (CommRingCat.of V'))) [GrpObj G], (∃ e : baseChange V' K' G ≅ baseChange K K' A, IsMonHom e.hom) → ∀ (V'' : Type) [CommRing V''] [IsDomain V''] [Algebra V' V''], Module.Finite V' V'' → Function.Injective (algebraMap V' V'') → ∃ (_ : Algebra K (FractionRing V'')) (_ : FiniteDimensional K (FractionRing V'')), (algebraMap V'' (FractionRing V'')).comp ((algebraMap V' V'').comp (algebraMap V V')) = (algebraMap K (FractionRing V'')).comp (algebraMap V K) ∧ ∃ e : baseChange V'' (FractionRing V'') (baseChange V' V'' G) ≅ baseChange K (FractionRing V'') A, IsMonHom e.hom := by
  first | exact @GlobalTheory.SS.model_finite_ext | exact GlobalTheory.SS.model_finite_ext | (intros; apply GlobalTheory.SS.model_finite_ext <;> assumption)
