import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ReducedFiniteTypeIffTestRing
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory

theorem testRing_localizationAway :
    ∀ (K : Type) [Field K] (p : TRing K) (g : p.R), ∃ (p' : TRing K) (lam : p.R →ₐ[K] p'.R), IsUnit (lam g) ∧ ∀ (T : Type) [CommRing T] [Algebra K T] (ψ : p.R →ₐ[K] T), IsUnit (ψ g) → ∃ k : p'.R →ₐ[K] T, k.comp lam = ψ := by
  intro K _ p g
  obtain ⟨h1, h2⟩ := reduced_finiteType_iff_testRing K
  obtain ⟨hft, hred⟩ := h2 p
  have hft1 : Algebra.FiniteType p.R (Localization.Away g) :=
    IsLocalization.finiteType_of_monoid_fg (Submonoid.powers g) _
  have hft' : Algebra.FiniteType K (Localization.Away g) := Algebra.FiniteType.trans hft hft1
  have hred' : IsReduced (Localization.Away g) :=
    isReduced_localizationPreserves (Submonoid.powers g) _ hred
  obtain ⟨p', ⟨e⟩⟩ := h1 (Localization.Away g) hft' hred'
  refine ⟨p', e.symm.toAlgHom.comp (IsScalarTower.toAlgHom K p.R (Localization.Away g)), ?_, ?_⟩
  · exact (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away g) g).map e.symm
  · intro T _ _ ψ hψ
    have hu : ∀ y : Submonoid.powers g, IsUnit (ψ y) := by
      rintro ⟨_, n, rfl⟩
      simpa using hψ.pow n
    refine ⟨(IsLocalization.liftAlgHom (M := Submonoid.powers g) (S := Localization.Away g)
      (f := ψ) hu).comp e.toAlgHom, ?_⟩
    apply AlgHom.ext
    intro x
    simp [IsLocalization.liftAlgHom]

end GlobalTheory
