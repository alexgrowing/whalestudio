import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NonemptyTorusExtensionOfSurjectivePointsStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS

theorem isSemiAbelian_of_retract : ∀ (S : Scheme.{0}) (G G₁ : Over S) [GrpObj G] [GrpObj G₁], IsSemiAbelian G → SmConn G₁ → ∀ (i : G₁ ⟶ G) (r : G ⟶ G₁), IsMonHom r → i ≫ r = 𝟙 G₁ → IsSemiAbelian G₁ := by
  intro S G G₁ _ _ hG h₁ i r hr hir
  obtain ⟨hc, hs, hsep, hq, hg⟩ := h₁
  refine ⟨hc, hs, hsep, hq, hg, fun Ω _ _ p => ?_⟩
  have h₂ : SmConn ((Over.pullback p).obj G₁) := by
    refine ⟨inferInstance, ?_, ?_, ?_, ?_⟩
    · show Smooth (pullback.snd G₁.hom p); infer_instance
    · show IsSeparated (pullback.snd G₁.hom p); infer_instance
    · show QuasiCompact (pullback.snd G₁.hom p); infer_instance
    · show GeometricallyConnected (pullback.snd G₁.hom p); infer_instance
  refine GlobalTheory.T.nonempty_torusExtension_of_surjective_points' Ω ((Over.pullback p).obj G) ((Over.pullback p).obj G₁) h₂ (hG.fibres Ω p)
    ((Over.pullback p).map r) inferInstance fun y => ⟨y ≫ (Over.pullback p).map i, ?_⟩
  rw [Category.assoc, ← Functor.map_comp, hir, CategoryTheory.Functor.map_id, Category.comp_id]

end GlobalTheory.SS
