import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleSectionNonzeroLocusEqAffineOpenAStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleOfAffineNonzeroLocusAbelianSchemeNoetherStatement
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ProjNormal

theorem exists_relAmple_of_affine : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] [IsDomain R] [IsIntegrallyClosed R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ V : A.left.Opens, IsAffineOpen V → (∀ s : Sp R, ∃ x ∈ V, A.hom x = s) → ∃ L : LB A.left, L.IsLB ∧ Out.RelAmple A L := by
  intro R _ _ _ _ A _ hA V hV hV'
  obtain ⟨M, hM, s, hs⟩ := GlobalTheory.T.exists_section_nonzeroLocus_eq_affineOpen R A hA V hV hV'
  exact ⟨M, hM, GlobalTheory.T.relAmple_of_affine_nonzeroLocus_abelianScheme_noetherian R A hA M hM s (hs ▸ hV) (hs ▸ hV')⟩

end GlobalTheory.ProjNormal
