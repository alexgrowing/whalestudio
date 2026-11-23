import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteTypeSchemeRepresentingPolarizedHomsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianSchemeRestrictOpenImmersionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidifiedBundlePullbackIsoOfLocalIsoAbelianHomStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomFixedPullbackRepresentableGlueStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.HomFixGlue

theorem homFix_finiteType : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A B : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left), IsAbelianScheme A → IsAbelianScheme B → L.IsLB → M.IsLB → Out.Rigidified A L → Out.Rigidified B M → Out.RelAmple A L → Out.RelAmple B M → ∃ R : HomFixRep A B L M, QuasiCompact R.π ∧ IsSeparated R.π ∧ LocallyOfFiniteType R.π := by
  intro S _ A B _ _ _ _ L M hA hB hL hM rA rB aA aB
  refine GlobalTheory.T.homFixedPullback_representable_glue GlobalTheory.T.rigidifiedBundle_pullbackIso_of_localIso_abelianHom S A B L M hA hB hL hM rA rB S.affineOpens (fun U => Sp Γ(S, U)) (fun U => U.2.fromSpec)
    (fun U => IsAffineOpen.isOpenImmersion_fromSpec U.2) ?_ ?_
  · intro s
    obtain ⟨U, hU, hs, -⟩ := exists_isAffineOpen_mem_and_subset (show s ∈ (⊤ : S.Opens) from trivial)
    exact ⟨⟨U, hU⟩, hU.range_fromSpec.ge hs⟩
  · intro U
    haveI : IsNoetherianRing Γ(S, U) := IsLocallyNoetherian.component_noetherian U
    obtain ⟨A', _, _, φA, gA, hA', hL', rA', aA'⟩ := GlobalTheory.T.exists_abelianScheme_restrict_openImmersion S A L hA hL rA aA _ U.2.fromSpec (IsAffineOpen.isOpenImmersion_fromSpec U.2)
    obtain ⟨B', _, _, φB, gB, hB', hM', rB', aB'⟩ := GlobalTheory.T.exists_abelianScheme_restrict_openImmersion S B M hB hM rB aB _ U.2.fromSpec (IsAffineOpen.isOpenImmersion_fromSpec U.2)
    obtain ⟨R, h1, h2, h3⟩ := GlobalTheory.T.exists_finiteType_scheme_representing_polarizedHoms Γ(S, U) A' B' (L.pull φA) (M.pull φB) hA' hB' hL' hM' rA' rB' aA' aB'
    exact ⟨A', B', _, _, φA, φB, R, gA, gB, h1, h2, h3⟩

end GlobalTheory.HomFixGlue
