import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteTypeRepresentingPolarizedHomsLocNoetStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperOfFiniteType
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormallyUnramifiedHomWithFixedPullbackSchemeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteOfIsProperOfFormallyUnramified
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.EndLoc.HomFixFinite

theorem exists_finite_unramified : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A B : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left), IsAbelianScheme A → IsAbelianScheme B → L.IsLB → M.IsLB → Out.Rigidified A L → Out.Rigidified B M → Out.RelAmple A L → Out.RelAmple B M → ∃ R : HomFixRep A B L M, IsFinite R.π ∧ FormallyUnramified R.π := by
  intro S _ A B _ _ _ _ L M hA hB hL hM rA rB aA aB
  obtain ⟨R, hqc, hsep, hlft⟩ := GlobalTheory.T.exists_finiteType_representing_polarizedHoms_locNoeth S A B L M hA hB hL hM rA rB aA aB
  have hpr : IsProper R.π :=
    GlobalTheory.EndLoc.HomFixProper.isProper_of_finiteType S A B L M R hA hB hL hM rA rB hqc hsep hlft
  have hun : FormallyUnramified R.π := GlobalTheory.T.formallyUnramified_homWithFixedPullback_scheme S A B L M R hA hB
  exact ⟨R, GlobalTheory.PropFin.isFinite_of_isProper_of_formallyUnramified _ _ R.π hpr hun, hun⟩

end GlobalTheory.EndLoc.HomFixFinite
