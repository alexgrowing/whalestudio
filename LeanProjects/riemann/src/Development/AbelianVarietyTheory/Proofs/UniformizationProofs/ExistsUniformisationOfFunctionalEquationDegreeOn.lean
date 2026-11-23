import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpBijOfMatchStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsExpFOfFam
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FiniteExponentBaseChangeFieldStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FunctionalEquationAllDegreesAlgebraicClosureStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GmResPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.Uniformization.WCompat
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueSamePt
import Development.AbelianVarietyTheory.Definitions.Uniformization.SameB
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.UU

theorem exists_unif_of_fe_one : Laws → Laws2 → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDVR V → ∀ (D : DegData V (IsLocalRing.maximalIdeal V)) (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G] (U : PreU (IsLocalRing.maximalIdeal V) D.toPre A G), U.FE (Kbar V) 1 → ∃ U' : Unif (IsLocalRing.maximalIdeal V) D A G, Match U U'.toUnifPre := by
  intro hL hL2 V _ _ _ hV D A G _ _ U h1
  obtain ⟨U', hM⟩ := ToChart.exists_match V (IsLocalRing.maximalIdeal V) D A G U
  refine ⟨⟨U', fun k hk => ?_⟩, hM⟩
  have hb : U.FE (Kbar V) k := GlobalTheory.T.functional_equation_all_degrees_algebraic_closure hL hL2 V hV D.toPre A G U D.tau_bimult h1 k hk
  have hF : U.FE (FractionRing V) k :=
    GlobalTheory.T.finite_exponent_base_change_field hL.globalFns V hV D.toPre A G U k hb (FractionRing V)
  exact GlobalTheory.T.expBij_of_match_of_fam_expF hL hL2 V hV D A G U U' hM k hk hF
    (ExpOnto.exists_expF_of_fam hL hL2 V hV D.toPre A G U D.tau_bimult (FractionRing V) k hk hF)

end GlobalTheory.UU
