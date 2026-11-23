import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsogenousRetractPolarisedFiniteExtStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PotentialSemiAbelianReductionOfIsogenyStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PotentialSemiAbelianReductionOfRetractStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCompleteDvrIntegralClosureFiniteStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PotentialSemiAbelianModelOfSymmetryHypStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
namespace GlobalTheory.SS

theorem potModel_isSemiAbelian : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] (K : Type) [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (A : Over (Spec (CommRingCat.of K))) [GrpObj A], IsAbelianScheme A → PotModel V K A (fun _ _ _ G _ => IsSemiAbelian G) := by
  intro V _ _ _ _ K _ _ _ _ A _ hA
  obtain ⟨L, _, _, _, B, _, Q, g, m, i, r, i', r', hp, hs, hsB, hi, hr, hm, hri, hi', hr', hir, hS⟩ :=
    GlobalTheory.T.exists_isogenous_retract_polarised_finiteExt K A hA
  obtain ⟨W, _, _, _, _, _, _, _, -, -, -, -, -, hup⟩ := GlobalTheory.T.exists_complete_dvr_integral_closure_finite V K L
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
  letI := Q.grp
  have hQ := GlobalTheory.T.potentialSemiAbelianModel_of_symmetryHyp W L Q hS
  have hB := GlobalTheory.T.potentialSemiAbelianReduction_of_retract W L B Q.A i' r' hi' hr' hir hQ
  have hAL : IsAbelianScheme ((Over.pullback (spMap (algebraMap K L))).obj A) := by
    have := hA.comm
    have := hA.smooth
    have := hA.proper
    have := hA.geomConnected
    exact
      { comm := Functor.isCommMonObj_obj
        smooth := by change Smooth (pullback.snd A.hom _); infer_instance
        proper := by change IsProper (pullback.snd A.hom _); infer_instance
        geomConnected := by change GeometricallyConnected (pullback.snd A.hom _); infer_instance }
  exact hup A _ (GlobalTheory.T.potentialSemiAbelianReduction_of_isogeny W L _ B g m hAL hp hs hsB i r hi hr hm hri hB)
end GlobalTheory.SS
