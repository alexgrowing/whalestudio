import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRootOfKeyFormula
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MinSt2
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.ExistsIsAddFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModuliModelUltrametricPoints
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SplitExtDVR

theorem exists_complete_dvr_split_ext : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V],
    IsAdicComplete (IsLocalRing.maximalIdeal V) V → ∀ (G : Over (Sp V)) [GrpObj G], IsSemiAbelian G →
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (_ : CharZero W) (g : V →+* W),
      IsAdicComplete (IsLocalRing.maximalIdeal W) W ∧ g.IsIntegral ∧ Function.Injective g ∧ IsLocalHom g ∧
      ∃ E : SplitExt (Sp (IsLocalRing.ResidueField W)),
        E.IsGt ((Over.pullback (spMap (IsLocalRing.residue W))).obj ((Over.pullback (spMap g)).obj G)) := by
  intro V _ _ _ _ hcV G _ hG
  haveI := hcV
  let F := AlgebraicClosure (FractionRing V)
  have : Algebra.IsAlgebraic V F :=
    (IsFractionRing.comap_isAlgebraic_iff (A := V) (K := FractionRing V) (C := F)).2 inferInstance
  have hi : Function.Injective (algebraMap V F) := by
    rw [IsScalarTower.algebraMap_eq V (FractionRing V) F]
    exact (algebraMap (FractionRing V) F).injective.comp (IsFractionRing.injective _ _)
  have : FaithfulSMul V F := (faithfulSMul_iff_algebraMap_injective _ _).2 hi
  obtain ⟨W, hd, hc, hfin, hs⟩ := GlobalTheory.Ex.UnifModel.exists_split V F G hG
  have hW : Function.Injective (algebraMap V W) := fun _ _ h => hi (congrArg (fun z : W => (z : F)) h)
  have : CharZero W := charZero_of_injective_algebraMap hW
  have : FaithfulSMul V W := (faithfulSMul_iff_algebraMap_injective _ _).2 hW
  have hl : IsLocalHom (algebraMap V W) := inferInstance
  have hint : (algebraMap V W).IsIntegral := by
    have : Algebra.IsIntegral V W := Algebra.IsIntegral.of_finite V W
    exact Algebra.IsIntegral.isIntegral
  exact ⟨W, inferInstance, inferInstance, hd, inferInstance, algebraMap V W, hc, hint, hW, hl, hs⟩

end GlobalTheory.SplitExtDVR
