import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyMultiWitOfArcWit
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsIsPullQk
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsRootOfIsAlgClosed
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPsiCoordOfIsPsiCoord
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PsiCoordExistsUniqueUpToUnitLocal
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ArcWitPsiOnBasicOpen
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ArcClauseOfNotFrac
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ArcVarZpowInjective
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.LocM.FJ
open GlobalTheory.Toroidal
open GlobalTheory.ArcQ (Wit LieImg)
open Formalism.MainNotions.DIV.Cons (intO)

noncomputable section

namespace GlobalTheory.LocM.FJ.MultiData

theorem psiCoord_rescale {R : Type} [CommRing R] [IsDomain R] (D : Out.DegPre R) (q : D.X → (FractionRing R)ˣ)
    {χ : D.X} {r s : R} (hr : PsiCoord D χ r)
    (hq : ((q χ : (FractionRing R)ˣ) : FractionRing R) = algebraMap R (FractionRing R) s) :
    PsiCoord (GlobalTheory.TauTwist.rescale D q) χ (s * r) := by
  obtain ⟨x, ⟨j, h, hj, rfl⟩, e⟩ := (GlobalTheory.PeriodFormCompare.psiCoord_iff D χ r).1 hr
  refine (GlobalTheory.PeriodFormCompare.psiCoord_iff (GlobalTheory.TauTwist.rescale D q) χ (s * r)).2
    ⟨q χ * GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.genVal (D.psi χ) j h, ⟨j, h, hj, ?_⟩, ?_⟩
  · dsimp only [GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.genVal, GlobalTheory.TauTwist.rescale, GlobalTheory.TauTwist.withPsi, ReciprocityTheory.ChartRestriction.G.DVR.scaleGen]
    rw [map_mul, map_mul, GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.res_res]
    congr 1
    ext
    show (q χ : FractionRing R) = (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom
      (((Sp (FractionRing R)).presheaf.map (𝟙 _)).hom
        ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom (q χ : FractionRing R)))
    rw [CategoryTheory.Functor.map_id]
    exact ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv_hom_id_apply _).symm
  · rw [Units.val_mul, hq, e, map_mul]

theorem exists_unit_psiCoord {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (D : Out.DegPre R) (χ : D.X)
    (h : PsiUnitOn D χ Set.univ) : ∃ v : Rˣ, PsiCoord D χ v := by
  obtain ⟨j, hj⟩ := GlobalTheory.PsiCoordLocal.exists_chart_top D χ
  have hh := GlobalTheory.PsiCoordLocal.generic_le D χ j hj
  obtain ⟨s, hs, e⟩ := h j ⊤ (isAffineOpen_top _) (Set.subset_univ _) hj hh
  obtain ⟨r, rfl⟩ := GlobalTheory.PsiCoordLocal.toOpen_top_bijective.2 s
  have hu : IsUnit r := (MulEquiv.isUnit_map
    (RingEquiv.ofBijective (Out.DegPre.toOpen (R := R) ⊤) GlobalTheory.PsiCoordLocal.toOpen_top_bijective).toMulEquiv).1 hs
  exact ⟨hu.unit, j, hj, hh, e⟩

end GlobalTheory.LocM.FJ.MultiData

namespace GlobalTheory.LocM.FJ.MultiData

end GlobalTheory.LocM.FJ.MultiData
