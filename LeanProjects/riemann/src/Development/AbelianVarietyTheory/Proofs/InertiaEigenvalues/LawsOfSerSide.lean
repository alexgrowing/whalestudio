import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearIndependentRowsMap
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemBlockTriangularTwoBlockSizesOfLe
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RatHeckeRealRd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitOffOutsideS0
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RationalDatumSmallFieldFormHeckeScalarUnitStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.TwInputs

theorem laws_of_serSide : ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E), (∀ i, D.ntw.NonzeroIndexPlace i → ∀ j b, RatRow Y.YS X.geo.v₀ Y.Z.good i j b) → Laws Y.Z.good Y.Z.rd := by
  intro D X E Y hR
  refine ⟨fun i j b => ?_, fun i j b => ?_, fun i j b => ?_, fun i hi j b => Y.Z.rat (hR i hi j b)⟩
  · exact GlobalTheory.SeriesTie.realRd_faithful D _ _ _ _ _ _ X.R X.cG Y.S Y.YS X.geo.v₀ Y.Z.ρ Y.Z.good i j b _
      (Y.Z.scalar i j b).ne X.unif X.char.models.HW (Y.Z.vec j)
      ((GlobalTheory.T.rational_datum_small_field_form_hecke_scalar_unit D X E Y).1 _ (Nat.le_add_left _ _) j.2)
  · exact GlobalTheory.SeriesTie.actRead_realRd D _ _ _ _ _ _ X.R X.cG Y.S Y.YS X.geo.v₀ Y.Z.ρ Y.Z.good i j b _
      Y.Z.pin X.unif X.char.models.HW
  · exact Y.Z.heckeRead (GlobalTheory.SeriesTie.HkRat.ratHecke_realRd D _ _ _ _ _ _ X.R X.cG Y.S Y.YS X.geo.v₀ Y.Z.ρ Y.Z.good i j b _
      Y.Z.pin (X.char.lev.mu0 j) (GlobalTheory.SplitOffS0.main Y.Z.good i _ (Y.Sb i)) Y.H.hL
      (Y.H.hs _ (Nat.le_add_left _ _) j.2) Y.reads)

end GlobalTheory.TwInputs
