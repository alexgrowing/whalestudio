import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankOrth

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct

namespace GlobalTheory.TowerSpaces

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_tow : ∀ D : D7, ∃ Tw : Tow D, (∀ j, j < D.R.m → HEq (Tw.iXYs D.R.t j) (D.sp.iXY j)) ∧
    HEq (Tw.iYXm D.R.t) (D.sp.iX'.comp D.sp.eYm.symm.toLinearMap) := by
  intro D
  obtain ⟨Tw⟩ := nonempty_tow (GlobalTheory.WittLow.wittLowEx D)
  exact ⟨Tw, Tw.iXYs_rec, Tw.iYXm_rec⟩

end GlobalTheory.TowerSpaces
