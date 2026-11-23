import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaSeriesDataHypothesesBelowMaximalLevel
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.FrecAt
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.MovDXiAtRecStep
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.LocalClassDataOfTrivialStabilizers
import Formalism.LocalToGlobal.GlobalTheory.BaseLatticeSelfDual
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem reindex_rename_point_det_latK : ∀ {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (sp : Spaces R F E) {N n : ℕ} (h : N = n) (J : Matrix (Fin N) (Fin N) E) (a : 𝓞 E) (y : GL (Fin N) (E ⊗[F] (FiniteAdeleRing (𝓞 F) F))) (Lb : Submodule (𝓞 E) (Fin N → E)), Formalism.L2.PairingIndexBounds.F.reGL (finCongr h.symm) (Formalism.L2.PairingIndexBounds.F.reGL (finCongr h) y) = y ∧ Matrix.GeneralLinearGroup.det (Formalism.L2.PairingIndexBounds.F.reGL (finCongr h) y) = Matrix.GeneralLinearGroup.det y ∧ HEq ((latK sp (J.reindex (finCongr h) (finCongr h)) a (Formalism.L2.PairingIndexBounds.F.reGL (finCongr h) y) (Lb.map ((reE (E := E) h).toLinearMap.restrictScalars (𝓞 E)))).map ((reE (E := E) (rfl : n = n)).toLinearMap.restrictScalars (𝓞 E))) (latK sp J a y Lb) := by
  intro R F E _ _ _ _ _ _ sp N n h J a y Lb
  subst h
  have hr : ∀ {A : Type} [CommRing A] (g : GL (Fin N) A), Formalism.L2.PairingIndexBounds.F.reGL (finCongr (rfl : N = N)) g = g := by
    intro A _ g
    ext i j
    simp [Formalism.L2.PairingIndexBounds.F.reGL]
  have hJ : J.reindex (finCongr (rfl : N = N)) (finCongr (rfl : N = N)) = J := by
    ext i j
    simp
  refine ⟨?_, ?_, ?_⟩
  · rw [hr, hr]
  · rw [hr]
  · apply heq_of_eq
    rw [hJ, hr, map_reE_rfl, map_reE_rfl]

end GlobalTheory
