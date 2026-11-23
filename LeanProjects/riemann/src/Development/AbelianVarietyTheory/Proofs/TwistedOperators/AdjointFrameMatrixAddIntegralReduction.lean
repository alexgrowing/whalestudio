import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SuppInd
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LocalIntegralGL
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
open Formalism.L2.DIV (kP Pl LevelP)
open Classical

namespace GlobalTheory.FrameAdjAdd

theorem frMapAdj_add_isIntM_redM : ∀ {D : D7} (S T : HSp D) (βS : GL (Fin S.rank) (Formalism.IndefR.Datum.EAf D)) (βT : GL (Fin T.rank) (Formalism.IndefR.Datum.EAf D)) (x y : WO S T),
  IsIntM (frMapAdj S T βS βT x) → IsIntM (frMapAdj S T βS βT y) →
  IsIntM (frMapAdj S T βS βT (x + y)) ∧
  ∀ PP : Pl D.host.E, redM PP (frMapAdj S T βS βT (x + y)) = redM PP (frMapAdj S T βS βT x) + redM PP (frMapAdj S T βS βT y) := by
  intro D S T βS βT x y hx hy
  have hadd : frMapAdj S T βS βT (x + y) = frMapAdj S T βS βT x + frMapAdj S T βS βT y := by
    unfold frMapAdj
    rw [Matrix.map_add (⇑(cA D)) (map_add (cA D)), Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul,
      Matrix.map_add (⇑(toEAf D)) (map_add (toEAf D)), Matrix.mul_add, Matrix.add_mul]
  have hI : IsIntM (frMapAdj S T βS βT (x + y)) := by
    intro i j
    rw [hadd]
    exact add_mem (hx i j) (hy i j)
  refine ⟨hI, fun PP => ?_⟩
  ext i j
  have h1 := hI i j
  have h2 := hx i j
  have h3 := hy i j
  simp only [redM, Matrix.add_apply, dif_pos h1, dif_pos h2, dif_pos h3]
  rw [← map_add]
  congr 1
  apply Subtype.ext
  simp [hadd]

end GlobalTheory.FrameAdjAdd
