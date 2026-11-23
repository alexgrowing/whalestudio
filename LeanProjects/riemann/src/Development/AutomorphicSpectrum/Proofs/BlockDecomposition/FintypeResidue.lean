import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.GaugeTopology.UBranch
import GroundTheory.AutomorphicForms.GL2.GJUnramifiedCosets

noncomputable section

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.GLnLocal
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.LFUDom

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

instance fintypeResidue : Fintype 𝓀[F] := Fintype.ofFinite _

theorem det_rowMat (i j : ℕ) (c : F) :
    (!![(GLnLocal.uniformizer F : F) ^ i, c; 0, (GLnLocal.uniformizer F : F) ^ j]).det ≠ 0 := by
  rw [Matrix.det_fin_two_of]
  have h : (GLnLocal.uniformizer F : F) ≠ 0 := Cartan.uniformizer_ne_zero F
  simpa using mul_ne_zero (pow_ne_zero i h) (pow_ne_zero j h)

def rowRep (i j : ℕ) (c : Fin j → 𝓀[F]) : GL (Fin 2) F :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero _ (det_rowMat i j (digitSum F j c))

theorem coe_rowRep (i j : ℕ) (c : Fin j → 𝓀[F]) :
    (rowRep i j c : Matrix (Fin 2) (Fin 2) F) =
      !![(GLnLocal.uniformizer F : F) ^ i, digitSum F j c; 0, (GLnLocal.uniformizer F : F) ^ j] :=
  rfl

end GlobalTheory.CompanionTheory.LFUDom
