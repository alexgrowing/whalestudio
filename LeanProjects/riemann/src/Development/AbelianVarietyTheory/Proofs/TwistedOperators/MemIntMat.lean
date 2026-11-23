import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConstMemBddAut
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFinWeil
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsEigenSysOfHeckeLin
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.InertHomIdx

variable {D : D7}

def compW (D : D7) (w : HeightOneSpectrum (𝓞 D.host.E)) : AE D →+* w.adicCompletion D.host.E :=
  (GlobalTheory.LFun.compAt D.host.F w).comp (finPart D)

def matW (S T : HSp D) (w : HeightOneSpectrum (𝓞 D.host.E)) :
    GlobalTheory.FinWeilO.XF S T →+ Matrix (Fin T.rank) (Fin S.rank) (w.adicCompletion D.host.E) where
  toFun x := (x : WO S T).map (compW D w)
  map_zero' := by ext i j; simp [GlobalTheory.FinWeilO.XF.coe_zero]
  map_add' x y := by ext i j; simp [GlobalTheory.FinWeilO.XF.coe_add]

theorem matW_apply (S T : HSp D) (w : HeightOneSpectrum (𝓞 D.host.E)) (x : GlobalTheory.FinWeilO.XF S T) :
    matW S T w x = (x : WO S T).map (compW D w) := rfl

def intMat (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (m n : ℕ) :
    AddSubgroup (Matrix (Fin m) (Fin n) L) where
  carrier := {X | ∀ i j, X i j ∈ Formalism.UG.intL L}
  add_mem' hX hY i j := add_mem (hX i j) (hY i j)
  zero_mem' _ _ := zero_mem _
  neg_mem' hX i j := neg_mem (hX i j)

theorem mem_intMat {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {m n : ℕ}
    {X : Matrix (Fin m) (Fin n) L} : X ∈ intMat L m n ↔ ∀ i j, X i j ∈ Formalism.UG.intL L := Iff.rfl

def lmul {L : Type} [Ring L] {m n : ℕ} (g : Matrix (Fin m) (Fin m) L) :
    Matrix (Fin m) (Fin n) L →+ Matrix (Fin m) (Fin n) L where
  toFun X := g * X
  map_zero' := Matrix.mul_zero g
  map_add' := Matrix.mul_add g

theorem lmul_apply {L : Type} [Ring L] {m n : ℕ} (g : Matrix (Fin m) (Fin m) L) (X : Matrix (Fin m) (Fin n) L) :
    lmul g X = g * X := rfl

end GlobalTheory.InertHomIdx

end
