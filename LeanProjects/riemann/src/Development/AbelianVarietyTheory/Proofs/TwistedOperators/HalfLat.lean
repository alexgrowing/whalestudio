import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConstMemBddAut
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFinWeil
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemHomLatticeIffIntegralMatrixSplitChart
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemLatHatIffOfSupport
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinPartIdemMulMemIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitProjAdeleComponentChartProperties
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceMatrixCoordinateOnHalf
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitIdempotentPrimeProjectionCorrespondence
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsMatrixOfIsLattice
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOfBasis
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSplitChartSplitChart
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open GlobalTheory.SplitHecke GlobalTheory.LFun.ConjPlace GlobalTheory.AdelicU

namespace GlobalTheory.SplitIdx

variable {D : D7}

def intMat (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (m n : ℕ) :
    AddSubgroup (Matrix (Fin m) (Fin n) (v.adicCompletion F)) where
  carrier := {y | ∀ i j, y i j ∈ v.adicCompletionIntegers F}
  add_mem' hx hy i j := add_mem (hx i j) (hy i j)
  zero_mem' _ _ := zero_mem _
  neg_mem' hx i j := neg_mem (hx i j)

def mulL {K : Type} [CommRing K] {m n : ℕ} (P : Matrix (Fin m) (Fin m) K) :
    Matrix (Fin m) (Fin n) K →+ Matrix (Fin m) (Fin n) K :=
  AddMonoidHom.mk' (fun y => P * y) (Matrix.mul_add P)

def halfLat (S T : HSp D) (e : AE D) : AddSubgroup (WO S T) :=
  (latO S T (frameLat S) (frameLat T) fun _ => True) ⊓ GlobalTheory.PlaceModel.half S T e

def actL (S T : HSp D) (h : GA D T) : WO S T →+ WO S T :=
  AddMonoidHom.mk' (actO S T 1 h) fun x y => by simp only [actO, Matrix.mul_add, Matrix.add_mul]

end GlobalTheory.SplitIdx

end
