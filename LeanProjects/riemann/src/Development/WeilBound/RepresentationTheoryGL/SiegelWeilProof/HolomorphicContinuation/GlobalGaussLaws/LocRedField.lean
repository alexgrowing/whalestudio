import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocalL2IsometryAlt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDecompositionUnitary
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelParabolicUnnMatrixBlockUpperTriangular
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.AtTauExUniqueHolds

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

variable {D : D7} {n : ℕ}

def genSet (D : D7) (n : ℕ) : Set (G D n) :=
  {g | (∃ b, mat g = blk4 1 b 0 1) ∨ (∃ a d, mat g = blk4 a 0 0 d) ∨ (∃ c, mat g = blk4 1 0 c 1)}

def blkDm {R : Type} (M : Matrix (Fin (n + n)) (Fin (n + n)) R) : Matrix (Fin n) (Fin n) R :=
  (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₂

def eI {R : Type} [CommRing R] (I : Finset (Fin n)) : Matrix (Fin n) (Fin n) R :=
  Matrix.diagonal fun i => if i ∈ I then 1 else 0

def wIm {R : Type} [CommRing R] (I : Finset (Fin n)) : Matrix (Fin (n + n)) (Fin (n + n)) R :=
  blk4 (1 - eI I) (eI I) (-eI I) (1 - eI I)

def J2 (R : Type) [CommRing R] (n : ℕ) : Matrix (Fin (n + n)) (Fin (n + n)) R := blk4 0 1 (-1) 0

def UnitD : Prop :=
  ∀ (D : D7) (n : ℕ) (g : G D n), IsUnit (blkDm (mat g)).det → g ∈ Subgroup.closure (genSet D n)

def PIn : Prop := ∀ (D : D7) (n : ℕ), ∀ p ∈ P D n, p ∈ Subgroup.closure (genSet D n)

def KIn : Prop := ∀ (D : D7) (n : ℕ), ∀ k ∈ K D n, k ∈ Subgroup.closure (genSet D n)

def LocRedField : Prop :=
  ∀ (k : Type) [Field k] (σ : k →+* k), (∀ a, σ (σ a) = a) → ∀ (n : ℕ) (g : GL (Fin (n + n)) k),
    g ∈ Formalism.UG.UJ σ (J2 k n) → ∃ I : Finset (Fin n), IsUnit (blkDm ((g : Matrix (Fin (n + n)) (Fin (n + n)) k) * wIm I)).det

def LocRedSplit : Prop :=
  ∀ (k : Type) [Field k] (n : ℕ) (g : GL (Fin (n + n)) k), ∃ (a d : GL (Fin n) k) (I : Finset (Fin n)),
    IsUnit (blkDm ((g : Matrix (Fin (n + n)) (Fin (n + n)) k) * blk4 a.1 0 0 d.1 * wIm I)).det

def KInInf : Prop :=
  ∀ (D : D7) (n : ℕ), ∀ k ∈ K D n, (mat k).map (finPart D) = 1 → k ∈ Subgroup.closure (genSet D n)

def KInFin : Prop :=
  ∀ (D : D7) (n : ℕ), ∀ k ∈ K D n, (∀ τ, (mat k).map (Formalism.IndefR.Eqv.psiT D τ) = 1) → k ∈ Subgroup.closure (genSet D n)

end PositivityTheory.Rg.Sw.Glob
