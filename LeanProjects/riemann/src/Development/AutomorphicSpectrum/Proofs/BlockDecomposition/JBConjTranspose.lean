import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.IsCoreMod
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAdmOnOfFiniteDimensional
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.FiniteDimensionalOfTrivialIsAdmOn
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AdmissibleOfIwasawaDecomposition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDensityOfImmersion
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MapMemKfin

noncomputable section

open Matrix Finset GlobalTheory.OpTrace GlobalTheory.AutomorphicL2Unitary GlobalTheory.LinRed
open scoped InnerProductSpace ComplexConjugate

namespace GlobalTheory.CompanionTheory.GLK

open PositivityTheory.RgTw (Mat G th IsThetaOp)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD

variable {n : ℕ} {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℂ U]

def jB (A : Mat n) (c : ℂ) : Mat (n + 1) :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks A 0 0 (c • (1 : Matrix (Fin 1) (Fin 1) ℂ)))

def rB (m : Mat (n + 1)) : Mat n := m.submatrix Fin.castSucc Fin.castSucc

def cB (m : Mat (n + 1)) : ℂ := m (Fin.last n) (Fin.last n)

theorem jB_mul (A B : Mat n) (c d : ℂ) : jB A c * jB B d = jB (A * B) (c * d) := by
  simp only [jB, reindex_apply, submatrix_mul_equiv, fromBlocks_multiply]
  congr 1
  simp [smul_smul, mul_comm]

theorem jB_one : jB (1 : Mat n) 1 = 1 := by
  simp [jB, Matrix.fromBlocks_one]

theorem jB_add (A B : Mat n) (c d : ℂ) : jB (A + B) (c + d) = jB A c + jB B d := by
  have h := (Matrix.reindexLinearEquiv ℂ ℂ (finSumFinEquiv (m := n) (n := 1)) finSumFinEquiv).map_add
    (fromBlocks A 0 0 (c • (1 : Matrix (Fin 1) (Fin 1) ℂ))) (fromBlocks B 0 0 (d • (1 : Matrix (Fin 1) (Fin 1) ℂ)))
  simp only [Matrix.coe_reindexLinearEquiv, fromBlocks_add, add_zero, ← add_smul] at h
  exact h

def gp (n : ℕ) : Set (Mat (n + 1)) := {m | jB (rB m) (cB m) = m ∧ m.det = 1}

def sg (π : G n →* (U →L[ℂ] U)) (m : Mat (n + 1)) : U →L[ℂ] U := piM π (rB m)

def lift (X : Mat n) : Mat (n + 1) := jB X (-X.trace)

def jR : (Mat n × ℂ) →+* Mat (n + 1) where
  toFun x := jB x.1 x.2
  map_one' := jB_one
  map_mul' x y := (jB_mul x.1 y.1 x.2 y.2).symm
  map_zero' := by simp [jB]
  map_add' x y := jB_add x.1 y.1 x.2 y.2

section
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

end

end GlobalTheory.CompanionTheory.GLK

end
