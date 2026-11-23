import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RouteSeesaw

variable {D : D7}

def adjM (S B : HSp D) (y : Mx D B.rank S.rank) : Mx D S.rank B.rank :=
  HMul.hMul (HMul.hMul ((S.gram⁻¹).map (incA D) : Matrix (Fin S.rank) (Fin S.rank) (AE D))
    ((y.map (cA D))ᵀ : Matrix (Fin S.rank) (Fin B.rank) (AE D))) (B.gram.map (incA D) : Matrix (Fin B.rank) (Fin B.rank) (AE D))

theorem adjM_zero (S B : HSp D) : adjM S B 0 = 0 := by
  have e : ((0 : Mx D B.rank S.rank).map (cA D)) = 0 := by ext a b; simp
  simp only [adjM, e, transpose_zero, Matrix.mul_zero, Matrix.zero_mul]

theorem adjM_add (S B : HSp D) (y z : Mx D B.rank S.rank) : adjM S B (y + z) = adjM S B y + adjM S B z := by
  have e : (y + z).map (cA D) = y.map (cA D) + z.map (cA D) := by
    ext a b; simp
  simp only [adjM, e, transpose_add, Matrix.mul_add, Matrix.add_mul]

def topR {A B : HSp D} {n : ℕ} (x : Matrix (Fin (A.rank + B.rank)) (Fin n) (AE D)) : Mx D A.rank n :=
  x.submatrix (Fin.castAdd B.rank) id

def botR {A B : HSp D} {n : ℕ} (x : Matrix (Fin (A.rank + B.rank)) (Fin n) (AE D)) : Mx D B.rank n :=
  x.submatrix (Fin.natAdd A.rank) id

def box2 {S A B : HSp D} (φ : WO S A → ℂ) (φ' : WO S B → ℂ) : WO S (GlobalTheory.Doubling.hsum A B) → ℂ :=
  fun x => φ (topR (A := A) (B := B) x) * φ' (botR (A := A) (B := B) x)

theorem externalProductOnHermitianSum_add_left {S A B : HSp D} (φ₁ φ₂ : WO S A → ℂ) (φ' : WO S B → ℂ) :
    box2 (φ₁ + φ₂) φ' = box2 φ₁ φ' + box2 φ₂ φ' := by
  funext x; simp [box2, add_mul]

theorem externalProductOnHermitianSum_smul_left {S A B : HSp D} (c : ℂ) (φ : WO S A → ℂ) (φ' : WO S B → ℂ) :
    box2 (c • φ) φ' = c • box2 φ φ' := by
  funext x; simp [box2, mul_assoc]

example {S A B : HSp D} (φ : WO S A → ℂ) (x : WO S (GlobalTheory.Doubling.hsum A B)) :
    box2 (A := A) (B := B) φ (fun _ => 1) x = φ (topR (A := A) (B := B) x) := mul_one _

end GlobalTheory.RouteSeesaw

end
