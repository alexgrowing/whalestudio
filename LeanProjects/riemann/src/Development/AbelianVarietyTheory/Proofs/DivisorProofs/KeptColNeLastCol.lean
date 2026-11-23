import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarOIsAddHaar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DropColsInsB

noncomputable section

namespace GlobalTheory.ColFib

open GlobalTheory.StdPairLoc GlobalTheory.ColIns GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory

attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv

section Set

variable {R : Type} {a b : ℕ}

def setA (X : Matrix (Fin a) (Fin (a + (b + 2))) R) (t : Fin a → R) : Matrix (Fin a) (Fin (a + (b + 2))) R :=
  fun i j => if j = newCol a b then t i else X i j

def setS (X : Matrix (Fin a) (Fin (a + (b + 2))) R) (s : Fin a → R) : Matrix (Fin a) (Fin (a + (b + 2))) R :=
  fun i j => if j = lastCol a b then s i else X i j

end Set

variable {F : Type} [Field F] [NumberField F]

def vecInd (v : Pl F) {p : ℕ} : (Fin p → Fv F v) → ℂ := Set.indicator {t | ∀ i, t i ∈ v.adicCompletionIntegers F} 1

variable {a b : ℕ}

def extE (v : Pl F) (g : Matrix (Fin a) (Fin (a + b)) (Fv F v) → ℂ) (X : Matrix (Fin a) (Fin (a + (b + 2))) (Fv F v)) : ℂ :=
  g (dropCols X) * vecInd v (colA X) * vecInd v (colS X)

def cutS (v : Pl F) (Φ : Matrix (Fin a) (Fin (a + (b + 2))) (Fv F v) → ℂ) (X : Matrix (Fin a) (Fin (a + (b + 2))) (Fv F v)) :
    ℂ :=
  Φ (setS X 0) * vecInd v (colS X)

def fibInt (v : Pl F) (Φ : Matrix (Fin a) (Fin (a + (b + 2))) (Fv F v) → ℂ) (Y : Matrix (Fin a) (Fin (a + b)) (Fv F v)) : ℂ :=
  ∫ t, Φ (insB Y t) ∂(haarVec v a)

end GlobalTheory.ColFib

end
