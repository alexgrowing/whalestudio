import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Unfold2

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.EisUnfold

section Join

variable {R : Type*} {m r s : ℕ}

def colJoin (y₁ : Matrix (Fin m) (Fin r) R) (y₂ : Matrix (Fin m) (Fin s) R) : Matrix (Fin m) (Fin (r + s)) R :=
  Matrix.of fun i k => Sum.elim (y₁ i) (y₂ i) (finSumFinEquiv.symm k)

def colL (y : Matrix (Fin m) (Fin (r + s)) R) : Matrix (Fin m) (Fin r) R := Matrix.of fun i j => y i (Fin.castAdd s j)

def colR (y : Matrix (Fin m) (Fin (r + s)) R) : Matrix (Fin m) (Fin s) R := Matrix.of fun i j => y i (Fin.natAdd r j)

@[simp] theorem colJoin_castAdd (y₁ : Matrix (Fin m) (Fin r) R) (y₂ : Matrix (Fin m) (Fin s) R) (i : Fin m) (j : Fin r) :
    colJoin y₁ y₂ i (Fin.castAdd s j) = y₁ i j := by
  simp [colJoin]

@[simp] theorem colJoin_natAdd (y₁ : Matrix (Fin m) (Fin r) R) (y₂ : Matrix (Fin m) (Fin s) R) (i : Fin m) (j : Fin s) :
    colJoin y₁ y₂ i (Fin.natAdd r j) = y₂ i j := by
  simp [colJoin]

@[simp] theorem colL_colJoin (y₁ : Matrix (Fin m) (Fin r) R) (y₂ : Matrix (Fin m) (Fin s) R) :
    colL (colJoin y₁ y₂) = y₁ := by
  ext i j; simp [colL]

@[simp] theorem colR_colJoin (y₁ : Matrix (Fin m) (Fin r) R) (y₂ : Matrix (Fin m) (Fin s) R) :
    colR (colJoin y₁ y₂) = y₂ := by
  ext i j; simp [colR]

@[simp] theorem colJoin_colL_colR (y : Matrix (Fin m) (Fin (r + s)) R) : colJoin (colL y) (colR y) = y := by
  ext i k
  refine Fin.addCases (fun j => ?_) (fun j => ?_) k
  · simp [colL]
  · simp [colR]

theorem colJoin_injective {y₁ y₁' : Matrix (Fin m) (Fin r) R} {y₂ y₂' : Matrix (Fin m) (Fin s) R}
    (h : colJoin y₁ y₂ = colJoin y₁' y₂') : y₁ = y₁' ∧ y₂ = y₂' :=
  ⟨by rw [← colL_colJoin y₁ y₂, h, colL_colJoin], by rw [← colR_colJoin y₁ y₂, h, colR_colJoin]⟩

def joinEquiv : Matrix (Fin m) (Fin r) R × Matrix (Fin m) (Fin s) R ≃ Matrix (Fin m) (Fin (r + s)) R where
  toFun z := colJoin z.1 z.2
  invFun y := (colL y, colR y)
  left_inv z := by simp
  right_inv y := by simp

@[simp] theorem joinEquiv_apply (z : Matrix (Fin m) (Fin r) R × Matrix (Fin m) (Fin s) R) :
    joinEquiv z = colJoin z.1 z.2 := rfl

theorem colJoin_map {R' : Type*} (f : R → R') (y₁ : Matrix (Fin m) (Fin r) R) (y₂ : Matrix (Fin m) (Fin s) R) :
    (colJoin y₁ y₂).map f = colJoin (y₁.map f) (y₂.map f) := by
  ext i k
  refine Fin.addCases (fun j => ?_) (fun j => ?_) k <;> simp

theorem colJoin_add [Add R] (y₁ y₁' : Matrix (Fin m) (Fin r) R) (y₂ y₂' : Matrix (Fin m) (Fin s) R) :
    colJoin (y₁ + y₁') (y₂ + y₂') = colJoin y₁ y₂ + colJoin y₁' y₂' := by
  ext i k
  refine Fin.addCases (fun j => ?_) (fun j => ?_) k <;> simp

theorem colJoin_neg [Neg R] (y₁ : Matrix (Fin m) (Fin r) R) (y₂ : Matrix (Fin m) (Fin s) R) :
    colJoin (-y₁) (-y₂) = -colJoin y₁ y₂ := by
  ext i k
  refine Fin.addCases (fun j => ?_) (fun j => ?_) k <;> simp

theorem colJoin_sub [Sub R] (y₁ y₁' : Matrix (Fin m) (Fin r) R) (y₂ y₂' : Matrix (Fin m) (Fin s) R) :
    colJoin (y₁ - y₁') (y₂ - y₂') = colJoin y₁ y₂ - colJoin y₁' y₂' := by
  ext i k
  refine Fin.addCases (fun j => ?_) (fun j => ?_) k <;> simp

@[simp] theorem colJoin_zero [Zero R] : colJoin (0 : Matrix (Fin m) (Fin r) R) (0 : Matrix (Fin m) (Fin s) R) = 0 := by
  ext i k
  refine Fin.addCases (fun j => ?_) (fun j => ?_) k <;> simp

end Join

variable {D : D7}

theorem rat_colJoin {m r s : ℕ} (p : Matrix (Fin m) (Fin r) D.host.E) (q : Matrix (Fin m) (Fin s) D.host.E) :
    rat (colJoin p q) = colJoin (rat p) (rat q) :=
  colJoin_map _ p q

def cellTerm (ψ : AddChar (AF D.host.F) ℂ) (V : HSp D) {r s : ℕ} (b : Matrix (Fin r) (Fin r) D.host.E)
    (a : Matrix (Fin (r + s)) (Fin (r + s)) D.host.E) (Φ : Mx D V.rank (r + s) → ℂ)
    (p : Matrix (Fin V.rank) (Fin r) D.host.E) (q : Matrix (Fin V.rank) (Fin s) D.host.E)
    (y₁ : Mx D V.rank r) (y₂ : Mx D V.rank s) : ℂ :=
  ψ (trA (Matrix.trace (inner V (rat q) y₂))) *
    (ψ (halfTr (Matrix.trace (HMul.hMul (rat b) (inner V (y₁ - rat p) (y₁ - rat p)) : Mx D r r))) *
      Φ (HMul.hMul (colJoin (rat p - y₁) (rat q)) (rat a)))

end GlobalTheory.CompanionTheory.EisUnfold

end
