import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.DeterminantPowerSmoothness.GtCharZero
import Development.AbelianVarietyTheory.Definitions.Foundations.TracePowApply

noncomputable section

open Matrix MvPolynomial

namespace PositivityTheory.RgBcC.Cxd2

open PositivityTheory.RgTw (Mat)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def Et (lam : Fin n → ℤ) : Matrix (Fin n) (Fin n) (Module.End ℂ (MvPolynomial (Fin n × Fin n) ℂ)) :=
  GlobalTheory.Mem.Gelf.rowE ℂ n n + (((dw lam).detShift : ℤ) : ℂ) • (1 : Matrix (Fin n) (Fin n) (Module.End ℂ (MvPolynomial (Fin n × Fin n) ℂ)))

def At (lam : Fin n → ℤ) : Matrix (Fin n) (Fin n) (Matrix (Jd n lam) (Jd n lam) ℂ) :=
  Matrix.of fun a b i j => Cxc.extL lam i (Et lam a b ((wb lam j : Formalism.BasicNotions.nablaSq ℂ n (dw lam)) : MvPolynomial (Fin n × Fin n) ℂ))

def AtTrace : Prop := ∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam → ∀ k : ℕ,
  (At lam ^ k).trace = GlobalTheory.Dec.gelfVal (infOf lam true) k • (1 : Matrix (Jd n lam) (Jd n lam) ℂ)

def AtTraceT : Prop := ∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam → ∀ k : ℕ,
  ((Matrix.of fun a b => -(At lam b a)) ^ k).trace = GlobalTheory.Dec.gelfVal (infOf lam false) k • (1 : Matrix (Jd n lam) (Jd n lam) ℂ)

def AtDer : Prop := ∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam → ∀ Y : Mat n,
  fderiv ℝ (Rm lam) 1 Y = ∑ a, ∑ b, Y a b • At lam a b

end PositivityTheory.RgBcC.Cxd2
