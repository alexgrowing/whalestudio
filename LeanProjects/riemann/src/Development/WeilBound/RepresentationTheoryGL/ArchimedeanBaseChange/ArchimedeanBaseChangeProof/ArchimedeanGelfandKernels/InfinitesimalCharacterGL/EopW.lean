import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.IsMultZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CasimirSignatureMemCenter
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TraceElementGelfandPolynomialFormula
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TraceElementsActByGelfandValues
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TracedQminorComatrixTruncatedInverseStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.QdetPolyMapMonicStatement
import Development.WeilBound.CoreStatements.SatakeConjugation.CapEqQdet

noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.UnitaryBC Polynomial Finset

namespace PositivityTheory.RgBcC.Bridge

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

open Classical in

def atW (w : InfinitePlace E) (x : Matrix (Fin a) (Fin a) ℂ) : Lie E a :=
  fun i j v => if v = w then x i j else (1 : Matrix (Fin a) (Fin a) ℂ) i j

def along (w : InfinitePlace E) (g : GA E a) (φ : GA E a → ℂ) : Matrix (Fin a) (Fin a) ℂ → ℂ :=
  fun x => chart φ g (atW w x)

def eopW (w : InfinitePlace E) (s : Bool) : Fin a → Fin a → Module.End ℂ (Sm E a) :=
  if s then Eop w.embedding else Eop (ComplexEmbedding.conjugate w.embedding)

def defect (t : ℕ → ℂ) (m N : ℕ) (D : ℂ[X]) : ℂ[X] :=
  (X - C (m : ℂ)) ^ (N + 1) * (D.comp (X + 1) - D) -
    D * ∑ k ∈ range (N + 1), C ((-1) ^ k * t k) * (X - C (m : ℂ)) ^ (N - k)

end PositivityTheory.RgBcC.Bridge
