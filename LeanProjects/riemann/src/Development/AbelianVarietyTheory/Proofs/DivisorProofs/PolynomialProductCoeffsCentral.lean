import Mathlib
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNilRad
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffMemSubmoduleOfComplexPolyValuesMem
open Matrix GlobalTheory.TorFin

noncomputable section

namespace GlobalTheory.IntModFac

open Polynomial

def sumPoly {S : Type} [Semiring S] (n : ℕ) (f : ℕ → S) : S[X] :=
  ∑ k ∈ Finset.range (n + 1), C (f k) * X ^ k

end GlobalTheory.IntModFac

namespace GlobalTheory

open Polynomial GlobalTheory.IntModFac

end GlobalTheory
