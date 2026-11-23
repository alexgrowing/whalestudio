import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneMemGoodCT

noncomputable section

open NumberField GlobalTheory.CuspRep

namespace GlobalTheory.CompanionTheory.CTFin

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

def capR (r s : ℕ) (τ : E →+* ℂ) (u : ℂ) : Module.End ℂ (Sm E (r + s)) :=
  Formalism.REAL.qdet (fun i j : Fin r => Eop (a := r + s) τ (Fin.castAdd s i) (Fin.castAdd s j)) (u + ((r : ℂ) - 1) / 2)

def capS (r s : ℕ) (τ : E →+* ℂ) (u : ℂ) : Module.End ℂ (Sm E (r + s)) :=
  Formalism.REAL.qdet (fun i j : Fin s => Eop (a := r + s) τ (Fin.natAdd r i) (Fin.natAdd r j)) (u + ((s : ℂ) - 1) / 2)

end GlobalTheory.CompanionTheory.CTFin

end
