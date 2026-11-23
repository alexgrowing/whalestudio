import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripSizesSum

noncomputable section

open GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.LeviBlockExponent GlobalTheory.CuspBlock

namespace GlobalTheory.JacLineSplit

abbrev linePlace {N : ℕ} (h : 2 ≤ N) : (Σ j : Fin 3, Fin (tripSizes 1 (N - 2) N j)) ≃ Fin N :=
  tripPlace (l := 1) (d := N - 2) (N := N) (by omega)

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def firstBlockScalar (N : ℕ) (x : kˣ) : Levi k (fun j : Fin 3 => Fin (tripSizes 1 (N - 2) N j)) :=
  MonoidHom.mulSingle (fun j : Fin 3 => GL (Fin (tripSizes 1 (N - 2) N j)) k) 0
    (Matrix.GeneralLinearGroup.scalar (Fin (tripSizes 1 (N - 2) N 0)) x)

abbrev IndAA (a a' : ℕ) (χ : Fin 2 → kˣ →* ℂˣ) : Type :=
  IndSp (pairPlace (N := a + a') ![a, a'] rfl) (ofChar (pairChar k ![a, a'] χ))

abbrev indAA (a a' : ℕ) (χ : Fin 2 → kˣ →* ℂˣ) : Representation ℂ (GL (Fin (a + a')) k) (IndAA k a a' χ) :=
  pairInd k (N := a + a') ![a, a'] rfl χ

abbrev lineKer (a a' : ℕ) (h : 2 ≤ a + a') (χ : Fin 2 → kˣ →* ℂˣ) : Submodule ℂ (IndAA k a a' χ) :=
  twKer (indAA k a a' χ) (unipRad k (linePlace h)) 1

end GlobalTheory.JacLineSplit
