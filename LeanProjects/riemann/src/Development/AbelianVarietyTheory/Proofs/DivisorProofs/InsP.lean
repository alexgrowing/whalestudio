import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocPart

noncomputable section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.EvZeroStd

def insP (k : Type) [Field k] (b a' : ℕ) : Matrix (Fin (b + 2 + a')) (Fin (b + a')) k :=
  Matrix.of fun i j => if (i : ℕ) = skip 0 (b + 1) j then 1 else 0

end GlobalTheory.EvZeroStd
