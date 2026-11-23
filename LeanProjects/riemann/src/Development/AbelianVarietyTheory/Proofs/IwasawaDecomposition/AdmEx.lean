import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleModelsOfHtBound
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ScaleZeroComp

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo

namespace GlobalTheory.ShFam.Pad

theorem admEx {D : D7} {A : Amb D} {N j : ℕ} (S : Sig A N j) (κ : Lv A) : AdmEx S κ :=
  admEx_of_htBound HTBound.htBound D A N j S κ

end GlobalTheory.ShFam.Pad
