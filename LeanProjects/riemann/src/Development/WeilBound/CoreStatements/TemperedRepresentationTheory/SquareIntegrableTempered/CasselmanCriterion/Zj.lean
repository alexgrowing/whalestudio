import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanNecTemp

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

namespace Zl.JC

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def zj {h : ℕ} (d : Fin h → ℕ) (t : kˣ) (j : Fin h) : Levi k (fun a => Fin (d a)) :=
  fun a => if a ≤ j then Matrix.GeneralLinearGroup.scalar (Fin (d a)) t else 1

def blockIdx {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) (i : Fin N) : Fin h :=
  ((stdBlocks d hd).symm i).1

end Zl.JC

end
