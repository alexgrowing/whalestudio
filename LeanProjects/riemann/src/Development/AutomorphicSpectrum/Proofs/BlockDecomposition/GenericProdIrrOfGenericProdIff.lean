import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZMir

theorem genericProdIrr_of_genericProdIff :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
      GenericProdIff k → GenericProdIrr k := by
  intro k _ _ _ _ H h N x hd
  exact H h N (fun a => (x a).1) hd (fun a => (x a).2.rep.V) (fun a => (x a).rep) (fun a => (x a).2.rep.smooth)

end GlobalTheory.CompanionTheory.BZMir
