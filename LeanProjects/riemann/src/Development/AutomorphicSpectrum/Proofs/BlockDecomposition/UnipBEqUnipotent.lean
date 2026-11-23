import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.CuspGenericWhittaker.CuspGeneric
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Whit

namespace GlobalTheory.CompanionTheory.IwasawaDict

theorem unipB_eq_unipotent : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ),
    unipB k (Fin n) = GroundTheory.Automorphic.Iwasawa.unipotent k n := by
  intro k _ _ _ _ n
  ext g
  rw [mem_unipB k, GroundTheory.Automorphic.Iwasawa.mem_unipotent k n]
  exact and_congr_left' ⟨fun h i j hij => h i j hij, fun h i j hij => h hij⟩

end GlobalTheory.CompanionTheory.IwasawaDict
