import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhitKerLeComapMap

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

namespace GlobalTheory.CompanionTheory.BZNuPair

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {X : Type} [AddCommGroup X] [Module ℂ X]

def whitImg (ψ : AddChar k Circle) (d : Fin 2 → ℕ) (J : Representation ℂ (Levi k fun a => Fin (d a)) X)
    (T : Subrepresentation J) : Subrepresentation (whit2 ψ d J) :=
  ⟨T.toSubmodule.map (whitKer ψ d J).mkQ, fun g v hv => by
    obtain ⟨t, ht, rfl⟩ := hv
    exact ⟨J (firstEmb d g) t, T.apply_mem_toSubmodule _ ht, rfl⟩⟩

theorem whitImg_mono (ψ : AddChar k Circle) (d : Fin 2 → ℕ) (J : Representation ℂ (Levi k fun a => Fin (d a)) X)
    {T T' : Subrepresentation J} (h : T' ≤ T) : whitImg ψ d J T' ≤ whitImg ψ d J T :=
  Submodule.map_mono (f := (whitKer ψ d J).mkQ) h

end

end GlobalTheory.CompanionTheory.BZNuPair

end
