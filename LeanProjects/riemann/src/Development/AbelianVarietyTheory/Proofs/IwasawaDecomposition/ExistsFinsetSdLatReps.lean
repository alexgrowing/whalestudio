import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ThDistC
import Formalism.LocalToGlobal.Columns.DecoFin
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinAlgOfFinite

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Col2.JetEx

namespace GlobalTheory.Mem.Col2.JetEx

theorem exists_finset_sdLat_reps : ∀ (X : Fields), X.Ok → ∀ n : ℕ, ∃ T : Finset (Submodule (𝓞 X.E) (Sp X.E n)), (∀ N ∈ T, IsSdLat N) ∧ ∀ N : Submodule (𝓞 X.E) (Sp X.E n), IsSdLat N → ∃ N₀ ∈ T, ∃ γ : UF X.E n, N = gmap γ.1 N₀ := by
  intro X hX n
  obtain ⟨s, hs, H⟩ := unimod_finite (posStar_of_conj hX.conjE) n
  refine ⟨s, hs, fun N hN => ?_⟩
  obtain ⟨N₀, h₀, g, hg, e⟩ := H N hN.1 hN.2
  exact ⟨N₀, h₀, ⟨g, hg⟩, e.symm⟩

end GlobalTheory.Mem.Col2.JetEx
