import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsLatIntVec

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS

theorem isLat_lam_of_matrix (K : Type) [Field K] [NumberField K] (m : ℕ)
    (c : Matrix (Fin m) (Fin m) K) : IsLat (lam c) := by
  have hL : IsLat (intVec K m) := isLat_intVec m
  refine ⟨Submodule.FG.sup hL.1 (Submodule.FG.map _ hL.1), ?_⟩
  rw [eq_top_iff, ← hL.2]
  exact Submodule.span_mono (fun v hv => (le_sup_left : intVec K m ≤ lam c) hv)

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
