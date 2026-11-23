import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwFin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NvEqOneOfIsCompact
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.TwFinGL1

theorem twisted_finiteness_gl1 : ∀ (p : ℕ) [Fact p.Prime] (r : ℕ), 0 < r → ∀ δ N : GL (Fin 1) (Qr p r),
    GlobalTheory.TwFin.TwFin (GlobalTheory.LKLoc.sig p (Q0 p) 1 r) (GlobalTheory.LKLoc.Kint p (Q0 p) 1 r) δ N := by
  intro p _ r hr δ N E
  refine ⟨{1}, fun t _ _ => ?_⟩
  obtain ⟨u, hu, k, hk, htk⟩ :=
    GlobalTheory.LKLoc.GLOneUnit.exists_decomp p (Q0 p) r inferInstance hr δ t
  exact ⟨u, hu, 1, Finset.mem_singleton_self _, k, hk, by rw [htk, mul_one]⟩

end GlobalTheory.TwFinGL1
