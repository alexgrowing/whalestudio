import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUMOfMem
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemTwKerIffAverage
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocallyConstantModulus

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPsiPG

theorem exists_Qp_mul_KO : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (g : GL (Fin (i + t)) k), ∃ q : Qp k i t, ∃ κ ∈ GlobalTheory.SplitWeil.KO k (Fin (i + t)), g = (q : GL (Fin (i + t)) k) * κ := by
  intro k _ _ _ _ i t g
  obtain ⟨u, l, w, hw, hg⟩ := GlobalTheory.SmGL.UnitInd.exists_iwasawa
    (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum (rfl : i + t = i + t))) g
  refine ⟨⟨(u : GL (Fin (i + t)) k) * GlobalTheory.SmGL.leviEmb k _ l, ?_⟩, w, hw, hg⟩
  exact Subgroup.mul_mem _ (GlobalTheory.SmGL.unipRad_le_parab k _ u.2)
    (GlobalTheory.SmGL.leviEmb_mem_parab k _ l)

end GlobalTheory.CompanionTheory.BZPsiPG
