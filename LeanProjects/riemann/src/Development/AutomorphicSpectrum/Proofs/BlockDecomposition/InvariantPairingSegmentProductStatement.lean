import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InvariantPairingSegmentProduct
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousMulVec
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd GlobalTheory.SplitWeil GlobalTheory.JHMult GlobalTheory.CompanionTheory.BZShell GlobalTheory.CompanionTheory.MirPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariant_pairing_segment_product : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (m : ℕ) (σ : IrrRep (GL (Fin (m + 1)) k)) (hc : IsCuspidal σ.ρ)
    (hirr : (multiProd (GlobalTheory.Published.consecBlocks 2 (m + 1)) (segTerm σ.ρ 2)).IsIrreducible),
    ∃ B : ((((gOf σ).tw 1).prod (gOf σ)).cast (size_eq m)).V →ₗ[ℂ]
        (((gDual σ).prod ((gDual σ).tw (-1))).cast (size_eq m)).V →ₗ[ℂ] ℂ,
      (∀ g v v', B ((((gOf σ).tw 1).prod (gOf σ)).cast (size_eq m) |>.ρ g v)
        (((gDual σ).prod ((gDual σ).tw (-1))).cast (size_eq m) |>.ρ g v') = B v v') ∧
      ∀ v, v ≠ 0 → ∃ v', B v v' ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.BZShell.SwapPair.exists_invariant_pairing | exact GlobalTheory.CompanionTheory.BZShell.SwapPair.exists_invariant_pairing | (intros; apply GlobalTheory.CompanionTheory.BZShell.SwapPair.exists_invariant_pairing <;> assumption)
