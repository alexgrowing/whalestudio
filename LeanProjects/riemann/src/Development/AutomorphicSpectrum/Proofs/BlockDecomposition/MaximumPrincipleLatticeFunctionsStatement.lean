import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MaximumPrincipleLatticeFunctions
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousMulVec
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsClopenCoset
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ZpowMulVec
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd GlobalTheory.SplitWeil GlobalTheory.JHMult GlobalTheory.CompanionTheory.BZShell GlobalTheory.CompanionTheory.MirPair GlobalTheory.CompanionTheory.BZCore
open scoped Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.maximum_principle_lattice_functions : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {d : ℕ} (hd : 0 < d) (z : GL (Fin d) k) (ϖ : k) (hz : (z : Matrix (Fin d) (Fin d) k) = ϖ • (1 : Matrix (Fin d) (Fin d) k)) (hϖ : ValuativeRel.valuation k ϖ < 1) (hϖ0 : ϖ ≠ 0) (F : COSub k d → (Fin d → k) → ℂ) (c : ℂ), Refines F → (∀ (L : COSub k d) (x l : Fin d → k), l ∈ L.sub → F L (x + l) = F L x) → (∀ (L : COSub k d) (x : Fin d → k), F (L.act z) ((z : Matrix (Fin d) (Fin d) k).mulVec x) = F L x) → (∀ x : Fin d → k, x ≠ 0 → ∃ s : ℕ, ∀ y : Fin d → k, y - x ∈ (latZ z (s : ℤ)).sub → ∀ r : ℕ, s ≤ r → F (latZ z (r : ℤ)) y = c) → ∀ (r : ℕ) (x : Fin d → k), F (latZ z (r : ℤ)) x = c := by
  first | exact @GlobalTheory.CompanionTheory.BZCore.MaxPrin.eq_const | exact GlobalTheory.CompanionTheory.BZCore.MaxPrin.eq_const | (intros; apply GlobalTheory.CompanionTheory.BZCore.MaxPrin.eq_const <;> assumption)
