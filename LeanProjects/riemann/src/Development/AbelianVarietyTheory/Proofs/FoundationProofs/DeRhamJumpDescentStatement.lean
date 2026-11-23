import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DeRhamJumpDescent
import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.SelmerWindowSums
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankCyclotomicExtAndCyclotomicCharSurjective
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.de_rham_jump_descent : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K K' LL : FinExt l) (h : K.1 ≤ K'.1) (Y : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (u : ℤ), (DdR (P.PD K') (Y.ρ.comp (Subgroup.inclusion (GK_le h))) ⊓ FilV (P.PD K') (LL := ↥LL.1) (V := Y.V) (u + 1) ≠ DdR (P.PD K') (Y.ρ.comp (Subgroup.inclusion (GK_le h))) ⊓ FilV (P.PD K') (LL := ↥LL.1) (V := Y.V) u) ↔ (DdR (P.PD K) Y.ρ ⊓ FilV (P.PD K) (LL := ↥LL.1) (V := Y.V) (u + 1) ≠ DdR (P.PD K) Y.ρ ⊓ FilV (P.PD K) (LL := ↥LL.1) (V := Y.V) u) := by
  first | exact @GlobalTheory.JumpDescent.jump_iff | exact GlobalTheory.JumpDescent.jump_iff | (intros; apply GlobalTheory.JumpDescent.jump_iff <;> assumption)
