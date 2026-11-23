import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiltrationRelIndexEqResidueCardPow
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DiagPairs
open GlobalTheory.PRep GlobalTheory.SmGL Matrix ValuativeRel GlobalTheory.CompanionTheory.IwJac
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.filtration_relIndex_eq_residue_card_pow : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ϖ : kˣ), ord k ϖ = 1 → ∀ x : Fin n → ℤ, StrictAnti x → ∀ d : ℕ, (filt ϖ x (d + 1)).relIndex (filt ϖ x d) = Nat.card 𝓀[k] ^ ∑ p ∈ diagPairs n d, (x p.1 - x p.2).toNat := by
  first | exact @GlobalTheory.CompanionTheory.IwJac.relIndex_filt_succ | exact GlobalTheory.CompanionTheory.IwJac.relIndex_filt_succ | (intros; apply GlobalTheory.CompanionTheory.IwJac.relIndex_filt_succ <;> assumption)
