import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NondegenerateUnipotentPairingSchwartz
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousMulVec
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd GlobalTheory.SplitWeil GlobalTheory.JHMult GlobalTheory.CompanionTheory.BZShell GlobalTheory.CompanionTheory.MirPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nondegenerate_unipotent_pairing_schwartz : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (d : ℕ) (hd : 0 < d) (R R' : MRep k d) (hR' : IsSmooth R'.ρ) {V V' : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup V'] [Module ℂ V'] [Nontrivial V]
    (B : R.V →ₗ[ℂ] R'.V →ₗ[ℂ] ℂ) (hB : ∀ x v v', B (R.ρ (uM d x) v) (R'.ρ (uM d x) v') = B v v')
    (hn : ∀ v, v ≠ 0 → ∃ v', B v v' ≠ 0)
    (ι : SchF k d V →ₗ[ℂ] R.V) (hι : Function.Injective ι) (hιs : ∀ x f, ι (shiftF x f) = R.ρ (uM d x) (ι f))
    (ι' : SchF k d V' →ₗ[ℂ] R'.V) (hιs' : ∀ x f, ι' (shiftF x f) = R'.ρ (uM d x) (ι' f))
    (hr : ∀ x v, R'.ρ (uM d x) v - v ∈ LinearMap.range ι')
    (hC : ∀ f f' x, B (ι f) (ι' (shiftF x f')) = B (ι f) (ι' f')),
    False := by
  first | exact @GlobalTheory.CompanionTheory.BZShell.Radical.false_of_translation_invariant | exact GlobalTheory.CompanionTheory.BZShell.Radical.false_of_translation_invariant | (intros; apply GlobalTheory.CompanionTheory.BZShell.Radical.false_of_translation_invariant <;> assumption)
