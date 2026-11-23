import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalMirabolicInvariantPairingScalar
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousMulVec
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd GlobalTheory.SplitWeil GlobalTheory.JHMult GlobalTheory.CompanionTheory.BZShell GlobalTheory.CompanionTheory.MirPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidal_mirabolic_invariant_pairing_scalar : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (m : ℕ) (σ : IrrRep (GL (Fin (m + 1)) k)) (hc : IsCuspidal σ.ρ)
    (β : σ.V →ₗ[ℂ] smoothPart σ.ρ.dual →ₗ[ℂ] ℂ)
    (hβ : ∀ g : GL (Fin (m + 1)) k,
      (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k).mulVec (Pi.single (Fin.last m) 1) = Pi.single (Fin.last m) 1 →
      ∀ a l, β (σ.ρ g a) (contra σ.ρ g l) = β a l),
    ∃ c : ℂ, ∀ a l, β a l = c * (l : Module.Dual ℂ σ.V) a := by
  first | exact @GlobalTheory.CompanionTheory.StabForm.form_unique | exact GlobalTheory.CompanionTheory.StabForm.form_unique | (intros; apply GlobalTheory.CompanionTheory.StabForm.form_unique <;> assumption)
