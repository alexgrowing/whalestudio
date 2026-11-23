import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicRestrictionUnipotentSmooth
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUnipMir
open GlobalTheory.PRep GlobalTheory.BZMir GroundTheory.LocalField Matrix GlobalTheory.CompanionTheory.MirFourier
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mirabolic_restriction_unipotent_smooth : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ (Mir k n) V), IsSmooth τ → IsSmooth (τ.comp (unipMir k n)) := by
  first | exact @GlobalTheory.CompanionTheory.MirFourier.isSmooth_comp_unipMir | exact GlobalTheory.CompanionTheory.MirFourier.isSmooth_comp_unipMir | (intros; apply GlobalTheory.CompanionTheory.MirFourier.isSmooth_comp_unipMir <;> assumption)
