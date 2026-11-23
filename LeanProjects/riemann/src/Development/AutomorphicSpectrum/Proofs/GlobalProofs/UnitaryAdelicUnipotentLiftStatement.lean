import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.UnitaryAdelicUnipotentLift
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.FiniteDimensionalOfSlices
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBlockEmb
open NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.block_embedding_parabolic_compatibility : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [IsTotallyComplex E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y →
    ∀ (T : Finset (Fin r)) (k : Fin r), k ∈ T → ∀ (l d : ℕ) (h : l + d ≤ r) (ι : GlobalTheory.CuspRep.GA E d →* GAd σ J),
      GlobalTheory.BlockForms.IsBlockEmb σ J X Y h ι → k.val + 1 = l + d → 1 ≤ d →
      (∀ j : Fin r, l ≤ j.val → j.val + 1 < l + d → j ∉ T) → (l = 0 ∨ ∃ p ∈ T, p.val + 1 = l) →
      glPart σ J X Y T k = ι.range := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.BlockRange.glPart_eq_range | exact GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.BlockRange.glPart_eq_range | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.BlockRange.glPart_eq_range <;> assumption)
