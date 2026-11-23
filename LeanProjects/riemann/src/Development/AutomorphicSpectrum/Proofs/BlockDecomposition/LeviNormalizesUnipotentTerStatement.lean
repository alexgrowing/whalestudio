import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviNormalizesUnipotentTer
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipMinSubsetMinParOne
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov GlobalTheory.CompanionTheory.ParCocompact
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_normalizes_unipotent_ter : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ m ∈ leviMin σ J X Y, ∀ u ∈ unipMin σ J X, m⁻¹ * u * m ∈ unipMin σ J X := by
  first | exact @GlobalTheory.CompanionTheory.ParCocompact.UnipNormal.leviMin_normalises_unipMin | exact GlobalTheory.CompanionTheory.ParCocompact.UnipNormal.leviMin_normalises_unipMin | (intros; apply GlobalTheory.CompanionTheory.ParCocompact.UnipNormal.leviMin_normalises_unipMin <;> assumption)
