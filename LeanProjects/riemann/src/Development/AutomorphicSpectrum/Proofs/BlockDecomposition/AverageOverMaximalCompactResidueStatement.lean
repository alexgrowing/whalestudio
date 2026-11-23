import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AverageOverMaximalCompactResidue
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JpUnif
open Matrix GlobalTheory.CompanionTheory.Jp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.average_over_maximal_compact_residue : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Fintype (IsLocalRing.ResidueField O)]
    (n : ℕ) (ϖ : O), Irreducible ϖ → ∀ f : GL (Ix n) (IsLocalRing.ResidueField O) → ℂ,
      avgK ϖ (fun κ => f (resK κ)) = sumG f / (Nat.card (GL (Ix n) (IsLocalRing.ResidueField O)) : ℂ) := by
  first | exact @GlobalTheory.CompanionTheory.Jp.AvgRes.avgK_res | exact GlobalTheory.CompanionTheory.Jp.AvgRes.avgK_res | (intros; apply GlobalTheory.CompanionTheory.Jp.AvgRes.avgK_res <;> assumption)
