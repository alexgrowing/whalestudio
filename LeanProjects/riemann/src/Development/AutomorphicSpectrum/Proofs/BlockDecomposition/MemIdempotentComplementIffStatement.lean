import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemIdempotentComplementIff
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_idempotent_complement_iff : ∀ {S : Type} [CommRing S] (P : Ideal S), P.IsPrime → ∀ x : S, x ∈ compI P ↔ ∃ e, IsIdempotentElem e ∧ e ∉ P ∧ e * x = 0 := by
  first | exact @GlobalTheory.CompanionTheory.CompIdeal.mem_compI_iff | exact GlobalTheory.CompanionTheory.CompIdeal.mem_compI_iff | (intros; apply GlobalTheory.CompanionTheory.CompIdeal.mem_compI_iff <;> assumption)
