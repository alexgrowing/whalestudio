import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ComparableModSquareLocalization
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.comparable_mod_square_localization : ∀ {S : Type} [CommRing S] (ϖ : S) [IsAdicComplete (Ideal.span {ϖ}) S], Val0 (S ⧸ Ideal.span {ϖ ^ 2}) → ∀ P : Ideal S, P.IsPrime → ∀ f g : S ⧸ compI P, f ∈ Ideal.span {g, Ideal.Quotient.mk (compI P) ϖ ^ 2} ∨ g ∈ Ideal.span {f, Ideal.Quotient.mk (compI P) ϖ ^ 2} := by
  first | exact @GlobalTheory.CompanionTheory.CompMod.mem_span_or_mem_span | exact GlobalTheory.CompanionTheory.CompMod.mem_span_or_mem_span | (intros; apply GlobalTheory.CompanionTheory.CompMod.mem_span_or_mem_span <;> assumption)
