import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeBelowComplexEmbeddingLabelIsMaximalCard
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueEqZeroIffV
open NumberField MvPowerSeries IsLocalRing ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes GlobalTheory.PrimePart
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primeBelowComplexEmbeddingLabel_isMaximal_card : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (c : Coeff l) (p : ℕ) [Fact p.Prime] (T : CDVR) (io : c.F →+* T.Fr) (X : ValExt T p), ∀ τ : E →+* ℂ, (primeBelow io X τ).IsMaximal ∧ ∃ h : ℕ, 0 < h ∧ Nat.card (𝓞 E ⧸ primeBelow io X τ) = p ^ h := by
  first | exact @GlobalTheory.PrimePart.primeBelow_isMaximal_card | exact GlobalTheory.PrimePart.primeBelow_isMaximal_card | (intros; apply GlobalTheory.PrimePart.primeBelow_isMaximal_card <;> assumption)
