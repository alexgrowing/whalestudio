import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogarithmicGroupLawSplitByIdempotent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueEqZeroIffV
open NumberField MvPowerSeries IsLocalRing ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes GlobalTheory.PrimePart
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.logarithmic_group_law_split_by_idempotent : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)), ∀ (d d' : ℕ) (G : LogFGL v d) (I : Matrix (Fin d) (Fin d') C) (P : Matrix (Fin d') (Fin d) C), (∀ a b, IsIntV v (I a b)) → (∀ a b, IsIntV v (P a b)) → P * I = 1 → (∃ φ, IsIntHom G G φ (I * P)) → (∃ ψ, IsIntHom G G ψ (1 - I * P)) → ∃ G' : LogFGL v d', (∃ j, IsIntHom G' G j I) ∧ ∃ q, IsIntHom G G' q P := by
  first | exact @GlobalTheory.IdemImage.exists_image | exact GlobalTheory.IdemImage.exists_image | (intros; apply GlobalTheory.IdemImage.exists_image <;> assumption)
