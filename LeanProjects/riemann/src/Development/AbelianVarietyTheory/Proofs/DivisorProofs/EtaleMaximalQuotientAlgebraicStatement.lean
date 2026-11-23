import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleMaximalQuotientAlgebraic
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_maximal_quotient_algebraic : ∀ (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], ¬ IsField B → ∀ (f : B), f ≠ 0 → ∀ (A' : Type) [CommRing A'] [Algebra B A'] [Algebra.Etale B A'] (M : MaximalSpectrum (FractionRing (Localization.Away (algebraMap B A' f)))), ∃ _ : Algebra (RatFunc k) (FractionRing (Localization.Away (algebraMap B A' f)) ⧸ M.asIdeal), Algebra.IsAlgebraic (RatFunc k) (FractionRing (Localization.Away (algebraMap B A' f)) ⧸ M.asIdeal) := by
  first | (exact @GlobalTheory.FracAlgEtale.exists_isAlgebraic_ratFunc_residue) | (exact GlobalTheory.FracAlgEtale.exists_isAlgebraic_ratFunc_residue) | (intros; apply GlobalTheory.FracAlgEtale.exists_isAlgebraic_ratFunc_residue  <;> assumption)
