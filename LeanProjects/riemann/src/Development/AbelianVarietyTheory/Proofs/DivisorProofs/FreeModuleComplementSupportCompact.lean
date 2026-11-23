import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SupportOfQuotientFlatModule
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.free_module_complement_support_compact : ∀ (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Flat R M] (r : ℕ), (∀ p : PrimeSpectrum R, Module.rankAtStalk M p = r) → ∀ s : Fin r → M, IsCompact (Module.support R (M ⧸ Submodule.span R (Set.range s)))ᶜ := by
  first | (exact @GlobalTheory.isCompact_compl_support_quotient_span) | (exact GlobalTheory.isCompact_compl_support_quotient_span) | (intros; apply GlobalTheory.isCompact_compl_support_quotient_span  <;> assumption)
