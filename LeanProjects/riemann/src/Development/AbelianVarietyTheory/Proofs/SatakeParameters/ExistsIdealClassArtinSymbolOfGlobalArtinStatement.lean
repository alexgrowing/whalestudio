import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIdealClassArtinSymbolOfGlobalArtin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModGDefs
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
open NumberField IsDedekindDomain Neutral.HilbertClassField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_idealClass_artinSymbol_of_globalArtin : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω], ∃ art : (Ω ≃ₐ[E] Ω) →* ClassGroup (𝓞 E), IsOpen (art.ker : Set (Ω ≃ₐ[E] Ω)) ∧ (∀ (A : ValuationSubring Ω) (g : Ω ≃ₐ[E] Ω), ReciprocityTheory.ChartRestriction.L1.InertiaEl A g → art g = 1) ∧ ∀ (v : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (φ : Ω ≃ₐ[E] Ω), LiesAbove A v → IsArithFrobenius A v φ → art φ = ClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩ := by
  first | exact @GlobalTheory.IdealArtinSymbol.exists_artinSymbol | exact GlobalTheory.IdealArtinSymbol.exists_artinSymbol | (intros; apply GlobalTheory.IdealArtinSymbol.exists_artinSymbol <;> assumption)
