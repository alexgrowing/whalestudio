import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CmLatticeGoodModelUnramified
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModChebOm
import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement
open NumberField IsDedekindDomain Neutral.HilbertClassField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmLattice_good_model_unramified : (∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω], ∃ art : (Ω ≃ₐ[E] Ω) →* ClassGroup (𝓞 E), IsOpen (art.ker : Set (Ω ≃ₐ[E] Ω)) ∧ (∀ (A : ValuationSubring Ω) (g : Ω ≃ₐ[E] Ω), ReciprocityTheory.ChartRestriction.L1.InertiaEl A g → art g = 1) ∧ ∀ (v : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (φ : Ω ≃ₐ[E] Ω), LiesAbove A v → IsArithFrobenius A v φ → art φ = ClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩) → ReciprocityTheory.ChartRestriction.L1.ChebOmSt → Formalism.L2.Th1.CM.CM2 := by
  first | exact @GlobalTheory.ArtinClassCM.good_model | exact GlobalTheory.ArtinClassCM.good_model | (intros; apply GlobalTheory.ArtinClassCM.good_model <;> assumption)
