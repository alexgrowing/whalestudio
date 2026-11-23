import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitFormLocalizationEtaleNbhd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExcisionNbhdSelf
open GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unit_form_localization_etale_nbhd : ∀ (B A₂ : Type) [CommRing B] [CommRing A₂] [Algebra B A₂] (f : B), IsExcisionNbhd B A₂ f → ∀ c : (Localization.Away (algebraMap B A₂ f))ˣ, ∃ (b₁ : B) (m : ℕ) (e : A₂), e - 1 ∈ Ideal.span {algebraMap B A₂ f} ∧ algebraMap A₂ (Localization.Away (algebraMap B A₂ f)) (algebraMap B A₂ b₁) = (c : Localization.Away (algebraMap B A₂ f)) * algebraMap A₂ (Localization.Away (algebraMap B A₂ f)) (e * algebraMap B A₂ f ^ m) := by
  first | (exact @GlobalTheory.DivUnitForm.unit_form) | (exact GlobalTheory.DivUnitForm.unit_form) | (intros; apply GlobalTheory.DivUnitForm.unit_form  <;> assumption)
