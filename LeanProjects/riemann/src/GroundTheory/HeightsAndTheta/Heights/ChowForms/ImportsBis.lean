import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowForms.StatementsSectionOrder
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def ChartIncDomain.Statement : Prop :=
  ∀ (F : Type) [Field F] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) F)) (t : Fin n → F),
    IsProjPrime I → linForm t ∉ I →
      IsDomain (ChartInc I t e) ∧ RingHom.ker (chartX I t e) = I ⊔ Ideal.span {linForm t - 1}

def ChartKernel.Statement : Prop :=
  ∀ (F : Type) [Field F] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) F)) (t : Fin n → F),
    IsProjPrime I → linForm t ∉ I →
      RingHom.ker (algebraMap (MvPolynomial (Fin e × Fin n) F) (ChartInc I t e)) = incIdeal I e

section Inhabitants

theorem ChartIncDomain.hypotheses_inhabited :
    IsProjPrime (⊥ : Ideal (MvPolynomial (Fin 2) ℚ)) ∧ linForm tLine ∉ (⊥ : Ideal (MvPolynomial (Fin 2) ℚ)) :=
  ⟨LineChowForm.isProjPrime_line, linForm_tLine_not_mem_bot⟩

theorem ChartKernel.hypotheses_inhabited :
    IsProjPrime (⊥ : Ideal (MvPolynomial (Fin 2) ℚ)) ∧ linForm tLine ∉ (⊥ : Ideal (MvPolynomial (Fin 2) ℚ)) :=
  ⟨LineChowForm.isProjPrime_line, linForm_tLine_not_mem_bot⟩

end Inhabitants

end

end GroundTheory.Heights₂.Heights
