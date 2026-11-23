import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsMahler
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory

theorem DefectConstStep.proof (h1 : DefectSymm.Statement) (h2 : ProperSymmCycle.Statement)
    (h3 : AdmissibleAE.Statement) (h4 : CycleSectionData.Statement) : DefectConstStep.Statement := by
  intro e hA n δ h Z f u u' hd hu hu'
  have hdu := h4 n e δ Z f u hd hu
  have hdu' := h4 n e δ Z f u' hd hu'
  have rel : ∀ {Y : ProjCycle ℂ n} {g : ℕ} {d : ℕ} {F : MvPolynomial (Fin (g + 1) × Fin n) ℂ},
      IsChowCycleData Y g d F → ∀ W ∈ Y.support, IsRelevant W :=
    fun hY W hW => (hY.prime W hW).isRelevant
  have hae := (h3 n Z (rel hd)).and ((h3 n _ (rel hdu)).and (h3 n _ (rel hdu')))
  obtain ⟨v, hvZ, hvu, hvu'⟩ := hae.exists
  have s1 : IsAdmissible (cycleSection Z v) u := h2 n Z u v hd.prime hu hvZ hvu
  have s2 : IsAdmissible (cycleSection Z v) u' := h2 n Z u' v hd.prime hu' hvZ hvu'
  rw [h1 e hA n δ h Z f u v hd hu hvZ hvu s1, h1 e hA n δ h Z f v u' hd hvZ hu' s2 hvu']

end GroundTheory.Heights₂.Heights
