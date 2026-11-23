import Mathlib
import Formalism.MirabolicMackeyTheory.StatementL

open Module NumberField IsDedekindDomain

namespace Formalism.EigenvalueLevelCeiling

open Formalism.DivisionValues

theorem idxFull_of (hMono : IdxMono) (hSc : IdxScaleIn) : IdxFull := by
  intro K _ _ _ Z _ _ _ _ _ w M Th ThK hM hTh hThK _hThM σ hσ hsc E r hE
  obtain ⟨hlat, heq⟩ := hSc K Z w ⊤ M ThK hM hThK σ hσ
  have hmono : lix w M (sc σ ThK) ≤ lix w M Th := hMono K Z w ⊤ M Th (sc σ ThK) hM hTh hlat hsc
  have hm : (lix w M (sc σ ThK) : ℝ) ≤ (lix w M Th : ℝ) := by exact_mod_cast hmono
  have hv : (lix w M (sc σ ThK) : ℝ) = (lix w M ThK : ℝ) + (finrank K Z : ℝ) * (vw w σ : ℝ) := by
    rw [heq]
    push_cast
    rw [finrank_top]
  linarith

end Formalism.EigenvalueLevelCeiling
