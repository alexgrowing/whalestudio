import Formalism.WachLatticeTwists.TorsionKernelSplitting.Statement
import Formalism.WachLatticeTwists.CoprimeLiftBounds.CoprimeLiftProofs.TheoremNFiveTopHolds
import Formalism.WachLatticeTwists.TorsionLengthCounts.RowCol
import Formalism.WachLatticeTwists.TorsionLengthCounts.SubmoduleLengthBoundStatement
import Formalism.WachLatticeTwists.TorsionLengthCounts.CardFilterAddLeOfNone

open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.JS

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR

theorem rowCost : StatRowCost := by
  intro O _ _ _ Cs _ _ Fs Im rr _ ℓ e c J hfin hlift hH0 hrk
  have hcol := Formalism.RepresentationBoundsCohomology.rowColength O Fs (Im.comap Fs.subtype) ℓ e
    (fun x => by
      rw [Submodule.mem_comap]
      exact hlift x.1 x.2)
  obtain ⟨H, hHk, hHt⟩ := hH0
  have htor := Formalism.RepresentationBoundsCohomology.submoduleLengthBound_statement O rr H ℓ c hHk
  refine hcol.trans ?_
  have hrk' : (Module.finrank O Fs : ℕ∞) ≤ (J : ℕ∞) := by exact_mod_cast hrk
  gcongr
  exact hHt.trans htor

theorem splitFold : StatSplitFold := by
  intro v what₂ cols conj lenRow a x c h y₁ y₂ j J R hk hrows hj hL
  refine hk.trans ?_
  have h1 : ∑ w ∈ what₂, lenRow w ≤ ∑ w ∈ cols, lenRow (conj w) := by
    rw [hrows]
    exact Finset.sum_image_le_of_nonneg (fun _ _ => bot_le)
  have h2 : ∑ w ∈ what₂, lenRow w + ∑ w ∈ cols, (a w + (j w : ℕ∞) * x w + c w + h w) ≤
      ∑ w ∈ cols, (a w + (J w : ℕ∞) * x w + c w + h w + y₁ w + y₂ w) := by
    calc ∑ w ∈ what₂, lenRow w + ∑ w ∈ cols, (a w + (j w : ℕ∞) * x w + c w + h w)
        ≤ ∑ w ∈ cols, lenRow (conj w) + ∑ w ∈ cols, (a w + (j w : ℕ∞) * x w + c w + h w) :=
          add_le_add h1 le_rfl
      _ = ∑ w ∈ cols, ((a w + (j w : ℕ∞) * x w + c w + h w) + lenRow (conj w)) := by
          rw [add_comm, ← Finset.sum_add_distrib]
      _ ≤ ∑ w ∈ cols, (a w + (J w : ℕ∞) * x w + c w + h w + y₁ w + y₂ w) := by
          refine Finset.sum_le_sum fun w hw => ?_
          rw [add_assoc (a w + (J w : ℕ∞) * x w + c w + h w)]
          have hjw : (j w : ℕ∞) ≤ (J w : ℕ∞) := by exact_mod_cast hj w hw
          have hLw := hL w hw
          gcongr
  gcongr

end Formalism.RepresentationBoundsCohomology.JS
