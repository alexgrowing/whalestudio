import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowForms.StatementsSectionOrder
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PChowFormSection
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem SpecFirstMemIncIdeal.proof : SpecFirstMemIncIdeal.Statement := by
  intro F _ n e I W f t hf hIW ht
  rw [mem_incIdeal_iff]
  rintro v ⟨x, hx0, hxW, hv⟩
  let w : Fin (e + 1) × Fin n → AlgebraicClosure F := fun ij =>
    Fin.cases (motive := fun _ => AlgebraicClosure F) (algebraMap F (AlgebraicClosure F) (t ij.2))
      (fun i => v (i, ij.2)) ij.1
  have hw : w ∈ incidence I (e + 1) := by
    refine ⟨x, hx0, fun g hg => hxW g (hIW hg), fun i => ?_⟩
    induction i using Fin.cases with
    | zero =>
      have h := hxW _ ht
      simpa [w, linForm, map_sum, aeval_X, aeval_C] using h
    | succ i => simpa [w] using hv i
  have hfw : aeval w f = 0 := (hf.2 f).mpr dvd_rfl w hw
  have hev : aeval v (specFirst f t) = aeval w f := by
    rw [specFirst, aeval_bind₁]
    congr 2
    funext ij
    obtain ⟨i, j⟩ := ij
    induction i using Fin.cases with
    | zero => simp [specFirstVar, w]
    | succ i => simp [specFirstVar, w]
  rw [hev, hfw]

end GroundTheory.Heights₂.Heights
