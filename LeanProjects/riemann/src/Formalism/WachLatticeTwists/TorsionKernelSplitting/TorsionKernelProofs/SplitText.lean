import Formalism.WachLatticeTwists.TorsionKernelSplitting.TorsionKernelProofs.TheoremNFiveTopSplitHZero
import Formalism.WachLatticeTwists.TorsionKernelSplitting.TorsionKernelProofs.KerTors

open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.JS

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR

theorem ko_pi_torsion (O : Type) [CommRing O] [IsDomain O] (rr : Type) [Fintype rr]
    (z : rr → KO O) : ∃ c : O, c ≠ 0 ∧ c • z = 0 := by
  have h1 : ∀ k, ∃ c : O, c ≠ 0 ∧ c • z k = 0 := by
    intro k
    obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective _ (z k)
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := O) x
    refine ⟨b, nonZeroDivisors.ne_zero hb, ?_⟩
    rw [← hx, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Submodule.mem_one]
    refine ⟨a, ?_⟩
    have hb0 : algebraMap O (FractionRing O) b ≠ 0 := by
      simpa using nonZeroDivisors.ne_zero hb
    rw [Algebra.smul_def, mul_div_cancel₀ _ hb0]
  choose c hc0 hc using h1
  refine ⟨∏ k, c k, Finset.prod_ne_zero_iff.2 fun k _ => hc0 k, funext fun k => ?_⟩
  rw [Pi.smul_apply, ← Finset.mul_prod_erase univ c (Finset.mem_univ k), mul_comm, mul_smul, hc k,
    smul_zero]
  rfl

end Formalism.RepresentationBoundsCohomology.JS
