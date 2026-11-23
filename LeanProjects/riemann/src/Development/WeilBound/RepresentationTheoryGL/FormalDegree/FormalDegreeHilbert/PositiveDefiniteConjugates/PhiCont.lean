import Development.WeilBound.RepresentationTheoryGL.FormalDegree.FormalDegreeHilbert.PositiveDefiniteConjugates.PhiMul
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.LocalA
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ContinuousOnFderivPhiP

noncomputable section

open Finset Matrix
open scoped ComplexOrder

namespace PositivityTheory.RgFd

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem continuous_pP (ε : Fin n → Bool) : Continuous fun g : UJ ε => pP (toM g) := by
  have h : Continuous fun g : UJ ε => PolarDecomposition.polar_L (toM g) :=
    (lcA_polarL_continuousOn ε).comp_continuous (continuous_toM ε) (fun g => g.2)
  exact continuous_matrix_exp_alt.comp h

theorem pP_posDef {ε : Fin n → Bool} (g : UJ ε) : (pP (toM g)).PosDef :=
  exp_noncompactPart_posDef (PolarDecomposition.polar_L_inP (ε := ε) g.2)

theorem phiCont : PhiCont := by
  intro n ε μ
  have hY : Continuous fun z : UJ ε × KG ε => toMK z.2⁻¹ * pP (toM z.1) * toMK z.2 :=
    ((Ps1.continuous_toMK_inv.comp continuous_snd).matrix_mul ((continuous_pP ε).comp continuous_fst)).matrix_mul
      (Ps1.continuous_toMK'.comp continuous_snd)
  refine continuous_iff_continuousAt.2 fun z => ?_
  have hpd := posDef_conj_toMK z.2 (pP_posDef z.1)
  have hΩ : toMK z.2⁻¹ * pP (toM z.1) * toMK z.2 ∈ OmegaSet n := posSet_subset_omega hpd
  have hc : ContinuousAt (PhiM μ) (toMK z.2⁻¹ * pP (toM z.1) * toMK z.2) :=
    ((phiM_differentiableOn μ).continuousOn).continuousAt (isOpen_omega.mem_nhds hΩ)
  show ContinuousAt (fun z : UJ ε × KG ε => (PhiM μ (toMK z.2⁻¹ * pP (toM z.1) * toMK z.2)).re) z
  exact Complex.continuous_re.continuousAt.comp
    (hc.comp (f := fun z : UJ ε × KG ε => toMK z.2⁻¹ * pP (toM z.1) * toMK z.2) hY.continuousAt)

end PositivityTheory.RgFd
