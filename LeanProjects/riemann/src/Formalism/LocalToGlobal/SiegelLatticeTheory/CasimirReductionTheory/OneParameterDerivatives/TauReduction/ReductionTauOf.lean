import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.TauReduction.LatticeVectorsBoundedBelow

set_option autoImplicit false

noncomputable section

open NumberField Matrix Filter Topology

namespace Formalism.L2.SG.Pf.Tau

open Size Formalism.MainNotions.S

theorem reductionTau_of (h3 : SubmoduleExists) (h6 : SizesLocallyComparable) (h7 : InfimumContinuousFamily)
    (h8 : MinkowskiSubmodule) (h9 : LatticeVectorsBoundedBelow) (h10 : HeightsPositive) : ReductionTau := by
  unfold Formalism.L2.SG.LitS.ReductionTau
  intro I hn
  refine ⟨?_, fun x => ?_⟩
  · exact h7 I.GA (Sub I) (fun x s => size I s) (fun x => h3 I hn x)
      (fun x s => Real.rpow_nonneg (h10 I x s).le _) (fun x r hr => h6 I x r hr)
  · obtain ⟨c, hc, hc8⟩ := h8 I
    obtain ⟨l, hl, hl9⟩ := h9 I x
    have hδ : ∀ s : Sub I x, Real.sqrt (l / c) ≤ size I s := by
      intro s
      obtain ⟨u, huB, hu0, hsum⟩ := hc8 x s
      have h1 := hl9 u (s.B_lat huB) hu0
      have hs0 : 0 ≤ size I s := Real.rpow_nonneg (h10 I x s).le _
      exact Real.sqrt_le_iff.2 ⟨hs0, (div_le_iff₀ hc).2 (by linarith)⟩
    haveI := h3 I hn x
    exact ⟨lt_min (by norm_num) (lt_of_lt_of_le (Real.sqrt_pos.2 (div_pos hl hc)) (le_ciInf hδ)),
      min_le_left _ _⟩

end Formalism.L2.SG.Pf.Tau
