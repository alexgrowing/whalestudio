import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectedPDivGroupChartCoboundaryTwoCoordStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectedChartEvalSquareVariablesSwapConstantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfEvalCubeLevelsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionsEqSeriesInChartStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartSquareCoordinatesPresentLevelsStatement

set_option autoImplicit false

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.Katz

theorem isCoc_iff_mem_cocycles : ∀ (p : ℕ) (k : Type) [CommRing k] (d : ℕ) (G : PDivGroup p k)
    (c : Chart G d), ∀ (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k), c.IsLawOf μ →
    ∀ s, IsCoc μ s ↔ (fun n => c.ev₂ n s) ∈ G.cocycles := by
  intro p k _ d G c μ hμ s
  have hcomp : ∀ n, pullbackTwo (G.res n) (c.ev₂ (n + 1) s) = c.ev₂ n s :=
    fun n => (GlobalTheory.T.functions_eq_series_in_chart p k d G c).2.1 n s
  have hnil := (GlobalTheory.T.eq_zero_of_eval_cube_levels p k d G c).1
  have hinj := (GlobalTheory.T.eq_zero_of_eval_cube_levels p k d G c).2
  have hcob : ∀ n, evA k _ (hnil n) (cob2 μ s) = cobTwo k (G.A n) (c.ev₂ n s) :=
    fun n => (GlobalTheory.T.connectedPDivGroupChart_coboundaryTwo_coord p k d G c μ hμ n (hnil n)).1 s
  have hswap : ∀ n, c.ev₂ n (Katz.swap s) = TensorProduct.comm k _ _ (c.ev₂ n s) :=
    fun n => (GlobalTheory.T.connectedChart_evalSquare_variables_swap_constant p k d G c n).2.2.1 s
  constructor
  · rintro ⟨h2, hs⟩ n
    refine ⟨mem_symCocycles.2 ⟨?_, ?_⟩, hcomp n⟩
    · rw [← hcob n, h2, map_zero]
    · rw [← hswap n, hs]
  · intro h
    refine ⟨?_, ?_⟩
    · refine hinj _ fun n hn => ?_
      have e := hcob n
      rw [(mem_symCocycles.1 (h n).1).1] at e
      exact e
    · obtain ⟨t, -, ht⟩ := (GlobalTheory.T.chart_square_coordinates_present_levels p k d G c).2 (fun n => c.ev₂ n s) hcomp
      have h1 := ht (Katz.swap s) fun n => by
        rw [hswap n]; exact (mem_symCocycles.1 (h n).1).2
      have h2 := ht s fun n => rfl
      rw [h1, h2]

end GlobalTheory.Katz
