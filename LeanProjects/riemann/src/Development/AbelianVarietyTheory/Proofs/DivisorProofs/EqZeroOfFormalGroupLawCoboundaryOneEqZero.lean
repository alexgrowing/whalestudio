import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigOfOmegaInjectiveOfEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectedPDivGroupFormalLawCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionsEqSeriesInChartStatement
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.Katz

theorem eq_zero_of_cob1_eq_zero : ∀ (p : ℕ) (k : Type) [CommRing k] (h : (p : k) = 0) (d : ℕ)
    (G : PDivGroup p k) (c : Chart G d) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k),
    c.IsLawOf μ → ∀ b, cob1 μ b = 0 → b = 0 := by
  intro p k _ h d G c μ hμ b hb
  obtain ⟨hres, -, huniq⟩ := GlobalTheory.T.functions_eq_series_in_chart p k d G c
  have hlaw := ((GlobalTheory.T.connectedPDivGroup_formalLaw_coordinates p k d G c).2 μ hμ).2
  let B : G.funs := ⟨fun n => c.ev n b, fun n => hres n b⟩
  have hB : G.cob B = 0 := by
    refine Subtype.ext (funext fun n => ?_)
    change cobOne k (G.A n) (c.ev n b) = 0
    rw [← (hlaw n b).2, hb, map_zero]
  have hB0 := G.eq_zero_of_cob_eq_zero h hB
  have hb0 : ∀ n, c.ev n b = 0 := fun n => congrArg (fun B : G.funs => B.1 n) hB0
  obtain ⟨f, -, hf⟩ := huniq (fun _ => 0) (fun n => map_zero _)
  exact (hf b hb0).trans (hf 0 fun n => map_zero _).symm

end GlobalTheory.Katz
