import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ColonIdealFrobeniusLeMapExpand
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MapMemA
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ImageStableDegreeBounds
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowerSeriesExistsUniqueDecompOverFrobeniusLikeEnStatement
open PowerSeries GlobalTheory.BK Matrix GlobalTheory.LiftCoker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.colonIdeal_frobenius_le_map_expand : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l : ℕ) [Fact l.Prime] (ι κ : Type) [Fintype ι] [Fintype κ] (G : Matrix κ ι K⟦X⟧), colon O K (G.map (frob K l)) ≤ (colon O K G).map (PowerSeries.expand l (Fact.out : l.Prime).ne_zero) := by
  first | exact @GlobalTheory.LiftCoker.colon_map_frob_le | exact GlobalTheory.LiftCoker.colon_map_frob_le | (intros; apply GlobalTheory.LiftCoker.colon_map_frob_le <;> assumption)
