import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCoType
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SupportParahoricBiTransformingDoubleCosets
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

namespace GlobalTheory.ParHecke

theorem esymm_map_mul_const (s : Multiset ℂ) (c : ℂ) (n : ℕ) :
    (s.map (· * c)).esymm n = c ^ n * s.esymm n := by
  unfold Multiset.esymm
  rw [Multiset.powersetCard_map, Multiset.map_map, Multiset.sum_map_mul_left.symm]
  congr 1
  refine Multiset.map_congr rfl fun t ht => ?_
  have hc : t.card = n := (Multiset.mem_powersetCard.1 ht).2
  simp only [Function.comp_apply]
  rw [Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate, hc, mul_comm, Multiset.map_id']

theorem genVal_map_mul (q r N n : ℕ) (B : Multiset ℂˣ) (c : ℂˣ) :
    genVal q r N (B.map (· * c)) n = (c : ℂ) ^ n * genVal q r N B n := by
  unfold genVal
  have e : ((B.map (· * c)).map fun b : ℂˣ => (b : ℂ)) = (B.map fun b : ℂˣ => (b : ℂ)).map (· * (c : ℂ)) := by
    simp [Multiset.map_map, Function.comp_def]
  rw [e, esymm_map_mul_const]
  ring

end GlobalTheory.ParHecke
