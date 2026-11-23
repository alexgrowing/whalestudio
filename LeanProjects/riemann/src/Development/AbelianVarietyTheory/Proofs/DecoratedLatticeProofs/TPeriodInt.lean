import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PerIntOnAmb
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.AdmissiblePeriodOfPeriodInt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HypOver
import Formalism.LocalRingCardinality.SpanPowerMembership.NZRowX

noncomputable section

namespace GlobalTheory.Core.Int.Inhab

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.NZ NumberField IsDedekindDomain GlobalTheory.Core.Int GlobalTheory.Core.Int.Model
  GlobalTheory.Core.RkFamModel

set_option maxHeartbeats 1600000 in

abbrev recOne : D7 :=
  letI := (Ht 0).cmStar
  hostLevelRecord (Ht 0) (W := Unit) () (fun _ _ => hcA 0) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ => rfl)
    (fun _ _ _ => rfl) 1 one_pos (fun _ _ l h => exampleWeight_cloud_gap_four l h) (fun _ _ => false) (fun _ _ _ => rfl)
    (fun _ _ l h => by
      have := exampleWeight_middle_entries l h
      simp only [Bool.false_eq_true, if_false, sub_zero]
      simp only [hcA, Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false, add_zero]
      exact this)
    (fun _ _ => 1) (fun _ _ => one_pos) (fun _ => 1) (fun _ => one_pos) 0 (fun _ => 0) (fun _ => 1) (fun _ => one_pos)
    (fun _ => oneCls 1 one_pos) (fun _ => T0) (dstarOf T0) (dstarOf_pos T0) (fun _ => 1) (fun _ => one_pos) 2 one_lt_two
    (fun _ => exampleLevel_near_lower Tau0 T0) exampleHost_type_primes_split (tH 0) (fun _ => examplePrime_mem_levelPrimes) (fun _ => examplePrime_ne_split_primes) (fun _ => π0O)
    (fun _ => π0_mem_K) (fun _ => π0_norm) (fun _ => π0_cong)
    (fun _ i _ => ((hostSpacesOfNorm (Ht 0) T0 (π0O : (Ht 0).E) π0_norm).X i).L0)
    (fun _ i _ => ((hostSpacesOfNorm (Ht 0) T0 (π0O : (Ht 0).E) π0_norm).X i).standardTuple_isLattice)
    (gap 0) (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ => false) (fun _ => rfl) 1 1 1 le_rfl Unit (fun _ => ()) (fun _ => ())
    (lbl 0) (fun _ => by norm_num [T0]) (fun _ _ => linePer 1) (fun _ => (stdHLat (Ht 0).E Unit).L)
    (localDataAtServedPlace' (Ht 0) (fun _ _ => hcA 0) (fun _ : Unit => oneCls 1 one_pos) (fun _ => T0) (fun _ _ => 0) (fun _ => 0) (fun _ _ => ∅))
    (localData_rank_eq_classes (Ht 0) (fun _ _ => hcA 0) (fun _ : Unit => oneCls 1 one_pos) (fun _ => T0) (fun _ _ => 0) (fun _ => 0) (fun _ _ => ∅))

end GlobalTheory.Core.Int.Inhab
