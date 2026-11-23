import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.SpanPowerMembership
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalStageNonempty

open Formalism.BasicNotions

namespace GlobalTheory.Mem

theorem nonempty_record_of_locStage : Nonempty D7 := by
  obtain ⟨L⟩ := GlobalTheory.Mem.nonempty_locStage
  exact Formalism.BasicNotions.Examples₂.nonempty_D7_of_localGap ⟨L.loc, L.locA, L.locT⟩

end GlobalTheory.Mem
