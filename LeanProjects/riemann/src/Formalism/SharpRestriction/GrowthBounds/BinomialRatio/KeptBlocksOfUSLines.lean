import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.CoarseDegreeRatioConsecutive
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.PairFacts

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G

theorem restPairX : RestPairX :=
  TransportedAlt.of_explicit (fun _ => 1) (fun _ _ => 1) (fun Cc _ CE1 CE2 _ => T2 CE1 CE2 Cc 1)
    fun C0 _ _ _ _ _ CE1 CE2 _ _ hCc hC0 _ h1 h2 _ _ _ _ _ _ _ _ _ t1 t2 t3 t4 t5 => by
      intro X _ hD hI hc j rz ry _ A _ _ mu lam hP hK
      have hs := std_of hCc hC0 h1 h2 le_rfl t1 t2 t3 t4 t5 hD hI hc
      have hseg := (hs.segB j).2
      have hN : (2 * (X.N1 : ℝ) + 3) ≤ (X.m : ℝ) + 1 := hs.N1k
      have hN' : 2 * X.N1 + 2 ≤ X.m := by exact_mod_cast (by linarith : (2 * (X.N1 : ℝ) + 2) ≤ (X.m : ℝ))
      have hr : segS X.TT j + 1 ≤ X.m := by omega
      exact pf_X hP hr (X.La C0) (fun i => (hK i).2)

end Formalism.MainNotions.ColumnSystems.Pf
