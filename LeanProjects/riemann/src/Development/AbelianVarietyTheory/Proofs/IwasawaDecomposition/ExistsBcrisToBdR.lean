import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PadicIntHomUnique
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisLoc
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

theorem IsCrisP.on_ainf {l : ℕ} [Fact l.Prime] {j : Per.Acris l →+* Per.BdRp l} (hj : IsCrisP j)
    (a : Per.Ainf l) :
    j (algebraMap (Per.Ainf l) (Per.Acris l) a) =
      algebraMap (Per.AinfP l) (Per.BdRp l) (algebraMap (Per.Ainf l) (Per.AinfP l) a) := by
  rw [GlobalTheory.RingIface.tower]
  exact hj.on0 (algebraMap (Per.Ainf l) (Per.Acris0 l) a)

end GlobalTheory.MemLoc
