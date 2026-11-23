import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.JCount
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCountE

noncomputable section

namespace Formalism.MainNotions.N.CylinderCountFamily

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders Formalism.MainNotions.FamilyNumericLemmas

variable (D : D7) {Dall Dgood : ℕ}

def PCountTie (A : AllRowsAt D Dall Dgood) : Prop :=
  ∀ (k : Fin 2) (S : Set (Tup D k)),
    Formalism.MainNotions.S.CountE.PCount A.B.I A.B.μf (D.host.g (1 - k)) (A.eT (cyl D k S))

theorem countCylAt_of (A : AllRowsAt D Dall Dgood) {n₀ : ℕ} {Alev C₃ c₃ cb : ℝ}
    (h1 : Formalism.MainNotions.S.CountE.CountIdempotentsClass Formalism.MainNotions.S.CountE.PCount D n₀ Alev C₃ c₃ cb)
    (hT : TieCountAt A n₀ Alev C₃ cb) (hP : PCountTie D A) : CountCylAt D A c₃ := by
  intro k S
  obtain ⟨b, h, hST, hgap, hC, hlf, hlb, -⟩ := hT
  exact h1 A.B.I b A.B.lam A.B.g (D.host.g (1 - k)) (A.eT (cyl D k S)) _ A.B.σ A.B.w _ A.B.σs A.B.tens
    A.B.μf A.B.fund A.B.R (A.ReT (cyl D k S)) h (hST k S).1 (hP k S) (hST k S).2 hgap hC hlf hlb

end Formalism.MainNotions.N.CylinderCountFamily
