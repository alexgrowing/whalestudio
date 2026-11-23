import Formalism.LocalToGlobal.ProjectiveLattices.FrameProofs
import Formalism.LocalToGlobal.ProjectiveLattices.ChartWD

noncomputable section

namespace Formalism.L2.Pj

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

section Clauses

variable (Xo : Moduli Dw l) (c : Coeff l)

def FrChartF : Prop :=
  FrChart (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z)

def BorChartF : Prop :=
  BorChart (K := c.F) (ι := Ix Dw) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (fun t y y' => FrBor t y y')

end Clauses

section Proofs

variable {Xo : Moduli Dw l} {c : Coeff l}

theorem evalWD_fr (h : FrChartF Xo c) :
    EvalWD (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) :=
  evalWD_of_frChart h

theorem wtField_of_borChart (h : BorChartF Xo c) : WtField Xo c := by
  intro a n f hf S _ _ t y y' hy hy' hb
  exact wtAll_of_borChart h (ex Dw a n) hf.1 hf.2 S t y y' hy hy' hb

theorem unitIndep_of_charts (h : BorChartF Xo c) (hL : IntLatU Xo c) : UnitIndep Xo c :=
  unitIndep_of (wtField_of_borChart h) (intDiagUnit_of hL)

theorem exist3_of (hC : FrChartF Xo c) (hB : BorChartF Xo c) (hL : IntLatU Xo c) :
    EvalWD (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) ∧ WtField Xo c ∧ IntDiagUnit Xo c :=
  ⟨evalWD_fr hC, wtField_of_borChart hB, intDiagUnit_of hL⟩

end Proofs

end Formalism.L2.Pj
