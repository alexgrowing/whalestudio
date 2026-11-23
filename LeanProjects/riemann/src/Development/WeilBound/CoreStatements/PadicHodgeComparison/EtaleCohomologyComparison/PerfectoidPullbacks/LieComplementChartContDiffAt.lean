import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Lin
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.IsTautologicalLineAt

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Limits GlobalTheory.LogCris GroundTheory.PAdicHodge

namespace CrystallineSemistableComparison.Pb

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

abbrev Amp (M : Model l K) (D : E.LineData M.X) : Prop := IsTautologicalLine M.p D

abbrev lineK {M : Model l K} (D : E.LineData M.X) : E.LineData M.gen := D.pb (pullback.fst _ _)

def LieComplementChartContDiffAt (L : KapL (l := l) (K := K) Amp) : Prop :=
  ∀ {M : Model l K} (a : (dat Amp).Ch M), M.Sm → ∀ (x : ((dat Amp).H a).N 2) (c : HdR M.q 2), (dat Amp).c1H a x →
    IsFirstChernDeRham M.q (lineK a.1) c → ∀ φ : Module.Dual K (HdR M.q 2), L.κ a 2 x φ = (per l K).o (φ c)

end CrystallineSemistableComparison.Pb
