import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.HeckeCl

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV CrystallineSemistableComparison UpperTheory.Ru.crystallineComparison UpperTheory.Gal.G3

namespace UpperTheory.Gal.crystallineComparison.Br

theorem trTot : TrTot := by
  intro l _ B Z Y p q s tr htr W r c hc J _ σ hσ hsp x
  change Htot l (sch.obj Y) at x
  change pullTot l (sch.map c) (DirectSum.lmap tr x) = ∑ j, pullTot l (sch.map (σ j)) x
  ext n
  rw [DFinsupp.finset_sum_apply]
  simp only [pullTot, DirectSum.lmap_apply]
  exact htr n W r c hc J σ hσ hsp (x n)

end UpperTheory.Gal.crystallineComparison.Br
