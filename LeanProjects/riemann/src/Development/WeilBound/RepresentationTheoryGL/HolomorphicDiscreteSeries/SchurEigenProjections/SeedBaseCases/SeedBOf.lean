import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.SchurEigenProjections.BigProjP

namespace PositivityTheory.RgHe.A.Pf

theorem seedB_of : PositivityTheory.RgHe.Seed → PositivityTheory.RgHe.Occ → PositivityTheory.RgHe.A.SchurEigenProjectionExists := by
  intro hS hO n ε lam ε' mu B e H H' _ _ _ _ _ _ π σ ν hν hF hP hπ hσ hW
  have hG : PositivityTheory.RgHe.Gp ε lam ε' mu e :=
    ⟨hF, hP.two, hP.neg, hP.le, hP.hc, hP.hc', hP.gap, hP.gap'⟩
  have hj := hO n ε lam ε' mu e hG hW H H' π σ hπ hσ
  exact hS n ε lam ε' mu e hG H H' π σ ν hν hπ hσ hj

end PositivityTheory.RgHe.A.Pf
