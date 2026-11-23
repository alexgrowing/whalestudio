import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.LeCovCoeff
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.AdmissibleColumnsLeAndHarmonicMapCover
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ShortThetaValueExistsUniqueNaturalOfLaws
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ShortThetaValueLinearInPolynomial
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FieldBC

namespace GlobalTheory

theorem evR_sum_smul_fin {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    (Xo : Moduli Dw l) (c : Coeff l) {ι : Type} (s : Finset ι) (t : ι → c.F) (f : ι → Rul Xo c)
    {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) :
    evR Xo c (∑ i ∈ s, t i • f i) y = ∑ i ∈ s, algebraMap c.F S (t i) * evR Xo c (f i) y := by
  classical
  have hL : ∑ i ∈ s, t i • f i = ∑ j : Fin s.card, t (s.equivFin.symm j) • f (s.equivFin.symm j) := by
    rw [← Finset.sum_coe_sort s]
    exact (Equiv.sum_comp s.equivFin.symm (fun i : s => t i • f i)).symm
  have hR : ∑ i ∈ s, algebraMap c.F S (t i) * evR Xo c (f i) y =
      ∑ j : Fin s.card, algebraMap c.F S (t (s.equivFin.symm j)) * evR Xo c (f (s.equivFin.symm j)) y := by
    rw [← Finset.sum_coe_sort s]
    exact (Equiv.sum_comp s.equivFin.symm (fun i : s => algebraMap c.F S (t i) * evR Xo c (f i) y)).symm
  rw [hL, hR]
  exact Formalism.L2.Pj.evR_sum_smul y (fun j => t (s.equivFin.symm j)) (fun j => f (s.equivFin.symm j))

end GlobalTheory
