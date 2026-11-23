import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.LeCovCoeff
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FieldBC

set_option autoImplicit false

namespace GlobalTheory.FieldBC

theorem totalDegree_map_inj {σ R S : Type*} [CommSemiring R] [CommSemiring S] (f : R →+* S)
    (hf : Function.Injective f) (P : MvPolynomial σ R) :
    (MvPolynomial.map f P).totalDegree = P.totalDegree := by
  unfold MvPolynomial.totalDegree
  rw [MvPolynomial.support_map_of_injective P hf]

theorem polyNab_fieldBC : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c c' : Coeff l) (hle : c.F ≤ c'.F) (nab : NabV Xo c) (n : ℕ) (P : MvPolynomial (LtN Dw n) c.F) (S : Type) [CommRing S] [Algebra c.F S] [Algebra c'.F S] (h : AlgOver c c' hle S) (y : FrPt Xo c' S) (k : ℤ) (F : Fin n → LB.Sec (Out.LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x))), (MvPolynomial.map (incF c c' hle) P).totalDegree = P.totalDegree ∧ ∑ m ∈ (MvPolynomial.map (incF c c' hle) P).support, algebraMap c'.F S ((MvPolynomial.map (incF c c' hle) P).coeff m) * ∏ b, nabBC hle nab y k (F b) (colOf m b) = ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, nab (y.res hle h) k (F b) (colOf m b) := by
  intro E _ _ _ H Dw l Xo c c' hle nab n P S _ inst _ h y k F
  have hinj : Function.Injective (incF c c' hle) := (incF c c' hle).injective
  refine ⟨totalDegree_map_inj _ hinj P, ?_⟩
  have e : inst = GlobalTheory.FieldBC.resAlg hle S := Algebra.algebra_ext _ _ (fun a => (h a).symm)
  subst e
  rw [MvPolynomial.support_map_of_injective P hinj]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [MvPolynomial.coeff_map]
  rfl

end GlobalTheory.FieldBC
