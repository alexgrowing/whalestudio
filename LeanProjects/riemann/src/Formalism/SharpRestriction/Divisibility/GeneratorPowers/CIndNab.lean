import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Formalism.LocalToGlobal.ProjectiveLattices.DatIndep

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

namespace CIndNab

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  (Xo : Moduli Dw l) (c : Coeff l)

theorem thExpr_eq (hU : ThExprUniqSt) [StarRing (𝓞 E)] (nab nab' : NabV Xo c) (h : IsNab Xo c nab)
    (h' : IsNab Xo c nab') {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) {n : ℕ}
    (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F) (hP : P ∈ harmA c a n)
    (F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((l.M : ℤ) ^ 2) (ptO Xo y.x))) :
    thExpr Xo c nab y P F = thExpr Xo c nab' y P F := by
  letI : Algebra ℚ S := ((algebraMap c.F S).comp (algebraMap ℚ c.F)).toAlgebra
  have key : ∀ (K : ℤ) (k : ℕ), K = (k : ℤ) →
      ∀ G : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L K (ptO Xo y.x)),
      ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, nab y K (G b) (colOf m b) =
        ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, nab' y K (G b) (colOf m b) := by
    rintro K k rfl G
    exact hU E H Dw l Xo c nab nab' h h' S y k n G a P hP
  unfold thExpr
  congr 1
  exact key _ (l.M ^ 2) (Nat.cast_pow l.M 2).symm F

theorem thValAt_iff (hU : ThExprUniqSt) [StarRing (𝓞 E)] (nab nab' : NabV Xo c) (h : IsNab Xo c nab)
    (h' : IsNab Xo c nab') {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) {n : ℕ}
    (x : Fin n → Dw.La) (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F) (hP : P ∈ harmA c a n)
    (v : S) : ThValAt Xo c nab y x P v ↔ ThValAt Xo c nab' y x P v := by
  constructor
  · rintro ⟨S', i1, i2, φ, y', F, hff, hmap, hvt, hv⟩
    exact ⟨S', i1, i2, φ, y', F, hff, hmap, hvt, hv.trans (thExpr_eq Xo c hU nab nab' h h' y' a P hP F)⟩
  · rintro ⟨S', i1, i2, φ, y', F, hff, hmap, hvt, hv⟩
    exact ⟨S', i1, i2, φ, y', F, hff, hmap, hvt, hv.trans (thExpr_eq Xo c hU nab nab' h h' y' a P hP F).symm⟩

end CIndNab

open CIndNab in

theorem nabUniq_of_chartIndep2 (hC : ChartIndepSt2) {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : Host E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) (c : Coeff l) : NabUniq Xo c := by
  intro _ nab nab' h h' a n _
  have hU := thExprUniq_of_chartIndep2 hC
  refine Set.ext fun f => ⟨?_, ?_⟩
  · rintro ⟨x, P, hP, hf⟩
    exact ⟨x, P, hP, fun p y => (thValAt_iff Xo c hU nab nab' h h' y x a P hP _).1 (hf p y)⟩
  · rintro ⟨x, P, hP, hf⟩
    exact ⟨x, P, hP, fun p y => (thValAt_iff Xo c hU nab nab' h h' y x a P hP _).2 (hf p y)⟩

end Formalism.MainNotions.ModuliIntegralCharts.H1
