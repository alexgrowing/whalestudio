import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.IntegralValueOfChartValues
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ThetaValCSteps
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.FrMapComp
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndSt
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.GermExCut

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor

attribute [local instance] Over.cartesianMonoidalCategory

theorem nab_zCast {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} (nab : NabV Xo c) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S)
    {k₁ k₂ : ℤ} (h : k₁ = k₂) (F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k₁ (ptO Xo y.x))) (α : Lt1 Dw →₀ ℕ) :
    nab y k₁ F α = nab y k₂ (zCast Xo.univ.t.G h F) α := by
  subst h
  rfl

theorem vLa_natCast_inv_pow {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) {M : ℕ}
    (hM : (M : 𝓞 K) ∉ la.asIdeal) (d : ℕ) : vLa la (((M : K) ^ d)⁻¹) = 0 := by
  have e : (M : K) = algebraMap (𝓞 K) K (M : 𝓞 K) := by simp
  have h1 : la.valuation K (M : K) = 1 := by
    rw [e, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
    exact hM
  simp [vLa, map_inv₀, map_pow, h1]

def FFVMapSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (c : Coeff l)
    [StarRing (𝓞 E)] (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmA c a n →
    ∀ (T : CDVR) (io : c.F →+* T.Fr), P.map io ∈ FFV (Dw := Dw) T a n

def GermTranslateExistence : Prop :=
  ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) [StarRing (𝓞 D.host.E)],
    (∀ a : 𝓞 D.host.E, star a = T.Q.H.bar a) →
    ∀ (Tc : CDVR) (io : T.Q.c.F →+* Tc.Fr) (yI : IntFr (T.Q.Xo j) T.Q.c Tc io) (e : ℕ)
      (la : HeightOneSpectrum (𝓞 T.Q.c.F)), OverLa la Tc.V io e → yI.IsAlg →
      ((T.Q.l.M : 𝓞 T.Q.c.F) ∉ la.asIdeal) → ∀ {n : ℕ} (x : Fin n → (T.Q.Dw j).La),
      letI := io.toAlgebra
      ∀ (F : Fin n → LB.Sec (LPow (T.Q.Xo j).univ.t.G (T.Q.Xo j).univ.t.PP.L ((T.Q.l.M : ℤ) ^ 2)
        (ptO (T.Q.Xo j) yI.1.x))),
      (∀ b, IsVtOver (T.Q.Xo j).univ.t.G (T.Q.Xo j).univ.t.PP T.Q.l.M (KilledBy (T.Q.Xo j) (T.Q.l.Mb ^ 2)) yI.1.s
        (levPt (T.Q.Xo j) yI.1.x (x b)) (F b)) →
      ∃ (C : IntegralChartA3 (T.Q.Xo j) T.Q.c Tc io yI) (g : Fin n → Germ.PS Tc.Fr 1 (chD C.ch)),
        (∀ b, IsGerm yI.1 C.ch.d C.ch.x C.ch.B.A.act C.ch.e C.ch.wP (T.Q.l.M ^ 2)
          (zCast (T.Q.Xo j).univ.t.G (natCast_sq T.Q.l.M) (F b)) (g b)) ∧ ∀ b, IsIntPS Tc (g b)

end ReciprocityTheory.ChartRestriction.G.PullbackSections
