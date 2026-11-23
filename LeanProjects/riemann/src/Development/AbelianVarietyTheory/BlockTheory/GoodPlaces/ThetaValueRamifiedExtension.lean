import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HarmonicValueOfFiniteExtension
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ThValFinExtSplit
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermDPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.SectionScalarValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.FFVMap
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ChartJetTrC

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ThetaValueRamifiedExtension

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections

attribute [local instance] Over.cartesianMonoidalCategory

def IsRamExt (V V' : CDVR) (i : V.Fr →+* V'.Fr) (r : ℕ) : Prop :=
  0 < r ∧ ∀ a : V.Fr, a ≠ 0 → vV V'.V (i a) = (r : ℤ) * vV V.V a

example (V : CDVR) : IsRamExt V V (RingHom.id _) 1 := ⟨one_pos, fun a _ => by simp⟩

section Defs

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

def extAlg {V V' : CDVR} (io : c.F →+* V.Fr) (i : V.Fr →+* V'.Fr) :
    letI := io.toAlgebra
    letI := (i.comp io).toAlgebra
    V.Fr →ₐ[c.F] V'.Fr :=
  letI := io.toAlgebra
  letI := (i.comp io).toAlgebra
  { i with commutes' := fun _ => rfl }

def IsBaseChange {V V' : CDVR} {io : c.F →+* V.Fr} (i : V.Fr →+* V'.Fr) (y : IntFr Xo c V io)
    (y' : IntFr Xo c V' (i.comp io)) : Prop :=
  letI := io.toAlgebra
  letI := (i.comp io).toAlgebra
  FrMap (extAlg io i) y.1 y'.1

def ModelsSplit {V : CDVR} {io : c.F →+* V.Fr} (y : IntFr Xo c V io) : Prop :=
  ∀ I : IntData Xo c V io y.1, SplitModel I

abbrev LevelSec {V : CDVR} {io : c.F →+* V.Fr} (y : IntFr Xo c V io) : Type :=
  letI := io.toAlgebra
  LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((l.M : ℤ) ^ 2) (ptO Xo y.1.x))

def IsLevelTranslate {V : CDVR} {io : c.F →+* V.Fr} (y : IntFr Xo c V io) (x : Dw.La) (F : LevelSec y) : Prop :=
  letI := io.toAlgebra
  IsVtOver Xo.univ.t.G Xo.univ.t.PP l.M (KilledBy Xo (l.Mb ^ 2)) y.1.s (levPt Xo y.1.x x) F

variable [StarRing (𝓞 E)]

def IsLevelGerm {V : CDVR} {io : c.F →+* V.Fr} {y : IntFr Xo c V io} (C : IntegralChartA3 Xo c V io y)
    (F : LevelSec y) (g : Germ.PS V.Fr 1 (chD C.ch)) : Prop :=
  letI := io.toAlgebra
  IsGerm y.1 C.ch.d C.ch.x C.ch.B.A.act C.ch.e C.ch.wP (l.M ^ 2) (zCast Xo.univ.t.G (natCast_sq l.M) F) g

def harmComb {V : CDVR} {io : c.F →+* V.Fr} {y : IntFr Xo c V io} (C : IntegralChartA3 Xo c V io y) {n : ℕ}
    (P : MvPolynomial (LtN Dw n) c.F) (g : Fin n → Germ.PS V.Fr 1 (chD C.ch)) : V.Fr :=
  letI := io.toAlgebra
  ∑ m ∈ P.support, io (P.coeff m) *
    ∏ b, C.ch.B.nabVal V.Fr C.ch.h H.w0 (l.M ^ 2) (g b) C.ch.uvec (MvPolynomial.monomial (colOf m b) 1)

example {V : CDVR} {io : c.F →+* V.Fr} {y : IntFr Xo c V io} (C : IntegralChartA3 Xo c V io y) {n : ℕ}
    (g : Fin n → Germ.PS V.Fr 1 (chD C.ch)) : harmComb C (0 : MvPolynomial (LtN Dw n) c.F) g = 0 := by
  simp [harmComb]

end Defs

def ThetaValueIdentity : Prop :=
  ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) [StarRing (𝓞 D.host.E)]
    (nab : NabV (T.Q.Xo j) T.Q.c), IsNab (T.Q.Xo j) T.Q.c nab →
    ∀ (w : WeightFamilies.Wt D j) (x : Fin w.n → (T.Q.Dw j).La) (P : MvPolynomial (LtN (T.Q.Dw j) w.n) T.Q.c.F),
    P ∈ harmA T.Q.c (wtA w) w.n →
    ∀ f : T.R j, IsThRule (T.Q.Xo j) T.Q.c nab x P f →
    ∀ (V : CDVR) (io : T.Q.c.F →+* V.Fr) (y : IntFr (T.Q.Xo j) T.Q.c V io) (e : ℕ)
      (la : HeightOneSpectrum (𝓞 T.Q.c.F)), OverLa la V.V io e → y.IsAlg →
      ((T.Q.l.M : 𝓞 T.Q.c.F) ∉ la.asIdeal) →
      ∃ (V' : CDVR) (i : V.Fr →+* V'.Fr) (r : ℕ) (y' : IntFr (T.Q.Xo j) T.Q.c V' (i.comp io))
        (F : Fin w.n → LevelSec y') (C : IntegralChartA3 (T.Q.Xo j) T.Q.c V' (i.comp io) y')
        (g : Fin w.n → Germ.PS V'.Fr 1 (chD C.ch)),
        IsRamExt V V' i r ∧ y'.IsAlg ∧ IsBaseChange i y y' ∧ ModelsSplit y' ∧
        (∀ b, IsLevelTranslate y' (x b) (F b)) ∧
        (∀ b, IsLevelGerm C (F b) (g b)) ∧ (∀ b, IsIntPS V' (g b)) ∧
        i (evI y f) = ((T.Q.l.M : V'.Fr) ^ P.totalDegree)⁻¹ * harmComb C P g

end GlobalTheory.IndefiniteRowSideFullHecke.ThetaValueRamifiedExtension
