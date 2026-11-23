import Formalism.LocalToGlobal.ProjectiveLattices.TowerOfAt
import Formalism.LocalToGlobal.ProjectiveLattices.BetaAtSymm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion

noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out
open Formalism.MainNotions.DIV.Cons (SCF intO)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

structure DatAt (Y : Model Xo c β) {p : ℕ} {C : SCF p} (P : PointsOfFlagModel.PtC Y C) : Type 1 where
  R : Type
  [ring : CommRing R]
  [dom : IsDomain R]
  [loc : IsLocalRing R]
  [ch0 : CharZero R]
  noeth : IsNoetherianRing R
  normal : IsIntegrallyClosed R
  complete : IsAdicComplete (maximalIdeal R) R
  ι : Sp R ⟶ Y.X
  f : R →+* intO ↥C.S
  f_loc : ∀ a ∈ maximalIdeal R, ‖((f a : intO ↥C.S) : ↥C.S)‖ < 1
  fac : spMap f ≫ ι = P.yt
  t : SAB H (Sp R)
  m : SABMap t Y.t ι
  U : PELUnif (maximalIdeal R) t
  unitOn : ∀ y, PsiUnitOn U.D.toPre y (ι ⁻¹' abLocus Y.t.G)
  tors : U.TorsionIso

attribute [instance] DatAt.ring DatAt.dom DatAt.loc DatAt.ch0

namespace DatAt

variable {Y : Model Xo c β} {p : ℕ} {C : SCF p} {P : PointsOfFlagModel.PtC Y C}

abbrev Ylat (A : DatAt Y P) : Type := A.U.D.toPre.X

def beta (A : DatAt Y P) (a b : A.Ylat) : ℝ :=
  betaAt A.U.D.toPre ((intO ↥C.S).subtype.comp A.f) p a b

theorem data_at_point_n3 (A : DatAt Y P) : UniformisationConclusion A.t (A.ι ⁻¹' abLocus Y.t.G) := ⟨A.U, A.unitOn, A.tors⟩

theorem beta_symm (A : DatAt Y P) (a b : A.Ylat) : A.beta a b = A.beta b a :=
  betaAt_symm _ _ _ a b

end DatAt

end Formalism.L2.Pj
