import Formalism.LocalToGlobal.ProjectiveLattices.VAtVNeBot
import Formalism.LocalToGlobal.ProjectiveLattices.ThClass
import Formalism.LocalToGlobal.ProjectiveLattices.LiftLaSpec

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GoodPts

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}

def Good {T : CDVR} {io : c.F →+* T.Fr} (y : IntFr Xo c T io) : Prop :=
  letI := io.toAlgebra
  ∃ (G : SAB H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (_ : SABMap t' Xo.univ.t y.1.x)
    (_ : SABMap t' G (spMap (algebraMap T.V T.Fr))), IsProper G.G.hom

def InV (T : CDVR) (x : T.Fr) : Prop := x ∈ (algebraMap T.V T.Fr).range

variable (Xo c)

def BddGood (la : HeightOneSpectrum (𝓞 c.F)) (κ : c.F) (f : Rul Xo c) : Prop :=
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la T.V io e →
    ∀ y : IntFr Xo c T io, y.IsAlg → Good y → InV T (io κ * evI y f)

def BddAll (la : HeightOneSpectrum (𝓞 c.F)) (κ : c.F) (f : Rul Xo c) : Prop :=
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la T.V io e →
    ∀ y : IntFr Xo c T io, y.IsAlg → InV T (io κ * evI y f)

def supSet (la : HeightOneSpectrum (𝓞 c.F)) (W : Submodule c.F (Rul Xo c)) : Set (Rul Xo c) :=
  {f | f ∈ W ∧ BddAll Xo c la 1 f}

end GlobalTheory.GoodPts
