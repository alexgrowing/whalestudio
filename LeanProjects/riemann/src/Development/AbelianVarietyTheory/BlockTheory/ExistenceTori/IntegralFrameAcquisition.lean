import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.VAtVNeBot
import Formalism.LocalToGlobal.ProjectiveLattices.PtFree

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.IntegralFrameAcquisition

open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor

def IsFiniteValuedExt (T T' : CDVR) (j : T.Fr →+* T'.Fr) (r : ℕ) : Prop :=
  j.Finite ∧ 0 < r ∧ ∀ x : T.Fr, vV T'.V (j x) = (r : ℤ) * vV T.V x

def algHomOver {K A B : Type} [CommRing K] [CommRing A] [CommRing B] (io : K →+* A) (j : A →+* B) :
    letI := io.toAlgebra
    letI := (j.comp io).toAlgebra
    A →ₐ[K] B :=
  letI := io.toAlgebra
  letI := (j.comp io).toAlgebra
  { j with commutes' := fun _ => rfl }

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

def IsIntegralFrameOf {T T' : CDVR} {io : c.F →+* T.Fr} (j : T.Fr →+* T'.Fr)
    (y : letI := io.toAlgebra; FrPt Xo c T.Fr) (y' : IntFr Xo c T' (j.comp io)) : Prop :=
  letI := io.toAlgebra
  letI := (j.comp io).toAlgebra
  ∃ (z : FrPt Xo c T'.Fr) (t : Ix Dw → T'.Frˣ), FrMap (algHomOver io j) y z ∧ FrBor t z y'.1

def AcquiresIntegralFrame (la : HeightOneSpectrum (𝓞 c.F)) {T : CDVR} {io : c.F →+* T.Fr} (e : ℕ)
    (y : letI := io.toAlgebra; FrPt Xo c T.Fr) : Prop :=
  ∃ (T' : CDVR) (j : T.Fr →+* T'.Fr) (r : ℕ) (y' : IntFr Xo c T' (j.comp io)),
    IsFiniteValuedExt T T' j r ∧ OverLa la T'.V (j.comp io) (r * e) ∧ y'.IsAlg ∧ IsIntegralFrameOf j y y'

variable (Xo c)

def AllAcquireIntegralFrame : Prop :=
  ∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ),
    OverLa la T.V io e → T.FinRes →
      ∀ y : (letI := io.toAlgebra; FrPt Xo c T.Fr), AcquiresIntegralFrame la e y

def AllTestAcquireIntegralFrame : Prop :=
  ∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ),
    OverLa la T.V io e → T.FinRes →
      ∀ y : (letI := io.toAlgebra; FrPt Xo c T.Fr),
        (letI := io.toAlgebra
         FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y) →
        AcquiresIntegralFrame la e y

variable {Xo c}

end GlobalTheory.IndefiniteRowSideFullHecke.IntegralFrameAcquisition
