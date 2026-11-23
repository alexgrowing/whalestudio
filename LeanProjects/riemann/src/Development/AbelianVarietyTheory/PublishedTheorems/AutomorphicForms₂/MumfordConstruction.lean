import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.Published

def MumfordConstruction : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E)
    (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Out.AdmBase R (IsLocalRing.maximalIdeal R) →
    ∀ f : R, f ≠ 0 → f ∈ IsLocalRing.maximalIdeal R →
    ∀ (D : Out.DegData R (IsLocalRing.maximalIdeal R)) (mod : Module (𝓞 E) D.toPre.X)
      (oD : letI := H.starRing; D.toPre.OAct (𝓞 E)),
      (letI := H.starRing; TraceFormTwistIso D.toPre oD H.w0) →
      (∀ y, PsiUnitOn D.toPre y {x | f ∉ x.asIdeal}) →
      ∃ (t : SAB H (Sp R)) (P : PELUnif (IsLocalRing.maximalIdeal R) t),
        P.D = D ∧ HEq P.mod mod ∧ HEq P.oD oD ∧
          IsProper (t.G.hom ∣_ (PrimeSpectrum.basicOpen f : (Sp R).Opens))

end GlobalTheory.Published
