import Formalism.SharpRestriction.LevelLetterCocycles.TwGood

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain

namespace Formalism.MainNotions

def QDistinct (D : D7) (Q : Finset (PlE D.host)) : Prop :=
  ∀ P ∈ Q, ∀ P' ∈ Q, P.asIdeal.comap (algebraMap ℤ (𝓞 D.host.E)) = P'.asIdeal.comap (algebraMap ℤ (𝓞 D.host.E)) →
    P' = P ∨ IsConjPl D.host P P'

def QDistinctAt (D : D7) (C : NChoice D) : Prop :=
  ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → QDistinct D (C.Q w)

end Formalism.MainNotions
