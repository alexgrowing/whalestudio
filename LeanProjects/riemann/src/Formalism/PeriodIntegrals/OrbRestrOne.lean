import Formalism.PeriodIntegrals.OrbJetBase

noncomputable section

open scoped BigOperators
open Classical

namespace PI.OrbJet

open NumberField IsDedekindDomain Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions.G

variable {D : D7}

def OrbitRestrictionAtConjugate (E : Ent D) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (h5 : 5 ≤ p), nP D p = 1 → ∀ (u : D.what₂.Word) (i : ℕ),
    ∀ Th, ThetaExpansionRealPlaces D p Th → ∀ z, (oneLoc E p h5 u i z (restr1 D p z Th)).AdmB

end PI.OrbJet

end
