import Formalism.PeriodIntegrals.OrbJetBase

noncomputable section

open scoped BigOperators
open Classical

namespace PI.OrbJet

open NumberField IsDedekindDomain Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions.G

variable {D : D7}

def OrbitRestriction (E : Ent D) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (h : OrbOK D p) (u : D.what₂.Word) (i : ℕ) (R : Finset (Pl D)), IsReps D p R →
    ∀ (ep : ℂ_[p]) (sg : Pl D → ℂ_[p]) (be : Pl D → MvPowerSeries (ZMod (nP D p)) ℂ_[p]), BeOK D p R ep sg be →
    ∀ Th, ThetaExpansionAllPlaces D p R ep sg be Th → ∀ r ∈ R, OrbitThetaExpansion (orbLoc E p h u i r (restr D p r Th)) ep (sg r) (be r)

end PI.OrbJet

end
