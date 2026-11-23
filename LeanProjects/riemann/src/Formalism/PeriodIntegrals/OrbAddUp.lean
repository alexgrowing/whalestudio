import Formalism.PeriodIntegrals.OrbJetBase

noncomputable section

open scoped BigOperators
open Classical

namespace PI.OrbJet

open NumberField IsDedekindDomain Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions.G

variable {D : D7}

def OrbitsAddLowerBound (E : Ent D) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (h : OrbOK D p) (u : D.what₂.Word) (i : ℕ), i < D.R.m → ∀ R : Finset (Pl D), IsReps D p R →
    ∀ (ep : ℂ_[p]) (sg : Pl D → ℂ_[p]) (be : Pl D → MvPowerSeries (ZMod (nP D p)) ℂ_[p]), BeOK D p R ep sg be →
    ∀ β : Pl D → ℝ, (∀ r ∈ R, OrbGe E p h u i r ep (sg r) (be r) (β r)) →
    ∀ Th, ThetaExpansionAllPlaces D p R ep sg be Th → OJ.KvalGe (D.R.N i) (D.R.N (i + 1)) p (E.nu u i) Th (∑ r ∈ R, β r)

end PI.OrbJet

end
