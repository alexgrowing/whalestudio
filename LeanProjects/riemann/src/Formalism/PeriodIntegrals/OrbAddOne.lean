import Formalism.PeriodIntegrals.OrbJetBase

noncomputable section

open scoped BigOperators
open Classical

namespace PI.OrbJet

open NumberField IsDedekindDomain Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions.G

variable {D : D7}

def OrbitsAddAtConjugate (E : Ent D) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (h5 : 5 ≤ p), nP D p = 1 → ∀ (u : D.what₂.Word) (i : ℕ), i < D.R.m →
    ∀ β : Pl D → ℝ, (∀ z, OneGe E p h5 u i z (β z)) →
    ∀ Th, ThetaExpansionRealPlaces D p Th → OJ.KvalGe (D.R.N i) (D.R.N (i + 1)) p (E.nu u i) Th (∑ z, β z)

end PI.OrbJet

end
