import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses

noncomputable section

namespace Formalism.L2.Pj

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}

def AbelianAtQZero (D : Datum H) : Prop :=
  D.q = 0 → ∀ (Xo : ∀ l : Level H, Moduli D l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W),
    N2 Y → ∀ i : Idx H p, abLocus (Y i).t.G = Set.univ

end Formalism.L2.Pj
