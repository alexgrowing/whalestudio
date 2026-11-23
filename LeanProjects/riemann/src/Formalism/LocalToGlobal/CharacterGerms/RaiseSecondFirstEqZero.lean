import Formalism.LocalToGlobal.CharacterGerms.CanonicalGaugeFirstPartialLawEq

noncomputable section

open scoped BigOperators
open Classical
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace Formalism.L2.FormalSeriesBounds

namespace CocycleCoordinateParts

open PartialDerivEval CocycleIdentity

section Exps

variable {dd : ℕ}

def xup (α : Fin 1 × Fin dd →₀ ℕ) : Fin 2 × Fin dd →₀ ℕ := α.mapDomain fun p => ((0 : Fin 2), p.2)

def zup2 (β : Fin dd →₀ ℕ) : Fin 2 × Fin dd →₀ ℕ := β.mapDomain fun j => ((1 : Fin 2), j)

def zup (β : Fin dd →₀ ℕ) : Fin 3 × Fin dd →₀ ℕ := β.mapDomain fun j => ((2 : Fin 3), j)

def xpart (d : Fin 2 × Fin dd →₀ ℕ) : Fin 1 × Fin dd →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun p => d ((0 : Fin 2), p.2)

def zpart (d : Fin 2 × Fin dd →₀ ℕ) : Fin dd →₀ ℕ := Finsupp.equivFunOnFinite.symm fun j => d ((1 : Fin 2), j)

def lpart (α : Fin 3 × Fin dd →₀ ℕ) : Fin 2 × Fin dd →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun p => α (Fin.castSucc p.1, p.2)

def zpart3 (α : Fin 3 × Fin dd →₀ ℕ) : Fin dd →₀ ℕ := Finsupp.equivFunOnFinite.symm fun j => α ((2 : Fin 3), j)

end Exps

section Ser

variable {C : Type} [Field C] [CharZero C] {dd : ℕ}

def slice (β : Fin dd →₀ ℕ) (F : PS C 2 dd) : PS C 1 dd := fun α => coeff (xup α + zup2 β) F

end Ser

section Kill

variable {C : Type} [Field C] [CharZero C] {dd : ℕ}

variable {V : VF C} {O : Type} [CommRing O] [StarRing O] (Y : FBChart C V O dd)

end Kill

section Closed

end Closed

end CocycleCoordinateParts

end Formalism.L2.FormalSeriesBounds
