import Formalism.LocalToGlobal.CharacterGerms.RaiseSecondFirstEqZero
import Formalism.LocalToGlobal.CharacterGerms.CoeffFirstPairingLinear

noncomputable section

open scoped BigOperators
open Classical
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace Formalism.L2.FormalSeriesBounds

namespace CocycleSliceMultiplication

open PartialDerivEval CocycleIdentity CocycleCoordinateParts

section Gen

variable {C : Type} [Field C] {V : VF C} {σ : Type}

def FrobG (V : VF C) (F : MvPowerSeries σ C) : Prop :=
  ∀ μ : σ →₀ ℕ, (∃ s, ¬ V.l ∣ μ s) → V.MM (coeff μ F)

end Gen

section Ser

variable {C : Type} [Field C] [CharZero C] {dd : ℕ}

def z1 (ζ : Fin dd →₀ ℕ) : Fin 1 × Fin dd →₀ ℕ := ζ.mapDomain fun j => ((0 : Fin 1), j)

theorem z2 : Z0 (![pt C dd 2] : Fin 1 → Pt C 3 dd) := by
  intro k i
  simp [pt]

variable {V : VF C} {O : Type} [CommRing O] [StarRing O] (Y : FBChart C V O dd)

def TT (ν : Fin 2 × Fin dd →₀ ℕ) (ζ : Fin dd →₀ ℕ) (d : Fin 3 × Fin dd →₀ ℕ) : C :=
  coeff d Y.B.ph1 * (if lpart d = ν then coeff (z1 ζ) (∏ j, Y.nmul V.l j ^ d ((2 : Fin 3), j)) else 0)

end Ser

section Facts

variable {dd : ℕ}

def gg (ν : Fin 2 × Fin dd →₀ ℕ) (j : Fin dd) : Fin 3 × Fin dd →₀ ℕ := lo ν + zup (Finsupp.single j 1)

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] (Y : FBChart C V O dd)

end Facts

section Slice

variable {dd : ℕ} {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O]
  (Y : FBChart C V O dd)

end Slice

end CocycleSliceMultiplication

end Formalism.L2.FormalSeriesBounds
