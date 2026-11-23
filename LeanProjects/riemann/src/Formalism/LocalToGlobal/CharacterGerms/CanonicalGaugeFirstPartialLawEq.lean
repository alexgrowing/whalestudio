import Formalism.LocalToGlobal.CharacterGerms.ConstantZeroSecondCoordinate

noncomputable section

open scoped BigOperators
open Classical
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace Formalism.L2.FormalSeriesBounds

namespace CocycleIdentity

open PartialDerivEval

section Slice

variable {C : Type} [Field C] {V : VF C} {dd : ℕ}

def lo (ν : Fin 2 × Fin dd →₀ ℕ) : Fin 3 × Fin dd →₀ ℕ :=
  ν.mapDomain fun p => (Fin.castSucc p.1, p.2)

def ZOne (F : PS C 3 dd) : Prop :=
  ∀ α : Fin 3 × Fin dd →₀ ℕ, (∀ k, α ((2 : Fin 3), k) = 0) → coeff α F = if α = 0 then 1 else 0

def FrobZ (V : VF C) (F : PS C 3 dd) : Prop :=
  ∀ α : Fin 3 × Fin dd →₀ ℕ, (∃ k, ¬ V.l ∣ α ((2 : Fin 3), k)) → V.MM (coeff α F)

end Slice

section Geo

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
  (Y : FBChart C V O dd)

def lift (a : Pt C 2 dd) : Pt C 3 dd := fun j => ev (n := 3) ![pt C dd 0, pt C dd 1] (a j)

def uAt (a : Pt C 2 dd) : PS C 3 dd := ev ![lift a, pt C dd 2] Y.u2

abbrev S3 : Pt C 3 dd := addOf Y.B.G.F (pt C dd 0) (pt C dd 1)

abbrev L3 : Pt C 3 dd := comp1 (Y.nmul V.l) (pt C dd 2)

abbrev hx (a b : Pt C 3 dd) : PS C 3 dd := ev ![a, b] Y.h

abbrev G1 : PS C 3 dd := hx Y (pt C dd 0) (pt C dd 2) + hx Y (pt C dd 1) (pt C dd 2) - hx Y (S3 Y) (pt C dd 2)

end Geo

section Closed

def XSliceSt : Prop :=
  UnitSeriesFrobenius → ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ)
    (Y : FBChart C V O dd) (a : Pt C 2 dd), (∀ j, constantCoeff (a j) = 0) → (∀ j, IntS V (a j)) →
    IntS V (uAt Y a) ∧ ZOne (uAt Y a) ∧ FrobZ V (uAt Y a) ∧
      ∀ (i : Fin dd) (ν : Fin 2 × Fin dd →₀ ℕ),
        coeff (lo ν + Finsupp.single ((2 : Fin 3), i) V.l) (uAt Y a) = coeff ν (ev ![a] (Y.fS i))

def PhLSliceSt : Prop :=
  LMulFrobFBSt → ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ)
    (Y : FBChart C V O dd) (i : Fin dd),
    IntS V (ev ![pt C dd 0, pt C dd 1, L3 Y] Y.B.ph1) ∧ ZOne (ev ![pt C dd 0, pt C dd 1, L3 Y] Y.B.ph1) ∧
      FrobZ V (ev ![pt C dd 0, pt C dd 1, L3 Y] Y.B.ph1) ∧
      ∀ ν : Fin 2 × Fin dd →₀ ℕ,
        V.MM (coeff (lo ν + Finsupp.single ((2 : Fin 3), i) V.l) (ev ![pt C dd 0, pt C dd 1, L3 Y] Y.B.ph1) -
          coeff ν (∑ j, Y.cS j * MvPowerSeries.C (Y.V1 j i)))

def PhPowSliceSt : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ)
    (Y : FBChart C V O dd) (i : Fin dd),
    IntS V (Y.B.ph1 ^ V.l) ∧ ZOne (Y.B.ph1 ^ V.l) ∧ FrobZ V (Y.B.ph1 ^ V.l) ∧
      ∀ ν : Fin 2 × Fin dd →₀ ℕ,
        V.MM (coeff (lo ν + Finsupp.single ((2 : Fin 3), i) V.l) (Y.B.ph1 ^ V.l) - coeff ν (Y.cS i ^ V.l))

end Closed

end CocycleIdentity

end Formalism.L2.FormalSeriesBounds
