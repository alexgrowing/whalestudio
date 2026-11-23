import Formalism.LocalToGlobal.CharacterGerms.RowTieVal

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]

section Defs

variable (Y : FBChart C V O dd) (p : ∀ o, PairData Y d (I o))

def expAll (x : Fin dd) : MvPowerSeries (WVO I) C :=
  MvPowerSeries.subst (fun i : Fin dd => ∑ w : WVO I, (p w.1).u w.2.1 w.2.2 i •
    (MvPowerSeries.X w : MvPowerSeries (WVO I) C)) (un1 (Y.ex x))

def pull1 (F : PS C 1 dd) : MvPowerSeries (WVO I) C :=
  MvPowerSeries.subst (fun q : Fin 1 × Fin dd => expAll Y p q.2) F

def rowOf {n : ℕ} (b : Fin n) (F : MvPowerSeries (WVO I) C) : MvPowerSeries (Fin n × WVO I) C :=
  MvPowerSeries.subst (fun w : WVO I => (MvPowerSeries.X (b, w) : MvPowerSeries (Fin n × WVO I) C)) F

def pullN {n : ℕ} (F : PS C n dd) : MvPowerSeries (Fin n × WVO I) C :=
  MvPowerSeries.subst (fun q : Fin n × Fin dd => rowOf q.1 (expAll Y p q.2)) F

def toAllS (o : Orb) (F : MvPowerSeries (WV (I o)) C) : MvPowerSeries (WVO I) C :=
  MvPowerSeries.subst (fun w : WV (I o) => (MvPowerSeries.X (⟨o, w⟩ : WVO I) : MvPowerSeries (WVO I) C)) F

def LogCoordSt : Prop :=
  ∀ (n : ℕ) (ι : Type) [Fintype ι] (cp : ι → Fin n) (uv : ι → Fin dd → C) (P : MvPolynomial ι C)
    (Q : MvPolynomial (Fin n × WVO I) C), IsImgO (fun o => Y.raw (p o)) cp uv P Q →
    ∀ F : PS C n dd, MvPowerSeries.constantCoeff (DpolyN (Y.B.FK C) cp uv P F) = jetAt0 Q (pullN Y p F)

def UnitSt : Prop :=
  PairsSep Y p → ∃ U : PS C 1 dd, IntS V U ∧ V.v (MvPowerSeries.constantCoeff U) = 0 ∧
    pull1 Y p (FB.expS C ((Y.k : C) • Y.B.hL C Y.h Y.w0)) =
      pull1 Y p U * ∏ o, toAllS o (mvExp (Y.raw (p o)).hRow)

def GermLiftSt (H : ∀ o, (Y.raw (p o)).Hyps V) : Prop :=
  PairsSep Y p → ∀ (o : Orb) (S : ∀ g, Sys (((Y.raw (p o)).rowData (H o)).G g))
    (t : ∀ g, I o g → MvPowerSeries (I o g) C), (∀ g, (S g).IsT (t g)) →
    ∀ F ∈ IntGerm V t, ∃ G : PS C 1 dd, IntS V G ∧ pull1 Y p G = toAllS o F

end Defs

def LeafSt : Prop :=
  ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ]
    (X : RawChart C d I κ) (H : X.Hyps V) (n : ℕ) (Po : MvPolynomial (Fin n × WV I) C)
    (kind : Fin n → Option (Fin 2 × ZMod d × ZMod d)), RowsOK (X.rowData H).G (X.rowData H).Alt Po kind →
    ∀ gr : Fin n → MvPowerSeries (WV I) C,
      jetAt0 Po (∏ ρ, (rowCopy ρ (gr ρ) * mvExp (rowCopy ρ X.hRow))) = ValOf (X.rowData H).hL Po kind gr

def ValEqPFromCutsSt : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ) (d : ℕ) [NeZero d]
    (Orb : Type) [Fintype Orb] (I : Orb → Fin 2 → Type) [∀ o g, Fintype (I o g)]
    (Y : FBChart C V O dd) (p : ∀ o, PairData Y d (I o)) (H : ∀ o, (Y.raw (p o)).Hyps V) (Ls : LetSys C dd) (n : ℕ),
    LogCoordSt Y p → UnitSt Y p → GermLiftSt Y p H → LeafSt → ValEqPSt Y p H Ls n

end Formalism.L2.FormalSeriesBounds
