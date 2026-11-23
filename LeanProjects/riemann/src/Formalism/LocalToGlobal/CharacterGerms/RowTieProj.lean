import Formalism.LocalToGlobal.CharacterGerms.RowTieFB

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ}
  {I : Fin 2 → Type} [∀ g, Fintype (I g)]

def ProjSt (Y : FBChart C V O dd) (p : PairData Y d I) : Prop :=
  ∃ e : Fin 2 → Pt C 1 dd,
    (∀ g i, IntS V (e g i)) ∧ (∀ g i, MvPowerSeries.constantCoeff (e g i) = 0) ∧
    (∀ g, comp1 (e g) (addOf Y.B.G.F (pt C (n := 2) dd 0) (pt C (n := 2) dd 1)) =
      addOf Y.B.G.F (comp1 (e g) (pt C (n := 2) dd 0)) (comp1 (e g) (pt C (n := 2) dd 1))) ∧
    (∀ g, comp1 (e g) (e g) = e g) ∧
    (∀ g a, comp1 (e g) (Y.B.A.act a) = comp1 (Y.B.A.act a) (e g)) ∧
    (∀ g c, linAct (e g) (p.u g c) = p.u g c) ∧
    (∀ g (v : Fin dd → C), ∃ b : I g → C, linAct (e g) v = ∑ c, b c • p.u g c) ∧
    ∀ g, IntS V (FB.expS C (ev (n := 2) ![comp1 (e g) (pt C dd 0), pt C dd 1] Y.h -
      ev (n := 2) ![pt C dd 0, comp1 (e (1 - g)) (pt C dd 1)] Y.h))

def EndomorphismLimitAll : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ)
    (Y : FBChart C V O dd), EndomorphismLimitIntegral Y

def ProjFBSt : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ)
    (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (p : PairData Y d I),
    EndomorphismLimitIntegral Y → ProjSt Y p

end Formalism.L2.FormalSeriesBounds
