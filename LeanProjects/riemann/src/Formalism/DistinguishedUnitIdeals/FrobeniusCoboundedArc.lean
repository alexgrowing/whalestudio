import Mathlib
import Formalism.DistinguishedUnitIdeals.FrobeniusDiffBijective
import Formalism.DistinguishedUnitIdeals.WordConsts
import Formalism.DistinguishedUnitIdeals.LemmaCFull

noncomputable section

namespace Formalism.ExponentWindows.E

open PowerSeries

def parM (ℓ hh g : ℕ) : ℕ := (hh + 2 * g) / (ℓ - 1) + 1

def parA (sig rr g ellmax : ℕ) : ℕ := 2 * sig + rr + 2 * g * ellmax

def parE (sig rr g ellmax kap : ℕ) : ℕ := 2 * rr + 4 * sig + 2 * parA sig rr g ellmax + 2 * kap

def LamOf {O : Type} [CommRing O] (B : Base O) {n : ℕ} (Cu : Cuts n) (H : ZMod n → ℕ → ℕ) :
    ZMod n → PowerSeries O :=
  fun c => Formalism.ExponentWindows.abelian₂ B.p (H c) (Cu.ell c)

structure PrimNum (ℓ : ℕ) {n : ℕ} (Cu : Cuts n) (j g G hh sig ellmax : ℕ) : Prop where

  G_le_g : G ≤ g

  g_le_h : g ≤ hh

  one_le_j : 1 ≤ j

  j_le_ell : ∀ c ∈ Cu.cuts, j ≤ Cu.ell c

  ell_le : ∀ c ∈ Cu.cuts, Cu.ell c ≤ ellmax

  sigOK : SigOK ℓ j (parM ℓ hh g) g sig

structure PrimBase {O : Type} [CommRing O] (B : Base O) (ϖ : O) (e : ℕ) : Prop where

  prime : B.ℓ.Prime

  three_le : 3 ≤ B.ℓ

  one_le_e : 1 ≤ e

  assoc : Associated (B.ℓ : O) (ϖ ^ e)

  complete : IsAdicComplete (Ideal.span {(B.ℓ : O)}) O

  e3 : B.E3

  e4 : B.E4

structure PrimLat {O : Type} [CommRing O] {B : Base O} {n : ℕ} {V : Type} [AddCommGroup V]
    [Module (PowerSeries O) V] (L : Lat B n V) (Cu : Cuts n) (j G hh : ℕ) : Prop where

  p9 : L.P9

  p5M : ∀ i, L.P5M i hh

  frobeniusBounded_after : ∀ c ∈ Cu.cuts, ∀ k : ℕ, 1 ≤ k → k ≤ j → L.P5M (c + (k : ZMod n)) G

  pullFree : ∀ c ∈ Cu.cuts, L.PullFree c j

  free : ∀ i, L.Free i

  ltors : L.LTors

structure PrimUnit {O : Type} [CommRing O] {B : Base O} {n : ℕ} {V₀ : Type} [AddCommGroup V₀]
    [Module (PowerSeries O) V₀] (L₀ : Lat B n V₀) (e₀ : V₀) : Prop where

  φ_fix : ∀ i, L₀.φ i e₀ = e₀

  γ_fix : ∀ i, L₀.γ i e₀ = e₀

  N_eq : ∀ i, L₀.N i = Submodule.span (PowerSeries O) {e₀}

  tors : ∀ a : PowerSeries O, a • e₀ = 0 → a = 0

structure PrimExt {O : Type} [CommRing O] {B : Base O} {n : ℕ} {V₂ V₀ : Type} [AddCommGroup V₂]
    [Module (PowerSeries O) V₂] [AddCommGroup V₀] [Module (PowerSeries O) V₀]
    {L₂ : Lat B n V₂} {L₀ : Lat B n V₀} (Y : Ext L₂ L₀) (e₀ : V₀) (Cu : Cuts n) (j G rr : ℕ)
    (H : ZMod n → ℕ → ℕ) : Prop where

  lift : ∀ c ∈ Cu.cuts, Y.Lift e₀ c rr

  p9 : Y.LY.P9

  p6 : Y.P6

  frobeniusBounded_after : ∀ c ∈ Cu.cuts, ∀ k : ℕ, 1 ≤ k → k ≤ j → Y.LY.P5M (c + (k : ZMod n)) G

  frobeniusCobounded_arc : ∀ c ∈ Cu.cuts, ∀ s < Cu.ell c, Y.LY.FrobeniusCobounded (c - (s : ZMod n)) (H c s)

  pullFree : ∀ c ∈ Cu.cuts, Y.LY.PullFree c j

def WordDD0 (ell : ℕ) (kind : ℕ → Kind) : Prop :=
  ∃ s₀ s₁ : ℕ, s₀ < s₁ ∧ s₁ < ell ∧ kind s₁ = Kind.down ∧ kind s₀ = Kind.down ∧
    ∀ s < ell, s ≠ s₀ → s ≠ s₁ → kind s = Kind.thin

def WordUD0 (ℓ ell a₀ : ℕ) (b : ℕ → ℕ) (kind : ℕ → Kind) : Prop :=
  ∃ s₀ s₁ : ℕ, s₀ < s₁ ∧ s₁ < ell ∧ kind s₁ = Kind.up ∧ kind s₀ = Kind.down ∧
    (∀ s < ell, s ≠ s₀ → s ≠ s₁ → kind s = Kind.thin) ∧
    2 * b s₀ ≤ ℓ * b s₁ ∧ 2 * a₀ < b s₁

def PrimWord (ℓ ell a₀ : ℕ) (b : ℕ → ℕ) (kind : ℕ → Kind) : Prop :=
  WordNone ell kind ∨ WordD ell kind ∨ WordDU ℓ ell b kind ∨ WordDD0 ell kind ∨
    WordUD0 ℓ ell a₀ b kind

section
variable {O : Type} [CommRing O] {B : Base O} {n : ℕ} {V₁ V₂ : Type} [AddCommGroup V₁]
  [Module (PowerSeries O) V₁] [AddCommGroup V₂] [Module (PowerSeries O) V₂]
  {L₁ : Lat B n V₁} {L₂ : Lat B n V₂}

structure PrimArcProps (h : LatHom L₁ L₂) (c : ZMod n) (ell : ℕ) (H : ℕ → ℕ)
    (g sig rr a₀ kap : ℕ) (ϖ : O) {r₁ r₂ : ℕ}
    (S₁ : LevelData L₁ c ell (Formalism.ExponentWindows.abelian₂ B.p H ell) r₁)
    (S₂ : LevelData L₂ c ell (Formalism.ExponentWindows.abelian₂ B.p H ell) r₂) (m : LevelMap h S₁ S₂)
    (b : ℕ → ℕ) (kind : ℕ → Kind) (U₁ : ℕ → Submodule O (Fin r₁ → O))
    (U₂ : ℕ → Submodule O (Fin r₂ → O)) (PP PP' : Polynomial O) : Prop where

  p4c₁ : L₁.GammaCongruentArc c ell (Formalism.ExponentWindows.abelian₂ B.p H ell)

  p4c₂ : L₂.GammaCongruentArc c ell (Formalism.ExponentWindows.abelian₂ B.p H ell)

  equiv₁ : S₁.Equiv

  equiv₂ : S₂.Equiv

  k2iii : S₂.K2iii

  rd₁ : S₁.RD g

  rd₂ : S₂.RD g

  k3a2 : S₂.K3a2 g PP

  k3a4 : S₁.K3a4 g PP'

  dcFix : S₁.DcFix

  partner₁ : S₁.Partner sig

  partner₂ : S₂.Partner sig

  p3₁ : S₁.P3

  p3₂ : S₂.P3

  flReg : S₂.FlReg ϖ H

  p4a₁ : S₁.DivisibleIff g

  p4a₂ : S₂.DivisibleIff g

  p4b₁ : S₁.XMulIff

  p4b₂ : S₂.XMulIff

  bridge₁ : S₁.Bridge ϖ H b kind U₁

  bridge₂ : S₂.Bridge ϖ H b kind U₂

  mapFl : m.MapFl

  p4d : h.LiftsDivisible c ell g rr

  lLift : LLift B.ℓ rr m.prL

  cMap : ∀ s < ell, kind s = Kind.up → CMap (U₁ s) (U₂ s) m.prL

  ppval : PPval B.ℓ kap PP PP'

  sat₁ : ∀ s < ell, Saturated ϖ (U₁ s)

  sat₂ : ∀ s < ell, Saturated ϖ (U₂ s)

  b_le_H : ∀ s < ell, kind s = Kind.up → b s ≤ H s

  g_lt_b : ∀ s < ell, kind s ≠ Kind.thin → g < b s

  word : PrimWord B.ℓ ell a₀ b kind

def PrimArc (h : LatHom L₁ L₂) (c : ZMod n) (ell : ℕ) (H : ℕ → ℕ) (g sig rr a₀ kap : ℕ) (ϖ : O) :
    Prop :=
  ∃ (r₁ r₂ : ℕ) (S₁ : LevelData L₁ c ell (Formalism.ExponentWindows.abelian₂ B.p H ell) r₁)
    (S₂ : LevelData L₂ c ell (Formalism.ExponentWindows.abelian₂ B.p H ell) r₂) (m : LevelMap h S₁ S₂)
    (b : ℕ → ℕ) (kind : ℕ → Kind) (U₁ : ℕ → Submodule O (Fin r₁ → O))
    (U₂ : ℕ → Submodule O (Fin r₂ → O)) (PP PP' : Polynomial O),
    PrimArcProps h c ell H g sig rr a₀ kap ϖ S₁ S₂ m b kind U₁ U₂ PP PP'

end

structure PrimBK {O : Type} [CommRing O] {B : Base O} {n : ℕ} {V₁ V₂ V₀ : Type} [AddCommGroup V₁]
    [Module (PowerSeries O) V₁] [AddCommGroup V₂] [Module (PowerSeries O) V₂] [AddCommGroup V₀]
    [Module (PowerSeries O) V₀] (L₁ : Lat B n V₁) (L₂ : Lat B n V₂) (L₀ : Lat B n V₀) (e₀ : V₀)
    (Cu : Cuts n) (H : ZMod n → ℕ → ℕ) (j g G hh sig rr : ℕ)
    (Zf₁ : AddSubgroup ((ZMod n → V₁) × (ZMod n → V₁)))
    (Zf₂ : AddSubgroup ((ZMod n → V₂) × (ZMod n → V₂))) : Prop where

  smul : ∀ (m : O), ∀ κ ∈ Zf₁, (C m • κ.1, C m • κ.2) ∈ Zf₁

  rho : ∀ c ∈ Cu.cuts, ∀ w, L₁.Wc Cu (LamOf B Cu H) c w →
    ∀ y z, L₁.IsRho c j (parM B.ℓ hh g) g sig w y z → (y, z) ∈ Zf₁

  ext : ∀ κ ∈ Zf₂, ∃ Y : Ext L₂ L₀, Y.Rep e₀ κ.1 κ.2 ∧ PrimExt Y e₀ Cu j G rr H

def ThmEPrim : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (B : Base O) (e n : ℕ) [NeZero n] (Cu : Cuts n) (H : ZMod n → ℕ → ℕ)
    (j g G hh sig rr kap ellmax : ℕ)
    (V₁ V₂ V₀ : Type) [AddCommGroup V₁] [Module (PowerSeries O) V₁] [AddCommGroup V₂]
    [Module (PowerSeries O) V₂] [AddCommGroup V₀] [Module (PowerSeries O) V₀]
    (L₁ : Lat B n V₁) (L₂ : Lat B n V₂) (L₀ : Lat B n V₀) (e₀ : V₀) (h : LatHom L₁ L₂)
    (Zf₁ : AddSubgroup ((ZMod n → V₁) × (ZMod n → V₁)))
    (Zf₂ : AddSubgroup ((ZMod n → V₂) × (ZMod n → V₂))),
    PrimBase B ϖ e → PrimNum B.ℓ Cu j g G hh sig ellmax →
    PrimLat L₁ Cu j G hh → PrimLat L₂ Cu j G hh → PrimUnit L₀ e₀ →
    PrimBK L₁ L₂ L₀ e₀ Cu H j g G hh sig rr Zf₁ Zf₂ →
    (∀ c ∈ Cu.cuts, PrimArc h c (Cu.ell c) (H c) g sig rr (parA sig rr g ellmax) kap ϖ) →
    ∀ κ ∈ Zf₂, ∃ κ₁ ∈ Zf₁,
      L₂.IsCobound (B.lc ^ parE sig rr g ellmax kap • κ.1 - fun i => h.f (κ₁.1 i))
        (B.lc ^ parE sig rr g ellmax kap • κ.2 - fun i => h.f (κ₁.2 i))

section
variable {O : Type} [CommRing O] {B : Base O} {n : ℕ}

def Lat.Inv {V : Type} [AddCommGroup V] [Module (PowerSeries O) V] (_L : Lat B n V)
    (a : PowerSeries O) : Prop :=
  Function.Bijective fun v : V => a • v

def LatHom.WPrime {V₁ V₂ : Type} [AddCommGroup V₁] [Module (PowerSeries O) V₁] [AddCommGroup V₂]
    [Module (PowerSeries O) V₂] {L₁ : Lat B n V₁} {L₂ : Lat B n V₂} (h : LatHom L₁ L₂) (c : ZMod n)
    (rr : ℕ) : Prop :=
  ∀ x ∈ L₂.N c, ∃ y ∈ L₁.N c, h.f y = B.lc ^ rr • x

end

def GammaCongruentArcOf : Prop :=
  ∀ (O : Type) [CommRing O] (B : Base O) (n : ℕ) [NeZero n]
    (V : Type) [AddCommGroup V] [Module (PowerSeries O) V] (L : Lat B n V) (c : ZMod n) (ell : ℕ)
    (H : ℕ → ℕ), B.E3 → B.E4 → L.P9 → L.Inv X → L.GammaCongruentArc c ell (Formalism.ExponentWindows.abelian₂ B.p H ell)

def LiftsDivisibleOf : Prop :=
  ∀ (O : Type) [CommRing O] (B : Base O) (n : ℕ)
    (V₁ V₂ : Type) [AddCommGroup V₁] [Module (PowerSeries O) V₁] [AddCommGroup V₂]
    [Module (PowerSeries O) V₂] (L₁ : Lat B n V₁) (L₂ : Lat B n V₂) (h : LatHom L₁ L₂) (c : ZMod n)
    (ell g rr : ℕ), L₁.Inv (B.Th ell g) → L₂.Inv (B.Th ell g) → h.WPrime c rr →
    h.LiftsDivisible c ell g rr

end Formalism.ExponentWindows.E
