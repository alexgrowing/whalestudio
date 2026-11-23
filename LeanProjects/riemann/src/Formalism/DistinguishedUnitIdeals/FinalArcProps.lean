import Mathlib
import Formalism.DistinguishedUnitIdeals.ExistsConstOfInvariantMod
import Formalism.DistinguishedUnitIdeals.FrobeniusCoboundedArc
import Formalism.DistinguishedUnitIdeals.GammaCongruentArcFromStart
import Formalism.DistinguishedUnitIdeals.PhiFreeOfBasis

noncomputable section

namespace Formalism.ExponentWindows.E

open PowerSeries

def hJ (G₀ Sz η : ℕ) (kind : Kind) (b : ℕ) : ℕ :=
  match kind with
  | Kind.thin => G₀
  | Kind.up => b + Sz
  | Kind.down => η

def kindAt {n : ℕ} (kd : ZMod n → Kind) (c : ZMod n) : ℕ → Kind := fun s => kd (c - (s : ZMod n))

def sizeAt {n : ℕ} (bb : ZMod n → ℕ) (c : ZMod n) : ℕ → ℕ := fun s => bb (c - (s : ZMod n))

def HArc {n : ℕ} (g G₀ Sz η : ℕ) (kd : ZMod n → Kind) (bb : ZMod n → ℕ) : ZMod n → ℕ → ℕ :=
  fun c s => Formalism.ExponentWindows.G.HK g G₀ Sz η (kindAt kd c s) (sizeAt bb c s)

def win2 (kind : Kind) (g b : ℤ) : Finset ℤ :=
  match kind with
  | Kind.thin => Finset.Icc (-g) (-1)
  | Kind.up => Finset.Icc (-b - g) (-b - 1) ∪ Finset.Icc (-g) (-1)
  | Kind.down => Finset.Icc (-g) (-1) ∪ Finset.Icc (b - g) (b - 1)

def win4 (kind : Kind) (g G₀ Sz η b : ℤ) : Finset ℤ :=
  match kind with
  | Kind.thin => Finset.Icc (-G₀ - g) (G₀ - 1)
  | Kind.up => Finset.Icc (-b - Sz - g) (-b - 1) ∪ Finset.Icc (-η - g) (η - 1)
  | Kind.down => Finset.Icc (b - g) (b + Sz - 1) ∪ Finset.Icc (-η - g) (η - 1)

def jumpWindows (ell g : ℕ) (kind : ℕ → Kind) (b : ℕ → ℕ) : Finset ℤ :=
  (Finset.range ell).biUnion fun s => win2 (kind s) g (b s)

def wideWindows (ell g G₀ Sz η : ℕ) (kind : ℕ → Kind) (b : ℕ → ℕ) : Finset ℤ :=
  (Finset.range ell).biUnion fun s => win4 (kind s) g G₀ Sz η (b s)

def kapOf (ℓ E g h : ℕ) : ℝ :=
  (E : ℝ) + 7 * (g : ℝ) * ((E : ℝ) + 1 + 1 / ((ℓ : ℝ) - 1)) + 3 * Real.logb ℓ (2 * (h : ℝ))

def TextWord (ℓ ell a₀ : ℕ) (b : ℕ → ℕ) (kind : ℕ → Kind) : Prop :=
  (∃ t₀ t₁ : ℕ, ∀ s < ell, s ≠ t₀ → s ≠ t₁ → kind s = Kind.thin) ∧
  ∀ s₀ s₁ : ℕ, s₀ < s₁ → s₁ < ell →
    (kind s₁ = Kind.down → kind s₀ = Kind.up → b s₀ < ℓ * b s₁) ∧
    (kind s₁ = Kind.up → kind s₀ = Kind.down → 2 * b s₀ ≤ ℓ * b s₁ ∧ 2 * a₀ < b s₁)

structure FinalNum (ℓ : ℕ) {n : ℕ} (Cu : Cuts n) (kd : ZMod n → Kind) (bb : ZMod n → ℕ)
    (j g G₀ Sz η hh sig rr kap ellmax : ℕ) : Prop where

  G_le_g : G₀ ≤ g

  S_le_g : Sz ≤ g

  η_le_g : η ≤ g

  g_le_h : g ≤ hh

  g_lt_b : ∀ i, kd i ≠ Kind.thin → g < bb i

  b_le_h : ∀ i, kd i ≠ Kind.thin → bb i + Sz ≤ hh

  one_le_j : 1 ≤ j

  thin_after : ∀ c ∈ Cu.cuts, ∀ k : ℕ, 1 ≤ k → k ≤ j → kd (c + (k : ZMod n)) = Kind.thin

  j_le_ell : ∀ c ∈ Cu.cuts, j ≤ Cu.ell c

  ell_le : ∀ c ∈ Cu.cuts, Cu.ell c ≤ ellmax

  word : ∀ c ∈ Cu.cuts,
    TextWord ℓ (Cu.ell c) (parA sig rr g ellmax) (sizeAt bb c) (kindAt kd c)

  sigOK : SigOK ℓ j (parM ℓ hh g) g sig

  kapOK : ∀ c ∈ Cu.cuts,
    kapExp ℓ (Cu.ell c - 1) (jumpWindows (Cu.ell c) g (kindAt kd c) (sizeAt bb c)) ≤ kap ∧
    kapExp ℓ (Cu.ell c - 1) (wideWindows (Cu.ell c) g G₀ Sz η (kindAt kd c) (sizeAt bb c)) ≤ kap

def KapOfKAP : Prop :=
  ∀ (ℓ n : ℕ) (Cu : Cuts n) (kd : ZMod n → Kind) (bb : ZMod n → ℕ) (g G₀ Sz η hh kap ellmax a₀ : ℕ),
    ℓ.Prime → G₀ ≤ g → Sz ≤ g → η ≤ g → g ≤ hh → (∀ i, kd i ≠ Kind.thin → bb i + Sz ≤ hh) →
    (∀ c ∈ Cu.cuts, Cu.ell c ≤ ellmax) →
    (∀ c ∈ Cu.cuts, TextWord ℓ (Cu.ell c) a₀ (sizeAt bb c) (kindAt kd c)) →
    kapOf ℓ (ellmax - 1) g hh ≤ (kap : ℝ) →
    ∀ c ∈ Cu.cuts,
      kapExp ℓ (Cu.ell c - 1) (jumpWindows (Cu.ell c) g (kindAt kd c) (sizeAt bb c)) ≤ kap ∧
      kapExp ℓ (Cu.ell c - 1) (wideWindows (Cu.ell c) g G₀ Sz η (kindAt kd c) (sizeAt bb c)) ≤ kap

structure FinalBase {O : Type} [CommRing O] (B : Base O) (ϖ : O) (eO : ℕ) (u x : Oˣ)
    (LL : Type) [Field LL] [Algebra O LL] : Prop where

  prim : PrimBase B ϖ eO

  u_eq : (u : O) = 1 + (B.ℓ : O) * (x : O)

  frac : IsFractionRing O LL

structure FinalLat {O : Type} [CommRing O] {B : Base O} {n : ℕ} {V : Type} [AddCommGroup V]
    [Module (PowerSeries O) V] (L : Lat B n V) (Cu : Cuts n) (kd : ZMod n → Kind) (bb : ZMod n → ℕ)
    (j G₀ Sz η hh : ℕ) : Prop where

  prim : PrimLat L Cu j G₀ hh

  invX : L.Inv X

  invP : ∀ s, L.Inv (B.p s)

  p5h : ∀ i, L.FrobeniusCobounded i (hJ G₀ Sz η (kd i) (bb i))

def WPrimeCuts {O : Type} [CommRing O] {B : Base O} {n : ℕ} {V₁ V₂ : Type} [AddCommGroup V₁]
    [Module (PowerSeries O) V₁] [AddCommGroup V₂] [Module (PowerSeries O) V₂] {L₁ : Lat B n V₁}
    {L₂ : Lat B n V₂} (h : LatHom L₁ L₂) (Cu : Cuts n) (rr : ℕ) : Prop :=
  ∀ c ∈ Cu.cuts, h.WPrime c rr

structure FinalLevels {O : Type} [CommRing O] {B : Base O} {n : ℕ} {V : Type} [AddCommGroup V]
    [Module (PowerSeries O) V] (L : Lat B n V) (c : ZMod n) (ell : ℕ) (H : ℕ → ℕ) {r : ℕ}
    (S : LevelData L c ell (Formalism.ExponentWindows.abelian₂ B.p H ell) r) {LL : Type} [Field LL] [Algebra O LL]
    {Ks : ℕ → Type} [∀ s, CommRing (Ks s)] [∀ s, Algebra LL (Ks s)] {Δ D : Type}
    [AddCommGroup D] [Module LL D] (R : G.LevelModel S LL Ks Δ D) (ϖ : O) (u : Oˣ)
    (j M g G₀ Sz η : ℕ) (kind : ℕ → Kind) (b : ℕ → ℕ) (e : Fin r → V) (lam : Fin r → D)
    (U : ℕ → Submodule O (Fin r → O)) : Prop where

  kind_eq : ∀ s < ell, R.kind s = kind s

  b_eq : ∀ s < ell, R.b s = b s

  η_eq : R.η = η

  k1b : R.K1b

  hasU : R.HasU u

  k1c : ∀ s < ell, (R.lev s).FiniteOrderFixed B.ℓ s

  k1d : ∀ s < ell, (R.lev s).PhiGammaCommute

  unitsAt : R.UnitsAt

  compl : R.Compl ϖ

  filt : ∀ s < ell, IsFilt (R.Fil s)

  jumps : ∀ s < ell, G.Jumps (kind s) G₀ Sz η (b s) (R.Fil s)

  mem : S.Mem

  locReg : R.LocReg

  pa1b : S.LocalizesConst M e

  equiv : S.Equiv

  span : Submodule.span (PowerSeries O) (Set.range e) = L.N (c - (ell : ZMod n))

  ind : LinearIndependent (PowerSeries O) e

  flDef : R.FlDef (B.ff' ell j M g)

  locLIs : R.LocLIs lam

  lamInd : LinearIndependent LL lam

  lamSpan : Submodule.span LL (Set.range lam) = ⊤

  uIs : ∀ s < ell, ∀ v : Fin r → O,
    v ∈ U s ↔ ∑ k, algebraMap O LL (v k) • lam k ∈ G.UOf (kind s) (b s) η (R.Fil s)

section
variable {O : Type} [CommRing O] {B : Base O} {n : ℕ} {V₁ V₂ : Type} [AddCommGroup V₁]
  [Module (PowerSeries O) V₁] [AddCommGroup V₂] [Module (PowerSeries O) V₂]
  {L₁ : Lat B n V₁} {L₂ : Lat B n V₂}

structure ArcData (h : LatHom L₁ L₂) (c : ZMod n) (ell : ℕ) (H : ℕ → ℕ) (LL : Type) [Field LL]
    [Algebra O LL] (Ks : ℕ → Type) [∀ s, CommRing (Ks s)] [∀ s, Algebra LL (Ks s)] (Δ : Type) where
  r₁ : ℕ
  r₂ : ℕ
  S₁ : LevelData L₁ c ell (Formalism.ExponentWindows.abelian₂ B.p H ell) r₁
  S₂ : LevelData L₂ c ell (Formalism.ExponentWindows.abelian₂ B.p H ell) r₂
  m : LevelMap h S₁ S₂
  D₁ : Type
  D₂ : Type
  [acg₁ : AddCommGroup D₁]
  [mod₁ : Module LL D₁]
  [acg₂ : AddCommGroup D₂]
  [mod₂ : Module LL D₂]
  R₁ : G.LevelModel S₁ LL Ks Δ D₁
  R₂ : G.LevelModel S₂ LL Ks Δ D₂
  e₁ : Fin r₁ → V₁
  e₂ : Fin r₂ → V₂
  lam₁ : Fin r₁ → D₁
  lam₂ : Fin r₂ → D₂
  U₁ : ℕ → Submodule O (Fin r₁ → O)
  U₂ : ℕ → Submodule O (Fin r₂ → O)

attribute [instance] ArcData.acg₁ ArcData.mod₁ ArcData.acg₂ ArcData.mod₂

structure FinalArcProps {h : LatHom L₁ L₂} {c : ZMod n} {ell : ℕ} {H : ℕ → ℕ} {LL : Type} [Field LL]
    [Algebra O LL] {Ks : ℕ → Type} [∀ s, CommRing (Ks s)] [∀ s, Algebra LL (Ks s)] {Δ : Type}
    (A : ArcData h c ell H LL Ks Δ) (ϖ : O) (u : Oˣ) (j M g G₀ Sz η : ℕ) (kind : ℕ → Kind)
    (b : ℕ → ℕ) : Prop where

  lev₁ : FinalLevels L₁ c ell H A.S₁ A.R₁ ϖ u j M g G₀ Sz η kind b A.e₁ A.lam₁ A.U₁

  lev₂ : FinalLevels L₂ c ell H A.S₂ A.R₂ ϖ u j M g G₀ Sz η kind b A.e₂ A.lam₂ A.U₂

  mapFl : A.m.MapFl

  cMap : ∀ s < ell, kind s = Kind.up → CMap (A.U₁ s) (A.U₂ s) A.m.prL

  prLIs : ∀ k, h.f (A.e₁ k) - ∑ l, C (LinearMap.toMatrix' A.m.prL l k) • A.e₂ l ∈
    sm (X : PowerSeries O) (L₂.N (c - (ell : ZMod n)))

def FinalArc (h : LatHom L₁ L₂) (c : ZMod n) (ell : ℕ) (H : ℕ → ℕ) (LL : Type) [Field LL]
    [Algebra O LL] (Ks : ℕ → Type) [∀ s, CommRing (Ks s)] [∀ s, Algebra LL (Ks s)] (Δ : Type)
    (ϖ : O) (u : Oˣ) (j M g G₀ Sz η : ℕ) (kind : ℕ → Kind) (b : ℕ → ℕ) : Prop :=
  ∃ A : ArcData h c ell H LL Ks Δ, FinalArcProps A ϖ u j M g G₀ Sz η kind b

end

def ThmEFinal : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (B : Base O) (eO n : ℕ) [NeZero n] (Cu : Cuts n) (kd : ZMod n → Kind) (bb : ZMod n → ℕ)
    (j g G₀ Sz η hh sig rr kap ellmax : ℕ) (u x : Oˣ)
    (LL : Type) [Field LL] [Algebra O LL] (Ks : ℕ → Type) [∀ s, CommRing (Ks s)]
    [∀ s, Algebra LL (Ks s)] (Δ : Type)
    (V₁ V₂ V₀ : Type) [AddCommGroup V₁] [Module (PowerSeries O) V₁] [AddCommGroup V₂]
    [Module (PowerSeries O) V₂] [AddCommGroup V₀] [Module (PowerSeries O) V₀]
    (L₁ : Lat B n V₁) (L₂ : Lat B n V₂) (L₀ : Lat B n V₀) (e₀ : V₀) (h : LatHom L₁ L₂)
    (Zf₁ : AddSubgroup ((ZMod n → V₁) × (ZMod n → V₁)))
    (Zf₂ : AddSubgroup ((ZMod n → V₂) × (ZMod n → V₂))),
    FinalBase B ϖ eO u x LL → FinalNum B.ℓ Cu kd bb j g G₀ Sz η hh sig rr kap ellmax →
    FinalLat L₁ Cu kd bb j G₀ Sz η hh → FinalLat L₂ Cu kd bb j G₀ Sz η hh → PrimUnit L₀ e₀ →
    PrimBK L₁ L₂ L₀ e₀ Cu (HArc g G₀ Sz η kd bb) j g G₀ hh sig rr Zf₁ Zf₂ →
    WPrimeCuts h Cu rr →
    (∀ c ∈ Cu.cuts, FinalArc h c (Cu.ell c) (HArc g G₀ Sz η kd bb c) LL Ks Δ ϖ u j
      (parM B.ℓ hh g) g G₀ Sz η (kindAt kd c) (sizeAt bb c)) →
    ∀ κ ∈ Zf₂, ∃ κ₁ ∈ Zf₁,
      L₂.IsCobound (B.lc ^ parE sig rr g ellmax kap • κ.1 - fun i => h.f (κ₁.1 i))
        (B.lc ^ parE sig rr g ellmax kap • κ.2 - fun i => h.f (κ₁.2 i))

end Formalism.ExponentWindows.E
