import Mathlib
import Formalism.DistinguishedUnitIdeals.ArcLiftOfLocalizationData
import Formalism.DistinguishedUnitIdeals.FrobeniusDiffBijective
import Formalism.DistinguishedUnitIdeals.ExistsConstOfInvariantMod
import Formalism.DistinguishedUnitIdeals.LemmaCFull
import Formalism.DistinguishedUnitIdeals.FrobeniusCoboundedArc

noncomputable section

namespace Formalism.ExponentWindows.E

open PowerSeries

section ring
variable {O : Type} [CommRing O]

def Base.ff' (B : Base O) (ell j M g : ℕ) : PowerSeries O := (⇑B.φ)^[ell - j] (B.ff j M g)

end ring

section lat
variable {O : Type} [CommRing O] {B : Base O} {n : ℕ} {V : Type} [AddCommGroup V]
  [Module (PowerSeries O) V]

def Lat.Hinv (L : Lat B n V) (i : ZMod n) (M : ℕ) {r : ℕ} (e : Fin r → V) : Prop :=
  ∀ m : Fin r, ∃ (K K₀ : ℕ) (a b : ℕ → ℕ) (y : ℕ → Fin r → PowerSeries O) (D : Fin r → V),
    (∀ t < M, a t + b t = K ∧ (B.ℓ - 1) * a t ≤ B.ℓ * t) ∧
    (∀ k, D k ∈ L.N i ∧ D k - B.lc ^ K₀ • e k ∈ sm X (L.N i) ∧
      L.γ i (D k) - D k ∈ sm (X ^ M) (L.N i)) ∧
    B.lc ^ (K + K₀) • e m - ∑ k, (∑ t ∈ Finset.range M, B.lc ^ b t * X ^ t * y t k) • D k ∈
      sm (X ^ M) (L.N i)

variable {L : Lat B n V} {c : ZMod n} {ell : ℕ} {Λ : PowerSeries O} {r : ℕ}

def LevelData.Mem (S : LevelData L c ell Λ r) : Prop :=
  ∀ x : ↥(L.W c ell Λ), (x : V) ∈ L.N c ↔ ∀ s < ell, S.loc s x ∈ S.Nl s

def LevelData.UnitsAt (S : LevelData L c ell Λ r) : Prop :=
  ∀ s < ell, (∀ e : S.Lv, (X : PowerSeries O) • e ∈ S.Nl s → e ∈ S.Nl s) ∧
    ∀ s' < ell, s' ≠ s → ∀ e : S.Lv, B.p s' • e ∈ S.Nl s → e ∈ S.Nl s

def LevelData.LocalizesConst (S : LevelData L c ell Λ r) (M : ℕ) (e : Fin r → V) : Prop :=
  ∀ (x : V) (a : Fin r → O) (w : ↥(L.W c ell Λ)), x ∈ L.N (c - (ell : ZMod n)) →
    L.γ (c - (ell : ZMod n)) x - x ∈ sm (X ^ M) (L.N (c - (ell : ZMod n))) →
    x - ∑ k, C (a k) • e k ∈ sm X (L.N (c - (ell : ZMod n))) →
    Λ • (w : V) = L.phiIt (c - (ell : ZMod n)) ell x →
    ∀ s < ell, S.loc s w - S.locL s (cst a) ∈ S.Fl s

def LevelData.FlP (S : LevelData L c ell Λ r) (f' : PowerSeries O) : Prop :=
  ∀ s < ell, ∀ w : ↥(L.W c ell Λ), f' • S.loc s w ∈ S.Fl s

def LevelData.FlSat (S : LevelData L c ell Λ r) : Prop :=
  ∀ s < ell, ∀ e : S.Lv, B.lc • e ∈ S.Fl s → e ∈ S.Fl s

end lat

def GammaCongruentArcFromStart : Prop :=
  ∀ (O : Type) [CommRing O] (B : Base O) (n : ℕ) [NeZero n]
    (V : Type) [AddCommGroup V] [Module (PowerSeries O) V] (L : Lat B n V) (c : ZMod n)
    (ell : ℕ) (H : ℕ → ℕ), B.E3 → B.E4 → L.GamN (c - (ell : ZMod n)) → L.Inv X →
    L.GammaCongruentArc c ell (Formalism.ExponentWindows.abelian₂ B.p H ell)

def DivisibleIffOf : Prop :=
  ∀ (O : Type) [CommRing O] (B : Base O) (n : ℕ) [NeZero n]
    (V : Type) [AddCommGroup V] [Module (PowerSeries O) V] (L : Lat B n V) (c : ZMod n)
    (ell : ℕ) (hh H : ℕ → ℕ) (r : ℕ) (S : LevelData L c ell (Formalism.ExponentWindows.abelian₂ B.p H ell) r) (g : ℕ),
    (∀ s < ell, L.FrobeniusCobounded (c - (s : ZMod n)) (hh s)) → (∀ s < ell, hh s + g ≤ H s) →
    S.Mem → S.UnitsAt → S.DivisibleIff g

def XMulIffOf : Prop :=
  ∀ (O : Type) [CommRing O] (B : Base O) (n : ℕ) [NeZero n]
    (V : Type) [AddCommGroup V] [Module (PowerSeries O) V] (L : Lat B n V) (c : ZMod n)
    (ell : ℕ) (hh H : ℕ → ℕ) (r : ℕ) (S : LevelData L c ell (Formalism.ExponentWindows.abelian₂ B.p H ell) r),
    (∀ s < ell, L.FrobeniusCobounded (c - (s : ZMod n)) (hh s)) → (∀ s < ell, hh s ≤ H s) →
    S.Mem → S.UnitsAt → S.XMulIff

def TruncPullOf : Prop :=
  ∀ (O : Type) [CommRing O] (B : Base O) (ell j M g sig : ℕ), j ≤ ell → B.Trunc j M g sig →
    ∀ t a : ℕ, (B.ℓ - 1) * a ≤ B.ℓ * t → ∃ x : PowerSeries O,
      B.lc ^ sig * ((⇑B.φ)^[ell] X) ^ t - B.lc ^ a * x ∈ Ideal.span {B.ff' ell j M g}

def PartnerOf : Prop :=
  ∀ (O : Type) [CommRing O] (B : Base O) (n : ℕ) [NeZero n]
    (V : Type) [AddCommGroup V] [Module (PowerSeries O) V] (L : Lat B n V) (c : ZMod n)
    (ell : ℕ) (H : ℕ → ℕ) (r : ℕ) (S : LevelData L c ell (Formalism.ExponentWindows.abelian₂ B.p H ell) r)
    (j M g sig : ℕ) (e : Fin r → V), j ≤ ell → B.Good j M g → B.Trunc j M g sig →
    Submodule.span (PowerSeries O) (Set.range e) = L.N (c - (ell : ZMod n)) →
    L.GamN (c - (ell : ZMod n)) → L.H (c - (ell : ZMod n)) M → L.Hinv (c - (ell : ZMod n)) M e →
    (∀ s < ell, L.Inv (B.p s)) → S.LocalizesConst M e → S.FlP (B.ff' ell j M g) → S.FlSat → S.Partner sig

def HinvOf : Prop :=
  ∀ (O : Type) [CommRing O] (B : Base O) (u₁ : O) (n : ℕ) [NeZero n] (M : ℕ)
    (V : Type) [AddCommGroup V] [Module (PowerSeries O) V] (L : Lat B n V) (i : ZMod n)
    (r : ℕ) (e : Fin r → V), B.ℓ.Prime → B.GammaXUnitShape u₁ → L.P9 →
    Submodule.span (PowerSeries O) (Set.range e) = L.N i → L.Hinv i M e

structure PrimPart {O : Type} [CommRing O] {B : Base O} {n : ℕ} {V : Type} [AddCommGroup V]
    [Module (PowerSeries O) V] (L : Lat B n V) (c : ZMod n) (ell : ℕ) (hh H : ℕ → ℕ) {r : ℕ}
    (S : LevelData L c ell (Formalism.ExponentWindows.abelian₂ B.p H ell) r) (j M g : ℕ) (e : Fin r → V) : Prop where

  invX : L.Inv X

  invP : ∀ s < ell, L.Inv (B.p s)

  p9 : L.P9

  p5h : ∀ s < ell, L.FrobeniusCobounded (c - (s : ZMod n)) (hh s)

  hh_le : ∀ s < ell, hh s + g ≤ H s

  span : Submodule.span (PowerSeries O) (Set.range e) = L.N (c - (ell : ZMod n))

  mem : S.Mem

  unitsAt : S.UnitsAt

  pa1b : S.LocalizesConst M e

  flP : S.FlP (B.ff' ell j M g)

  flSat : S.FlSat

def PartnersPrim : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O) (B : Base O)
    (n : ℕ) [NeZero n] (V : Type) [AddCommGroup V] [Module (PowerSeries O) V] (L : Lat B n V)
    (c : ZMod n) (ell : ℕ) (hh H : ℕ → ℕ) (r : ℕ) (S : LevelData L c ell (Formalism.ExponentWindows.abelian₂ B.p H ell) r)
    (j M g sig : ℕ) (e : Fin r → V),
    Irreducible ϖ → ϖ ∣ (B.ℓ : O) → B.ℓ.Prime → 3 ≤ B.ℓ → B.E3 → B.E4 →
    1 ≤ j → j ≤ ell → 3 * g ≤ (B.ℓ - 1) * M → SigOK B.ℓ j M g sig →
    PrimPart L c ell hh H S j M g e →
    L.GammaCongruentArc c ell (Formalism.ExponentWindows.abelian₂ B.p H ell) ∧ S.DivisibleIff g ∧ S.XMulIff ∧ S.Partner sig

end Formalism.ExponentWindows.E

namespace Formalism.ExponentWindows.G

open TensorProduct

def ordF (ell j ℓ M g s : ℕ) : ℕ := if s < ell - j then (ℓ - 1) * M else 3 * g

def HK (g G Sz η : ℕ) (kind : Kind) (b : ℕ) : ℕ :=
  match kind with
  | Kind.thin => g + G
  | Kind.up => g + (b + Sz)
  | Kind.down => g + η

def HeightNumerics (ell j ℓ M g G Sz η h : ℕ) (kind : ℕ → Kind) (b : ℕ → ℕ) : Prop :=
  h + 2 * g < (ℓ - 1) * M ∧ G ≤ g ∧ Sz ≤ g ∧ η ≤ g ∧ g ≤ h ∧
    ∀ s < ell, kind s ≠ Kind.thin → b s + Sz ≤ h ∧ s < ell - j

def HeightLeTruncOrder : Prop :=
  ∀ (ell j ℓ M g G Sz η h : ℕ) (kind : ℕ → Kind) (b : ℕ → ℕ),
    HeightNumerics ell j ℓ M g G Sz η h kind b → ∀ s < ell,
      match kind s with
      | Kind.thin => HK g G Sz η (kind s) (b s) + g ≤ ordF ell j ℓ M g s
      | Kind.up => HK g G Sz η (kind s) (b s) + (g + 1) ≤ ordF ell j ℓ M g s
      | Kind.down => HK g G Sz η (kind s) (b s) + (b s + Sz + 1) ≤ ordF ell j ℓ M g s

def Tw {LL D : Type} [Field LL] [AddCommGroup D] [Module LL D] (m : ℤ) (i : ℤ) : Submodule LL D :=
  if m ≤ i then ⊤ else ⊥

section
variable {O : Type} [CommRing O] {B : E.Base O} {n : ℕ} {V : Type} [AddCommGroup V]
  [Module (PowerSeries O) V] {L : E.Lat B n V} {c : ZMod n} {ell : ℕ} {Λ : PowerSeries O} {r : ℕ}
  {S : E.LevelData L c ell Λ r} {LL : Type} [Field LL] [Algebra O LL]
  {Ks : ℕ → Type} [∀ s, CommRing (Ks s)] [∀ s, Algebra LL (Ks s)] {Δ D : Type}
  [AddCommGroup D] [Module LL D]

def LevelModel.FlDef (R : LevelModel S LL Ks Δ D) (f' : PowerSeries O) : Prop :=
  ∀ s < ell, ∀ e : S.Lv, e ∈ S.Fl s ↔ ∃ x ∈ Xi (Ks s) (Tw (LL := LL) (D := D) 0),
    R.pr s (Λ • e) = HahnSeries.ofPowerSeries ℤ (Ks s) (R.ρ s f') • x

def LevelModel.FlIs (R : LevelModel S LL Ks Δ D) (od : ℕ → ℤ) : Prop :=
  ∀ s < ell, ∀ e : S.Lv, e ∈ S.Fl s ↔ R.pr s e ∈ Xi (Ks s) (Tw (LL := LL) (D := D) (od s))

def LevelModel.UnitsAt (R : LevelModel S LL Ks Δ D) : Prop :=
  ∀ s < ell, IsUnit (R.ρ s PowerSeries.X) ∧ ∀ s' < ell, s' ≠ s → IsUnit (R.ρ s (B.p s'))

def LevelModel.LocLIs (R : LevelModel S LL Ks Δ D) (lam : Fin r → D) : Prop :=
  ∀ s < ell, ∀ y : Fin r → PowerSeries O, R.pr s (Λ • S.locL s y) =
    ∑ k, HahnSeries.ofPowerSeries ℤ (Ks s) (R.ρ s (y k)) • cstD (Ks s) (lam k)

def LevelModel.LocReg (R : LevelModel S LL Ks Δ D) : Prop :=
  ∀ s < ell, ∀ w : ↥(L.W c ell Λ), R.pr s (Λ • S.loc s w) ∈ Xi (Ks s) (Tw (LL := LL) (D := D) 0)

def LevelModel.Compl (R : LevelModel S LL Ks Δ D) (ϖ : O) : Prop :=
  ∀ s < ell, ∀ (k : ℕ) (a : PowerSeries O), PowerSeries.X ^ k ∣ R.ρ s a →
    ∃ (N : ℕ) (z : PowerSeries O), PowerSeries.C (ϖ ^ N) * a = B.p s ^ k * z

end

def FShape {O : Type} [CommRing O] (B : E.Base O) (ell j M g : ℕ) : Prop :=
  ∃ u : (PowerSeries O)ˣ, B.ff' ell j M g =
    (u : PowerSeries O) * PowerSeries.X ^ M *
      ∏ s ∈ Finset.range ell, B.p s ^ ordF ell j B.ℓ M g s

def FShapeOf : Prop :=
  ∀ (O : Type) [CommRing O] (B : E.Base O) (ell j M g : ℕ), j ≤ ell → B.E3 → FShape B ell j M g

def FlIsOf : Prop :=
  ∀ (O : Type) [CommRing O] (B : E.Base O) (n : ℕ) (V : Type) [AddCommGroup V]
    [Module (PowerSeries O) V] (L : E.Lat B n V) (c : ZMod n) (ell : ℕ) (Λ : PowerSeries O) (r : ℕ)
    (S : E.LevelData L c ell Λ r) (LL : Type) [Field LL] [Algebra O LL]
    (Ks : ℕ → Type) [∀ s, CommRing (Ks s)] [∀ s, Algebra LL (Ks s)] (Δ D : Type)
    [AddCommGroup D] [Module LL D] (R : LevelModel S LL Ks Δ D) (j M g : ℕ) (H : ℕ → ℕ),
    Λ = abelian₂ B.p H ell → FShape B ell j M g → R.K1b → R.UnitsAt →
    R.FlDef (B.ff' ell j M g) →
    R.FlIs (fun s => (ordF ell j B.ℓ M g s : ℤ) - (H s : ℤ))

def FiltrationLeOf : Prop :=
  ∀ (O : Type) [CommRing O] (B : E.Base O) (n : ℕ) (V : Type) [AddCommGroup V]
    [Module (PowerSeries O) V] (L : E.Lat B n V) (c : ZMod n) (ell : ℕ) (Λ : PowerSeries O) (r : ℕ)
    (S : E.LevelData L c ell Λ r) (LL : Type) [Field LL] [Algebra O LL]
    (Ks : ℕ → Type) [∀ s, CommRing (Ks s)] [∀ s, Algebra LL (Ks s)] (Δ D : Type)
    [AddCommGroup D] [Module LL D] (R : LevelModel S LL Ks Δ D) (j M g G Sz h : ℕ) (H : ℕ → ℕ),
    HeightNumerics ell j B.ℓ M g G Sz R.η h R.kind R.b →
    (∀ s < ell, H s = HK g G Sz R.η (R.kind s) (R.b s)) →
    (∀ s < ell, IsFilt (R.Fil s) ∧ Jumps (R.kind s) G Sz R.η (R.b s) (R.Fil s)) →
    R.FlIs (fun s => (ordF ell j B.ℓ M g s : ℤ) - (H s : ℤ)) → S.P3

def FlRegOf : Prop :=
  ∀ (O : Type) [CommRing O] (B : E.Base O) (n : ℕ) (V : Type) [AddCommGroup V]
    [Module (PowerSeries O) V] (L : E.Lat B n V) (c : ZMod n) (ell : ℕ) (Λ : PowerSeries O) (r : ℕ)
    (S : E.LevelData L c ell Λ r) (LL : Type) [Field LL] [Algebra O LL]
    (Ks : ℕ → Type) [∀ s, CommRing (Ks s)] [∀ s, Algebra LL (Ks s)] (Δ D : Type)
    [AddCommGroup D] [Module LL D] (R : LevelModel S LL Ks Δ D) (ϖ : O) (H : ℕ → ℕ) (od : ℕ → ℤ)
    (lam : Fin r → D),
    Λ = abelian₂ B.p H ell → R.K1b → R.FlIs od → (∀ s < ell, 0 ≤ od s) →
    R.LocLIs lam → LinearIndependent LL lam → R.Compl ϖ → S.FlReg ϖ H

def UnitsAtOf : Prop :=
  ∀ (O : Type) [CommRing O] (B : E.Base O) (n : ℕ) (V : Type) [AddCommGroup V]
    [Module (PowerSeries O) V] (L : E.Lat B n V) (c : ZMod n) (ell : ℕ) (Λ : PowerSeries O) (r : ℕ)
    (S : E.LevelData L c ell Λ r) (LL : Type) [Field LL] [Algebra O LL]
    (Ks : ℕ → Type) [∀ s, CommRing (Ks s)] [∀ s, Algebra LL (Ks s)] (Δ D : Type)
    [AddCommGroup D] [Module LL D] (R : LevelModel S LL Ks Δ D),
    R.UnitsAt → (∀ s < ell, Antitone (R.Fil s)) → S.UnitsAt

def FlSatOf : Prop :=
  ∀ (O : Type) [CommRing O] (B : E.Base O) (n : ℕ) (V : Type) [AddCommGroup V]
    [Module (PowerSeries O) V] (L : E.Lat B n V) (c : ZMod n) (ell : ℕ) (Λ : PowerSeries O) (r : ℕ)
    (S : E.LevelData L c ell Λ r) (LL : Type) [Field LL] [Algebra O LL]
    (Ks : ℕ → Type) [∀ s, CommRing (Ks s)] [∀ s, Algebra LL (Ks s)] (Δ D : Type)
    [AddCommGroup D] [Module LL D] (R : LevelModel S LL Ks Δ D) (od : ℕ → ℤ),
    algebraMap O LL (B.ℓ : O) ≠ 0 → R.FlIs od → S.FlSat

def FlPOf : Prop :=
  ∀ (O : Type) [CommRing O] (B : E.Base O) (n : ℕ) (V : Type) [AddCommGroup V]
    [Module (PowerSeries O) V] (L : E.Lat B n V) (c : ZMod n) (ell : ℕ) (Λ : PowerSeries O) (r : ℕ)
    (S : E.LevelData L c ell Λ r) (LL : Type) [Field LL] [Algebra O LL]
    (Ks : ℕ → Type) [∀ s, CommRing (Ks s)] [∀ s, Algebra LL (Ks s)] (Δ D : Type)
    [AddCommGroup D] [Module LL D] (R : LevelModel S LL Ks Δ D) (f' : PowerSeries O),
    R.FlDef f' → R.LocReg → S.FlP f'

structure PrimPartModel {O : Type} [CommRing O] {B : E.Base O} {n : ℕ} {V : Type} [AddCommGroup V]
    [Module (PowerSeries O) V] (L : E.Lat B n V) (c : ZMod n) (ell : ℕ) (hh H : ℕ → ℕ) {r : ℕ}
    (S : E.LevelData L c ell (abelian₂ B.p H ell) r) {LL : Type} [Field LL] [Algebra O LL]
    {Ks : ℕ → Type} [∀ s, CommRing (Ks s)] [∀ s, Algebra LL (Ks s)] {Δ D : Type}
    [AddCommGroup D] [Module LL D] (R : LevelModel S LL Ks Δ D) (ϖ : O) (j M g G Sz h : ℕ)
    (e : Fin r → V) (lam : Fin r → D) : Prop where

  invX : L.Inv PowerSeries.X

  invP : ∀ s < ell, L.Inv (B.p s)

  p9 : L.P9

  p5h : ∀ s < ell, L.FrobeniusCobounded (c - (s : ZMod n)) (hh s)

  hh_le : ∀ s < ell, hh s + g ≤ H s

  span : Submodule.span (PowerSeries O) (Set.range e) = L.N (c - (ell : ZMod n))

  mem : S.Mem

  pa1b : S.LocalizesConst M e

  locReg : R.LocReg

  k1b : R.K1b

  unitsAt : R.UnitsAt

  compl : R.Compl ϖ

  flDef : R.FlDef (B.ff' ell j M g)

  locLIs : R.LocLIs lam

  lamInd : LinearIndependent LL lam

  ell_ne : algebraMap O LL (B.ℓ : O) ≠ 0

  num : HeightNumerics ell j B.ℓ M g G Sz R.η h R.kind R.b

  H_eq : ∀ s < ell, H s = HK g G Sz R.η (R.kind s) (R.b s)

  filt : ∀ s < ell, IsFilt (R.Fil s) ∧ Jumps (R.kind s) G Sz R.η (R.b s) (R.Fil s)

def PartnersModel : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O) (B : E.Base O)
    (n : ℕ) [NeZero n] (V : Type) [AddCommGroup V] [Module (PowerSeries O) V] (L : E.Lat B n V)
    (c : ZMod n) (ell : ℕ) (hh H : ℕ → ℕ) (r : ℕ) (S : E.LevelData L c ell (abelian₂ B.p H ell) r)
    (LL : Type) [Field LL] [Algebra O LL]
    (Ks : ℕ → Type) [∀ s, CommRing (Ks s)] [∀ s, Algebra LL (Ks s)] (Δ D : Type)
    [AddCommGroup D] [Module LL D] (R : LevelModel S LL Ks Δ D) (j M g G Sz h sig : ℕ)
    (e : Fin r → V) (lam : Fin r → D),
    Irreducible ϖ → ϖ ∣ (B.ℓ : O) → B.ℓ.Prime → 3 ≤ B.ℓ → B.E3 → B.E4 →
    1 ≤ j → j ≤ ell → E.SigOK B.ℓ j M g sig →
    PrimPartModel L c ell hh H S R ϖ j M g G Sz h e lam →
    L.GammaCongruentArc c ell (abelian₂ B.p H ell) ∧ S.DivisibleIff g ∧ S.XMulIff ∧ S.Partner sig ∧ S.P3 ∧ S.FlReg ϖ H

end Formalism.ExponentWindows.G
