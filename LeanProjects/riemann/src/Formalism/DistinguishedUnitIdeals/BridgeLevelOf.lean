import Mathlib
import Formalism.DistinguishedUnitIdeals.GammaCongruentArcFromStart

noncomputable section

namespace Formalism.ExponentWindows.G

structure BridgeItems {O : Type} [CommRing O] {B : E.Base O} {n : ℕ} {V : Type} [AddCommGroup V]
    [Module (PowerSeries O) V] {L : E.Lat B n V} {c : ZMod n} {ell : ℕ} {Λ : PowerSeries O} {r : ℕ}
    {S : E.LevelData L c ell Λ r} {LL : Type} [Field LL] [Algebra O LL]
    {Ks : ℕ → Type} [∀ s, CommRing (Ks s)] [∀ s, Algebra LL (Ks s)] {Δ D : Type}
    [AddCommGroup D] [Module LL D] (R : LevelModel S LL Ks Δ D) (ϖ : O) (η : ℕ)
    (kind : ℕ → Kind) (b : ℕ → ℕ) (lam : Fin r → D) (U : ℕ → Submodule O (Fin r → O)) : Prop where

  frac : IsFractionRing O LL

  kind_eq : ∀ s < ell, R.kind s = kind s

  b_eq : ∀ s < ell, R.b s = b s

  η_eq : R.η = η

  k1b : R.K1b

  unitsAt : R.UnitsAt

  compl : R.Compl ϖ

  locLIs : R.LocLIs lam

  lamInd : LinearIndependent LL lam

  lamSpan : Submodule.span LL (Set.range lam) = ⊤

  uIs : ∀ s < ell, ∀ v : Fin r → O,
    v ∈ U s ↔ ∑ k, algebraMap O LL (v k) • lam k ∈ UOf (kind s) (b s) η (R.Fil s)

def BridgeLevelOf : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (B : E.Base O) (n : ℕ) (V : Type) [AddCommGroup V] [Module (PowerSeries O) V]
    (L : E.Lat B n V) (c : ZMod n) (ell : ℕ) (H : ℕ → ℕ) (r : ℕ)
    (S : E.LevelData L c ell (abelian₂ B.p H ell) r) (LL : Type) [Field LL] [Algebra O LL]
    (Ks : ℕ → Type) [∀ s, CommRing (Ks s)] [∀ s, Algebra LL (Ks s)] (Δ D : Type)
    [AddCommGroup D] [Module LL D] (R : LevelModel S LL Ks Δ D) (η : ℕ) (kind : ℕ → Kind)
    (b : ℕ → ℕ) (lam : Fin r → D) (U : ℕ → Submodule O (Fin r → O)),
    BridgeItems R ϖ η kind b lam U →
    ∀ s < ell, ∀ y : Fin r → PowerSeries O,
      S.locL s y ∈ S.Nb s ↔ LevelCond ϖ (B.p s) (H s) (b s) (kind s) (U s) y

def BridgeSatOf : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (B : E.Base O) (n : ℕ) (V : Type) [AddCommGroup V] [Module (PowerSeries O) V]
    (L : E.Lat B n V) (c : ZMod n) (ell : ℕ) (H : ℕ → ℕ) (r : ℕ)
    (S : E.LevelData L c ell (abelian₂ B.p H ell) r) (LL : Type) [Field LL] [Algebra O LL]
    (Ks : ℕ → Type) [∀ s, CommRing (Ks s)] [∀ s, Algebra LL (Ks s)] (Δ D : Type)
    [AddCommGroup D] [Module LL D] (R : LevelModel S LL Ks Δ D) (η : ℕ) (kind : ℕ → Kind)
    (b : ℕ → ℕ) (lam : Fin r → D) (U : ℕ → Submodule O (Fin r → O)),
    BridgeItems R ϖ η kind b lam U → ∀ s < ell, Saturated ϖ (U s)

def BridgeOf : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (B : E.Base O) (n : ℕ) (V : Type) [AddCommGroup V] [Module (PowerSeries O) V]
    (L : E.Lat B n V) (c : ZMod n) (ell : ℕ) (H : ℕ → ℕ) (r : ℕ)
    (S : E.LevelData L c ell (abelian₂ B.p H ell) r) (LL : Type) [Field LL] [Algebra O LL]
    (Ks : ℕ → Type) [∀ s, CommRing (Ks s)] [∀ s, Algebra LL (Ks s)] (Δ D : Type)
    [AddCommGroup D] [Module LL D] (R : LevelModel S LL Ks Δ D) (η : ℕ) (kind : ℕ → Kind)
    (b : ℕ → ℕ) (lam : Fin r → D) (U : ℕ → Submodule O (Fin r → O)),
    BridgeItems R ϖ η kind b lam U → S.Bridge ϖ H b kind U

end Formalism.ExponentWindows.G
