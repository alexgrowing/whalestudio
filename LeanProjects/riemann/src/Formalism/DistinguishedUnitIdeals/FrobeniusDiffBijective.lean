import Mathlib
import Formalism.DistinguishedUnitIdeals.StatementE

noncomputable section

namespace Formalism.ExponentWindows.E

open PowerSeries

section ring
variable {O : Type} [CommRing O]

def Base.E3 (B : Base O) : Prop :=
  ∃ u : (PowerSeries O)ˣ, B.φ X = (u : PowerSeries O) * X * B.q ^ (B.ℓ - 1)

def Base.E4 (B : Base O) : Prop :=
  ∃ e : (PowerSeries O)ˣ, B.γ X = X * (1 + (e : PowerSeries O) * B.q)

def Base.GammaXUnitShape (B : Base O) (u₁ : O) : Prop :=
  (∃ a : PowerSeries O, B.γ X = X * (C u₁ + X * a)) ∧
    ∀ r : ℕ, 1 ≤ r → ∃ ε : Oˣ, u₁ ^ r - 1 = (ε : O) * (B.ℓ : O) ^ (1 + padicValNat B.ℓ r)

def Base.mm (B : Base O) : Ideal (PowerSeries O) := Ideal.span {B.lc, X}

end ring

section lat
variable {O : Type} [CommRing O] {B : Base O} {n : ℕ} {V : Type} [AddCommGroup V]
  [Module (PowerSeries O) V]

def Lat.P5M (L : Lat B n V) (i : ZMod n) (m : ℕ) : Prop :=
  ∀ v ∈ L.N (i - 1), B.q ^ m • L.φ i v ∈ L.N i

def Lat.FrobeniusCobounded (L : Lat B n V) (i : ZMod n) (h : ℕ) : Prop :=
  ∀ v ∈ L.N i, B.q ^ h • v ∈ Submodule.span (PowerSeries O) (L.φ i '' (L.N (i - 1) : Set V))

def Lat.P9 (L : Lat B n V) : Prop := ∀ i, ∀ v ∈ L.N i, L.γ i v - v ∈ sm X (L.N i)

def Lat.PullFree (L : Lat B n V) (c : ZMod n) (k : ℕ) : Prop :=
  ∃ (r : ℕ) (e : Fin r → V), Submodule.span (PowerSeries O) (Set.range e) = L.N c ∧
    LinearIndependent (PowerSeries O) (fun a => L.phiIt c k (e a))

def Lat.Free (L : Lat B n V) (i : ZMod n) : Prop :=
  ∃ (r : ℕ) (e : Fin r → V), LinearIndependent (PowerSeries O) e ∧
    Submodule.span (PowerSeries O) (Set.range e) = L.N i

def Lat.Complete (L : Lat B n V) : Prop := ∀ i, IsAdicComplete B.mm (L.N i)

def Lat.XReg (L : Lat B n V) : Prop := ∀ i, ∀ v ∈ L.N i, (X : PowerSeries O) • v = 0 → v = 0

def Lat.LTors (_L : Lat B n V) : Prop := ∀ v : V, B.lc • v = 0 → v = 0

end lat

section ext
variable {O : Type} [CommRing O] {B : Base O} {n : ℕ} {V₂ V₀ : Type} [AddCommGroup V₂]
  [Module (PowerSeries O) V₂] [AddCommGroup V₀] [Module (PowerSeries O) V₀]
  {L₂ : Lat B n V₂} {L₀ : Lat B n V₀}

def Ext.P6 (Y : Ext L₂ L₀) : Prop := ∀ i (u : V₂), Y.ι.f u ∈ Y.LY.N i → u ∈ L₂.N i

def Ext.Lift (Y : Ext L₂ L₀) (e₀ : V₀) (c : ZMod n) (rr : ℕ) : Prop :=
  ∃ x ∈ Y.LY.N c, Y.π.f x = B.lc ^ rr • e₀

def Lat.PhiFree (L₀ : Lat B n V₀) (i : ZMod n) (k : ℕ) : Prop :=
  ∃ (r : ℕ) (b : Fin r → PowerSeries O),
    (∀ a : PowerSeries O, ∃ a' : Fin r → PowerSeries O, a = ∑ t, b t * (⇑B.φ)^[k] (a' t)) ∧
    ∀ m : Fin r → V₀, (∀ t, m t ∈ L₀.N i) → ∑ t, b t • L₀.phiIt i k (m t) = 0 → ∀ t, m t = 0

end ext

section ring2
variable {O : Type} [CommRing O]

def Base.E3it (B : Base O) (j : ℕ) : Prop :=
  ∃ u : (PowerSeries O)ˣ,
    (⇑B.φ)^[j] X = (u : PowerSeries O) * X * ∏ k ∈ Finset.range j, B.p k ^ (B.ℓ - 1)

def Base.E2 (B : Base O) (s : ℕ) : Prop :=
  B.p s ∈ Ideal.span {B.lc, (X : PowerSeries O) ^ (B.ℓ ^ s)}

def Base.Sat (B : Base O) (f : PowerSeries O) : Prop :=
  ∀ (K : ℕ) (a : PowerSeries O), B.lc ^ K * a ∈ Ideal.span {f} → a ∈ Ideal.span {f}

def SigOK (ℓ j M g sig : ℕ) : Prop :=
  (3 * g * ℓ ^ (j - 1) + M) * ℓ ≤ sig * (ℓ ^ (j - 1) * (ℓ - 1) ^ 2)

def Base.Trunc (B : Base O) (j M g sig : ℕ) : Prop :=
  ∀ r a : ℕ, (B.ℓ - 1) * a ≤ B.ℓ * r → ∃ x : PowerSeries O,
    B.lc ^ sig * ((⇑B.φ)^[j] X) ^ r - B.lc ^ a * x ∈ Ideal.span {B.ff j M g}

end ring2

section lat2
variable {O : Type} [CommRing O] {B : Base O} {n : ℕ} {V : Type} [AddCommGroup V]
  [Module (PowerSeries O) V]

def Lat.H (L : Lat B n V) (c : ZMod n) (M : ℕ) : Prop :=
  ∀ z ∈ sm X (L.N c), ∃ (K : ℕ) (a b : ℕ → ℕ) (d : ℕ → V),
    (∀ r, 1 ≤ r → r < M → a r + b r = K ∧ (B.ℓ - 1) * a r ≤ B.ℓ * r ∧ d r ∈ L.N c) ∧
    (L.γ c (∑ r ∈ Finset.Ico 1 M, (B.lc ^ b r * X ^ r) • d r) -
      ∑ r ∈ Finset.Ico 1 M, (B.lc ^ b r * X ^ r) • d r) - B.lc ^ K • z ∈ sm (X ^ M) (L.N c)

def Lat.FrobeniusMapsXPow (L : Lat B n V) (M : ℕ) : Prop :=
  ∀ i, ∀ v ∈ sm (X ^ M) (L.N (i - 1)), L.φ i v ∈ sm (X ^ M * B.q) (L.N i)

end lat2

def E3itOf : Prop :=
  ∀ (O : Type) [CommRing O] (B : Base O), B.E3 → ∀ j, B.E3it j

def LevelFactorMemSpanOf : Prop :=
  ∀ (O : Type) [CommRing O] (B : Base O), 1 ≤ B.ℓ → B.E3 → ∀ s, B.E2 s

def BaseGoodOf : Prop :=
  ∀ (O : Type) [CommRing O] (B : Base O) (j M g : ℕ), B.E3 → B.E4 → 3 * g ≤ (B.ℓ - 1) * M →
    B.Good j M g

def ExistsGammaXUnitShape : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O) (B : Base O),
    Irreducible ϖ → ϖ ∣ (B.ℓ : O) → B.ℓ.Prime → 3 ≤ B.ℓ → B.E4 → ∃ u₁ : O, B.GammaXUnitShape u₁

def SatAOf : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O) (B : Base O)
    (j M g : ℕ), Irreducible ϖ → ϖ ∣ (B.ℓ : O) → (B.ℓ : O) ≠ 0 → B.E3 → B.Sat (B.ff j M g)

def TruncOf : Prop :=
  ∀ (O : Type) [CommRing O] (B : Base O) (j M g sig : ℕ), 3 ≤ B.ℓ → 1 ≤ j → B.E3 →
    SigOK B.ℓ j M g sig → B.Trunc j M g sig

def TruncSpanLe : Prop :=
  ∀ (O : Type) [CommRing O] (B : Base O) (n : ℕ) [NeZero n] (j M g G : ℕ)
    (V : Type) [AddCommGroup V] [Module (PowerSeries O) V] (L : Lat B n V) (c : ZMod n),
    G ≤ 3 * g → (∀ k : ℕ, 1 ≤ k → k ≤ j → L.P5M (c + (k : ZMod n)) G) →
    sm (B.ff j M g) (L.pull c j) ≤ sm (X ^ M) (L.N (c + (j : ZMod n)))

def FrobeniusMapsXPowOf : Prop :=
  ∀ (O : Type) [CommRing O] (B : Base O) (n : ℕ) [NeZero n] (M : ℕ)
    (V : Type) [AddCommGroup V] [Module (PowerSeries O) V] (L : Lat B n V) (Mi : ZMod n → ℕ),
    B.E3 → (∀ i, L.P5M i (Mi i)) → (∀ i, Mi i < (B.ℓ - 1) * M) →
    L.FrobeniusMapsXPow M ∧ ∀ i, ∀ v ∈ sm (X ^ M) (L.N (i - 1)), L.φ i v ∈ sm (X ^ M) (L.N i)

def FrobeniusDiffBijective : Prop :=
  ∀ (O : Type) [CommRing O] (B : Base O) (n : ℕ) [NeZero n] (M : ℕ)
    (V : Type) [AddCommGroup V] [Module (PowerSeries O) V] (L : Lat B n V),
    B.E3 → L.FrobeniusMapsXPow M → L.Complete → L.XReg →
    ∀ t : ZMod n → V, (∀ i, t i ∈ sm (X ^ M) (L.N i)) →
      ∃! z : ZMod n → V, (∀ i, z i ∈ sm (X ^ M) (L.N i)) ∧ L.dφ z = t

def CompleteOf : Prop :=
  ∀ (O : Type) [CommRing O] (B : Base O) (n : ℕ) [NeZero n]
    (V : Type) [AddCommGroup V] [Module (PowerSeries O) V] (L : Lat B n V),
    IsAdicComplete (Ideal.span {(B.ℓ : O)}) O → (∀ i, L.Free i) → L.Complete

def XRegOf : Prop :=
  ∀ (O : Type) [CommRing O] (B : Base O) (n : ℕ) [NeZero n]
    (V : Type) [AddCommGroup V] [Module (PowerSeries O) V] (L : Lat B n V),
    (∀ i, L.Free i) → L.XReg

def SatOf : Prop :=
  ∀ (O : Type) [CommRing O] (B : Base O) (n : ℕ) [NeZero n] (j : ℕ) (f : PowerSeries O)
    (V : Type) [AddCommGroup V] [Module (PowerSeries O) V] (L : Lat B n V) (c : ZMod n),
    B.Sat f → L.PullFree c j →
    ∀ (K : ℕ), ∀ v ∈ L.pull c j, B.lc ^ K • v ∈ sm f (L.pull c j) → v ∈ sm f (L.pull c j)

def GamInjOf : Prop :=
  ∀ (O : Type) [CommRing O] (B : Base O) (u₁ : O) (n : ℕ) [NeZero n] (M : ℕ)
    (V : Type) [AddCommGroup V] [Module (PowerSeries O) V] (L : Lat B n V) (c : ZMod n),
    B.GammaXUnitShape u₁ → L.P9 → ∀ v ∈ sm X (L.N c), L.γ c v - v ∈ sm (X ^ M) (L.N c) →
      ∃ K : ℕ, B.lc ^ K • v ∈ sm (X ^ M) (L.N c)

def HOf : Prop :=
  ∀ (O : Type) [CommRing O] (B : Base O) (u₁ : O) (n : ℕ) [NeZero n] (M : ℕ)
    (V : Type) [AddCommGroup V] [Module (PowerSeries O) V] (L : Lat B n V) (c : ZMod n),
    B.ℓ.Prime → B.GammaXUnitShape u₁ → L.P9 → L.H c M

def ExistsTransport : Prop :=
  ∀ (O : Type) [CommRing O] (B : Base O) (n : ℕ) [NeZero n] (j M g sig : ℕ)
    (V : Type) [AddCommGroup V] [Module (PowerSeries O) V] (L : Lat B n V) (c : ZMod n),
    B.Trunc j M g sig → L.H c M → ∀ z ∈ sm X (L.N c), ∃ τ, L.IsTr c j M g sig z τ

def LatticeLeArcSpan : Prop :=
  ∀ (O : Type) [CommRing O] (B : Base O) (n : ℕ) [NeZero n]
    (V : Type) [AddCommGroup V] [Module (PowerSeries O) V] (L : Lat B n V) (c : ZMod n)
    (ell : ℕ) (hh H : ℕ → ℕ), (∀ s < ell, L.FrobeniusCobounded (c - (s : ZMod n)) (hh s)) →
    (∀ s < ell, hh s ≤ H s) →
    L.N c ≤ dv (∏ s ∈ Finset.range ell, B.p s ^ H s) (L.pull (c - (ell : ZMod n)) ell)

def ExtCOf : Prop :=
  ∀ (O : Type) [CommRing O] (B : Base O) (n : ℕ) [NeZero n]
    (V₂ V₀ : Type) [AddCommGroup V₂] [Module (PowerSeries O) V₂] [AddCommGroup V₀]
    [Module (PowerSeries O) V₀] (L₂ : Lat B n V₂) (L₀ : Lat B n V₀) (Y : Ext L₂ L₀),
    Y.P6 → L₀.XReg → ∀ i (k : ℕ) (u : V₂), Y.ι.f u ∈ sm (X ^ k) (Y.LY.N i) →
      u ∈ sm (X ^ k) (L₂.N i)

def ExtGOf : Prop :=
  ∀ (O : Type) [CommRing O] (B : Base O) (n : ℕ) [NeZero n]
    (V₂ V₀ : Type) [AddCommGroup V₂] [Module (PowerSeries O) V₂] [AddCommGroup V₀]
    [Module (PowerSeries O) V₀] (L₂ : Lat B n V₂) (L₀ : Lat B n V₀) (Y : Ext L₂ L₀)
    (i : ZMod n) (k : ℕ) (lam : PowerSeries O), Y.P6 → L₀.PhiFree i k →
    ∀ u : V₂, Y.ι.f u ∈ dv lam (Y.LY.pull i k) → u ∈ dv lam (L₂.pull i k)

def LatGoodOf : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O) (B : Base O)
    (u₁ : O) (n : ℕ) [NeZero n] (Cu : Cuts n) (j M g G sig : ℕ) (Mi : ZMod n → ℕ)
    (V : Type) [AddCommGroup V] [Module (PowerSeries O) V] (L : Lat B n V),
    Irreducible ϖ → ϖ ∣ (B.ℓ : O) → (B.ℓ : O) ≠ 0 → B.ℓ.Prime → 3 ≤ B.ℓ → 1 ≤ j →
    B.E3 → B.GammaXUnitShape u₁ → G ≤ g → SigOK B.ℓ j M g sig →
    L.P9 → (∀ i, L.P5M i (Mi i)) → (∀ i, Mi i < (B.ℓ - 1) * M) →
    (∀ c ∈ Cu.cuts, ∀ k : ℕ, 1 ≤ k → k ≤ j → Mi (c + (k : ZMod n)) ≤ G) →
    (∀ c ∈ Cu.cuts, L.PullFree c j) → L.Complete → L.XReg → L.LTors →
    L.Good Cu j M g sig

def LatGoodPrim : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O) (B : Base O)
    (n : ℕ) [NeZero n] (Cu : Cuts n) (j M g G sig : ℕ) (Mi : ZMod n → ℕ)
    (V : Type) [AddCommGroup V] [Module (PowerSeries O) V] (L : Lat B n V),
    Irreducible ϖ → ϖ ∣ (B.ℓ : O) → (B.ℓ : O) ≠ 0 → B.ℓ.Prime → 3 ≤ B.ℓ → 1 ≤ j →
    IsAdicComplete (Ideal.span {(B.ℓ : O)}) O →
    B.E3 → B.E4 → G ≤ g → SigOK B.ℓ j M g sig →
    L.P9 → (∀ i, L.P5M i (Mi i)) → (∀ i, Mi i < (B.ℓ - 1) * M) →
    (∀ c ∈ Cu.cuts, ∀ k : ℕ, 1 ≤ k → k ≤ j → Mi (c + (k : ZMod n)) ≤ G) →
    (∀ c ∈ Cu.cuts, L.PullFree c j) → (∀ i, L.Free i) → L.LTors →
    L.Good Cu j M g sig

def ExtGoodOf : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O) (B : Base O)
    (n : ℕ) [NeZero n] (Cu : Cuts n) (j M g G rr : ℕ) (Mi hi : ZMod n → ℕ)
    (H : ZMod n → ℕ → ℕ)
    (V₂ V₀ : Type) [AddCommGroup V₂] [Module (PowerSeries O) V₂] [AddCommGroup V₀]
    [Module (PowerSeries O) V₀] (L₂ : Lat B n V₂) (L₀ : Lat B n V₀) (e₀ : V₀) (Y : Ext L₂ L₀),
    Irreducible ϖ → ϖ ∣ (B.ℓ : O) → (B.ℓ : O) ≠ 0 → B.E3 → G ≤ g →
    (∀ c ∈ Cu.cuts, Y.Lift e₀ c rr) → Y.LY.P9 → Y.P6 → L₀.XReg →
    (∀ i, Y.LY.P5M i (Mi i)) → (∀ i, Y.LY.FrobeniusCobounded i (hi i)) →
    (∀ c ∈ Cu.cuts, ∀ k : ℕ, 1 ≤ k → k ≤ j → Mi (c + (k : ZMod n)) ≤ G) →
    (∀ c ∈ Cu.cuts, ∀ s < Cu.ell c, hi (c - (s : ZMod n)) ≤ H c s) →
    (∀ c ∈ Cu.cuts, Y.LY.PullFree c j) →
    (∀ c ∈ Cu.cuts, L₀.PhiFree (c - (Cu.ell c : ZMod n)) (Cu.ell c)) →
    Y.Good e₀ Cu (fun c => ∏ s ∈ Finset.range (Cu.ell c), B.p s ^ H c s) j M g rr

end Formalism.ExponentWindows.E
