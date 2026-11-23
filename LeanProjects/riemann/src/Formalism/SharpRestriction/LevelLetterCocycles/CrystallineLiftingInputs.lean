import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LiftingTheory
import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices
import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
import Formalism.SharpRestriction.LevelLetterCocycles.HerrCohomologyExtensions

noncomputable section

namespace Formalism.MainNotions.CrystallineLiftingInputs

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct

def sig2 (l H : ℕ) : ℝ := 2 * (H : ℝ) / ((l : ℝ) - 1) ^ 2 + 1

def Mpar (l h : ℕ) : ℕ := h / (l - 1) + 1

section Core

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

def DL (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (i : ZMod n) (x : W.DD T) : Prop :=
  (letE i : LetA O n) • x = x ∧ ∀ δ ∈ W.DelF, W.γD T δ x = x

def InPN (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (k : ℕ) (x : W.DD T) : Prop :=
  ∃ y ∈ W.N T, (∀ δ ∈ W.DelF, W.γD T δ y = y) ∧ x = W.π₀ ^ k • y

def PolesFin (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (x : W.DD T) : Prop :=
  ∃ k : ℕ, W.InvN T (∏ j ∈ Finset.range k, Formalism.MainNotions.LiftingTheory.pk W j) x

def Dlat (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (i : ZMod n) : Set (T.V ⊗[Qp] B) :=
  {z | ∃ (x : W.DD T) (hx : x ∈ W.N T), DL W T i x ∧ z = W.cmp T ⟨x, hx⟩}

def DlatImg (W : LocWach PD LL O v n) {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L)
    (i : ZMod n) : Set (T₂.V ⊗[Qp] B) :=
  {z | ∃ (x : W.DD T₁) (_ : x ∈ W.N T₁) (hx' : W.map F x ∈ W.N T₂), DL W T₁ i x ∧ z = W.cmp T₂ ⟨W.map F x, hx'⟩}

def RankFC [NeZero n] (W : LocWach PD LL O v n) : Prop :=
  ∀ (d : ℕ) (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b : ZMod n → ℕ) (S η m : ℕ),
    Formalism.MainNotions.RamifiedCoefficientChains.SetCS W d T₁ T₂ F b S η m → ∀ i : ZMod n,
      ((i.val + d) % 2 = 0 →
        finrank LL ↥(FilCris PD T₂.ρ (-(η : ℤ)) ⊓ DcrisL PD T₂.ρ (W.emb i)) ≤ m) ∧
      ((i.val + d) % 2 = 1 →
        (finrank LL ↥(DcrisL PD T₂.ρ (W.emb i)) : ℤ) -
          finrank LL ↥(FilCris PD T₂.ρ (b i : ℤ) ⊓ DcrisL PD T₂.ρ (W.emb i)) ≤ m)

def QTool [NeZero n] (W : LocWach PD LL O v n) : Prop :=
  ∀ (d : ℕ) (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b : ZMod n → ℕ) (S η m : ℕ)
    (Mi hi : ZMod n → ℕ),
    Formalism.MainNotions.RamifiedCoefficientChains.SetCS W d T₁ T₂ F b S η m → Formalism.MainNotions.LiftingTheory.JumpsLet W T₁ Mi hi →
    (∀ i : ZMod n,
      Formalism.MainNotions.LiftingTheory.Kills W F i (W.π₀ ^ (Formalism.MainNotions.LiftingTheory.Hmax n Mi hi / (PD.p - 1) + 1)) ∧
      Formalism.MainNotions.LiftingTheory.Kills W F i (Formalism.MainNotions.LiftingTheory.lp W (Formalism.MainNotions.LiftingTheory.eWA PD.p (Formalism.MainNotions.LiftingTheory.Hmax n Mi hi))) ∧
      Formalism.MainNotions.LiftingTheory.Kills W F i
        (Formalism.MainNotions.LiftingTheory.qp W ^ ⌈Formalism.MainNotions.RamifiedCoefficientChains.aR PD.p (Formalism.MainNotions.RamifiedCoefficientChains.hpar n b S + η)⌉₊)) ∧
    ∀ (Y : LocLat G Qp LL O) (ι : LatHom T₂.L Y.L) (π : LatHom Y.L W.one.L),
      IsSESLat (G := G) (Qp := Qp) (LL := LL) (O := O) ι π → IsCrys PD Y.ρ →
      ∀ i : ZMod n,
        Formalism.MainNotions.LiftingTheory.Kills W π i (W.π₀ ^ (Formalism.MainNotions.LiftingTheory.Hmax n Mi hi / (PD.p - 1) + 1)) ∧
        Formalism.MainNotions.LiftingTheory.Kills W π i (Formalism.MainNotions.LiftingTheory.lp W (Formalism.MainNotions.LiftingTheory.eWA PD.p (Formalism.MainNotions.LiftingTheory.Hmax n Mi hi))) ∧
        Formalism.MainNotions.LiftingTheory.Kills W π i
          (Formalism.MainNotions.LiftingTheory.qp W ^ ⌈Formalism.MainNotions.RamifiedCoefficientChains.aR PD.p (Formalism.MainNotions.RamifiedCoefficientChains.hpar n b S + η)⌉₊)

def dOp (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (x : W.DD T) : W.DD T :=
  Ring.inverse (algebraMap (LetA O n) W.EE W.π₀) • (W.γ T x - x)

def InQN (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (i : ZMod n) (k : ℤ) (x : W.DD T) : Prop :=
  DL W T i x ∧
    (if 0 ≤ k then Formalism.MainNotions.LiftingTheory.qp W ^ k.toNat • x ∈ W.N T else
      ∃ y ∈ W.N T, x = Formalism.MainNotions.LiftingTheory.qp W ^ (-k).toNat • y)

def cR (W : LocWach PD LL O v n) (j : ℤ) : LL :=
  (algebraMap O LL (((W.χΓ W.gam) ^ (-j) : Oˣ) : O) - 1) / (-(PD.p : LL))

def dShift (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (j : ℤ) (x : W.DD T) : W.DD T :=
  -(((PD.p : ℕ) : O) • dOp W T x) - ((((W.χΓ W.gam) ^ (-j) : Oˣ) : O) - 1) • x

def dProd (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) : List ℤ → W.DD T → W.DD T
  | [] => id
  | j :: js => dShift W T j ∘ dProd W T js

def rootsR (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (i : ZMod n) (y y' : ℤ) (Bd : ℕ) :
    Finset ℤ := by
  classical
  exact (Finset.Icc (y' + 1 - Bd) (y + Bd)).filter fun z =>
    ∃ u : ℤ, (∃ τ, Formalism.MainNotions.LiftingTheory.Over W τ i ∧ IsJumpV PD T.ρ τ u) ∧ y' < z - u ∧ z - u ≤ y

def RTool [NeZero n] (W : LocWach PD LL O v n) : Prop :=
  Formalism.MainNotions.LiftingTheory.CaseA W →
    (cR W 0 = 0 ∧ ∀ j j' : ℤ, j ≠ j' →
      v (cR W j - cR W j') = ((padicValInt PD.p (j - j') : ℚ) : WithTop ℚ)) ∧
    ∀ (T : LocLat G Qp LL O), IsCrys PD T.ρ →
    ∀ (i : ZMod n) (y y' : ℤ) (Bd : ℕ), y' < y →
      (∀ τ, Formalism.MainNotions.LiftingTheory.Over W τ i → JumpsInV PD T.ρ τ (Set.Icc (-(Bd : ℤ)) Bd)) →
      (∀ x, InQN W T i y x → InQN W T i y (dOp W T x)) ∧
      (∀ x, InQN W T i y' x → InQN W T i y' (dOp W T x)) ∧
      (∀ x, InQN W T i y x → InQN W T i y' (((PD.p : ℕ) : O) • x) → InQN W T i y' x) ∧
      ∃ k : ℕ, ∀ x, InQN W T i y x →
        InQN W T i y' (((PD.p : ℕ) : O) ^ k •
          dProd W T ((rootsR W T i y y' Bd).sort (· ≤ ·)) x)

def RMult [NeZero n] (W : LocWach PD LL O v n) : Prop :=
  Formalism.MainNotions.LiftingTheory.CaseA W → ∀ (T : LocLat G Qp LL O), IsCrys PD T.ρ →
    ∀ (i : ZMod n) (τ : K →ₐ[Qp] LL), Formalism.MainNotions.LiftingTheory.Over W τ i → ∀ (y y' x : ℤ), y' < y →
    ∀ k : ℕ, ∑ j ∈ Finset.Ioc y' y, multV PD T.ρ τ (x - j) < (k : ℤ) →
    ∀ w : Fin k → W.DD T,
      (∀ a, InQN W T i y (w a) ∧ InQN W T i y' (dShift W T x (w a))) →
      ∃ c : Fin k → O, c ≠ 0 ∧ InQN W T i y' (∑ a, c a • w a)

def eY (l y : ℕ) : ℕ := ⌈(y : ℝ) * l / ((l : ℝ) - 1)⌉₊

def InI (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (i : ZMod n) (w : W.DD T) : Prop :=
  DL W T i w ∧ PolesFin W T w ∧ InPN W T 1 (W.γ T w - w)

def IsSer (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (i : ZMod n) (w : W.DD T)
    (c : ℕ → W.DD T) : Prop :=
  c 0 = 0 ∧ (∀ y, DL W T i (c y) ∧ c y ∈ W.N T) ∧
    ∀ K : ℕ, ∃ j : ℕ, InPN W T K (((PD.p : ℕ) : O) ^ j •
      (((PD.p : ℕ) : O) ^ eY PD.p K • (W.γ T w - w) -
        ∑ y ∈ Finset.range K, ((PD.p : ℕ) : O) ^ (eY PD.p K - eY PD.p y) •
          (W.γ T (W.π₀ ^ y • c y) - W.π₀ ^ y • c y)))

def TTool1 [NeZero n] (W : LocWach PD LL O v n) : Prop :=
  Formalism.MainNotions.LiftingTheory.CaseA W → ∀ (T : LocLat G Qp LL O), IsCrys PD T.ρ → ∀ (i : ZMod n) (w : W.DD T),
    InI W T i w →
    (∃ c, IsSer W T i w c) ∧ ∀ c c', IsSer W T i w c → IsSer W T i w c' → ∀ K : ℕ, ∃ j : ℕ,
      InPN W T K (((PD.p : ℕ) : O) ^ j • ∑ y ∈ Finset.range K,
        ((PD.p : ℕ) : O) ^ (eY PD.p K - eY PD.p y) • (W.π₀ ^ y • (c y - c' y)))

def fMX (W : LocWach PD LL O v n) (M X : ℕ) : LetA O n := W.π₀ ^ M * Formalism.MainNotions.LiftingTheory.qp W ^ X

def IsRem (W : LocWach PD LL O v n) (j M X y : ℕ) (r : LetA O n) : Prop :=
  (∃ a : ℕ → O, r = ∑ k ∈ Finset.range (M + X), algebraMap O (LetA O n) (a k) * W.π₀ ^ k) ∧
    ∃ g : LetA O n, ((W.φA ^ j) W.π₀) ^ y - r = fMX W M X * g

def pullJ (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (i : ZMod n) (j : ℕ) :
    Submodule (LetA O n) (W.DD T) :=
  Submodule.span (LetA O n) (((W.φD T) ^ j) '' {x | x ∈ W.N T ∧ DL W T i x})

def IsTrunc (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (i : ZMod n) (j M X σ : ℕ)
    (w z : W.DD T) : Prop :=
  ∃ (c : ℕ → W.DD T) (r s : ℕ → LetA O n), IsSer W T i w c ∧
    (∀ y, IsRem W j M X y (r y) ∧
      ((PD.p : ℕ) : LetA O n) ^ eY PD.p y * s y = ((PD.p : ℕ) : LetA O n) ^ σ * r y) ∧
    z = ((PD.p : ℕ) : O) ^ σ • ((W.φD T) ^ j) w -
      ∑ y ∈ Finset.range (max M X + 1), s y • ((W.φD T) ^ j) (c y)

def TCase (l j M X σ : ℕ) : Prop :=
  (j = 1 ∧ 1 ≤ M ∧ σ = ⌈((M : ℝ) + X) / ((l : ℝ) - 1) + 1⌉₊) ∨
    (j = 2 ∧ M = 1 ∧ σ = ⌈(X : ℝ) / ((l : ℝ) - 1) ^ 2 + 1⌉₊)

def TTool2 [NeZero n] (W : LocWach PD LL O v n) : Prop :=
  Formalism.MainNotions.LiftingTheory.CaseA W → 11 ≤ PD.p → ∀ (j M X σ : ℕ), TCase PD.p j M X σ →
  (∀ (T : LocLat G Qp LL O), IsCrys PD T.ρ → ∀ (i : ZMod n),
    (∀ w, InI W T i w → ∃ z, IsTrunc W T i j M X σ w z) ∧
    (∀ w z, InI W T i w → IsTrunc W T i j M X σ w z →
      z - ((PD.p : ℕ) : O) ^ σ • ((W.φD T) ^ j) w ∈ pullJ W T i j ∧
      ∃ p ∈ pullJ W T i j, W.γ T z - z = fMX W M X • p) ∧
    (∀ w z z', InI W T i w → IsTrunc W T i j M X σ w z → IsTrunc W T i j M X σ w z' →
      ∃ p ∈ pullJ W T i j, z - z' = fMX W M X • p) ∧
    (∀ (a a' : O) w w' z z' z'', InI W T i w → InI W T i w' → IsTrunc W T i j M X σ w z →
      IsTrunc W T i j M X σ w' z' → IsTrunc W T i j M X σ (a • w + a' • w') z'' →
      ∃ p ∈ pullJ W T i j, z'' - (a • z + a' • z') = fMX W M X • p) ∧
    (∀ w z, InI W T i w → InPN W T 1 w → IsTrunc W T i j M X σ w z →
      ∃ p ∈ pullJ W T i j, z = fMX W M X • p) ∧
    (∀ p ∈ pullJ W T i j, ∃ p' ∈ pullJ W T i j,
      ((PD.p : ℕ) : O) ^ (2 * σ) • p - fMX W M X • p' ∈ Submodule.span (LetA O n)
        {z | ∃ w, w ∈ W.N T ∧ InI W T i w ∧ IsTrunc W T i j M X σ w z})) ∧
  ∀ (T T' : LocLat G Qp LL O) (F : LatHom T.L T'.L), IsCrys PD T.ρ → IsCrys PD T'.ρ →
    ∀ (i : ZMod n) w z z', InI W T i w → IsTrunc W T i j M X σ w z →
      IsTrunc W T' i j M X σ (W.map F w) z' →
      ∃ p ∈ pullJ W T' i j, W.map F z - z' = fMX W M X • p

def THor [NeZero n] (W : LocWach PD LL O v n) : Prop :=
  Formalism.MainNotions.LiftingTheory.CaseA W → 11 ≤ PD.p → ∀ (j M X σ : ℕ), TCase PD.p j M X σ →
  ∀ (T : LocLat G Qp LL O), IsCrys PD T.ρ → ∀ (i : ZMod n) (w z : W.DD T) (hw : w ∈ W.N T),
    InI W T i w → IsTrunc W T i j M X σ w z →
    ∀ (ζ : LL) (R k : ℕ) (a : LetA O n) (hk : (Formalism.MainNotions.LiftingTheory.qp W ^ k * a) • z ∈ W.N T),
      ((IsPrimitiveRoot ζ PD.p ∧ R = k + X) ∨ (ζ = 1 ∧ R = (PD.p - 1) * M)) →
      (∀ r : ℤ, r < 0 → W.levN T (i + (j : ZMod n)) ζ ⟨_, hk⟩ r = 0) ∧
      ∀ r : ℕ, r < R → W.levN T (i + (j : ZMod n)) ζ ⟨_, hk⟩ (r : ℤ) =
        PowerSeries.coeff r (W.lev (i + (j : ZMod n)) ζ (Formalism.MainNotions.LiftingTheory.qp W ^ k * a)) •
          ((PD.p : LL) ^ σ • ιV PD (LL := LL) (V := T.V)
            ((φVB PD (LL := LL) (V := T.V))^[j] (W.cmp T ⟨w, hw⟩)))

def FTool [NeZero n] (W : LocWach PD LL O v n) : Prop :=
  ∀ (d : ℕ) (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b : ZMod n → ℕ) (S η m : ℕ),
    Formalism.MainNotions.RamifiedCoefficientChains.SetCS W d T₁ T₂ F b S η m →
    ∀ (T : LocLat G Qp LL O), IsCrys PD T.ρ →
      (∀ i τ, Formalism.MainNotions.LiftingTheory.Over W τ i →
        JumpsInV PD T.ρ τ (Set.Ici (-((Formalism.MainNotions.RamifiedCoefficientChains.hpar n b S : ℕ) : ℤ)))) →
      (∀ (c : ZMod n) τ, (c.val + d) % 2 = 0 → Formalism.MainNotions.LiftingTheory.Over W τ (c + 1) →
        JumpsInV PD T.ρ τ (Set.Ici (-(η : ℤ)))) →
      let M := Mpar PD.p (Formalism.MainNotions.RamifiedCoefficientChains.hpar n b S)
      (∀ (i : ZMod n) (x : W.DD T), x ∈ W.N T → DL W T (i - 1) x →
        ∃ y ∈ W.N T, W.φD T (W.π₀ ^ M • x) = (W.π₀ ^ M * Formalism.MainNotions.LiftingTheory.qp W) • y) ∧
      (∀ w, InPN W T M w → ∃! z, InPN W T M z ∧ W.φD T z - z = w) ∧
      (∀ (i : ZMod n) (x : W.wachCocyclesDelta T), DL W T i (x : W.DD T × W.DD T).1 →
        InPN W T M (x : W.DD T × W.DD T).2 →
          (InPN W T M (x : W.DD T × W.DD T).1 → W.clK T x = 0) ∧
          (PolesFin W T (x : W.DD T × W.DD T).1 → W.clK T x ∈ latticeFiniteCohomology PD T.L)) ∧
      (∀ (c : ZMod n) (x : W.DD T), (c.val + d) % 2 = 0 → x ∈ W.φpull T →
        (letE (c + 1) : LetA O n) • x = x → Formalism.MainNotions.LiftingTheory.qp W ^ η • x ∈ W.N T) ∧
      (∀ (c : ZMod n) (w z : W.DD T), (c.val + d) % 2 = 0 → InI W T c w →
        IsTrunc W T c 1 M η ⌈((M : ℝ) + η) / ((PD.p : ℝ) - 1) + 1⌉₊ w z →
        (∃ x : W.wachCocyclesDelta T, (x : W.DD T × W.DD T).1 = z ∧ InPN W T M (x : W.DD T × W.DD T).2) ∧
        (InPN W T 1 w → ∀ x : W.wachCocyclesDelta T, (x : W.DD T × W.DD T).1 = z →
          InPN W T M (x : W.DD T × W.DD T).2 → W.clK T x = 0))

def LemmaG [NeZero n] (W : LocWach PD LL O v n) : Prop :=
  ∀ (d : ℕ) (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b : ZMod n → ℕ) (S η m : ℕ),
    Formalism.MainNotions.RamifiedCoefficientChains.SetCS W d T₁ T₂ F b S η m → ∀ i : ZMod n, (i.val + d) % 2 = 1 →
    let H := Formalism.MainNotions.RamifiedCoefficientChains.hpar n b S + η
    ∃ E : ℕ, (E : ℝ) ≤ (3 * Formalism.MainNotions.RamifiedCoefficientChains.aR PD.p H + S + 2 * η) / ((PD.p : ℝ) - 1) +
        3 * Formalism.MainNotions.RamifiedCoefficientChains.lam PD.p H ∧
      ∀ x ∈ (fun z => φVB PD (LL := LL) (V := T₂.V) (φVB PD (LL := LL) (V := T₂.V) z)) ''
          Dlat W T₂ (i - 2),
        x ∈ FilCris PD T₂.ρ (b i : ℤ) →
        ((PD.p : LL) ^ (⌈(E : ℝ) + sig2 PD.p H + ((b (i - 1) + S : ℕ) : ℝ) - (b i : ℝ)⌉ : ℤ)) • x ∈
          DlatImg W F i

end Core

section Lit

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    (LL O : Type) [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]

def FonDim : Prop :=
  ∀ T : LocLat G Qp LL O,
    (Module.Finite LL ↥(Dcris PD T.ρ) ∧
      finrank LL ↥(Dcris PD T.ρ) ≤ finrank Qp K₀ * finrank LL T.V) ∧
    ∀ τ : K →ₐ[Qp] LL, Module.Finite LL ↥(DdRE PD T.ρ τ) ∧
      finrank LL ↥(DdRE PD T.ρ τ) ≤ finrank LL T.V

def FonStrict : Prop :=
  (∀ (T₀ T₁ T₂ : LocLat G Qp LL O) (ι : LatHom T₀.L T₁.L) (π : LatHom T₁.L T₂.L),
    IsSESLat (Qp := Qp) ι π → IsCrys PD T₁.ρ →
    IsCrys PD T₀.ρ ∧ IsCrys PD T₂.ρ ∧
      ∀ (τ : K →ₐ[Qp] LL) (a : ℤ),
        multV PD T₁.ρ τ a = multV PD T₀.ρ τ a + multV PD T₂.ρ τ a) ∧
  ∀ (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L), Function.Surjective F.f →
    IsCrys PD T₁.ρ →
    IsCrys PD T₂.ρ ∧ ∀ (τ : K →ₐ[Qp] LL) (a : ℤ), multV PD T₂.ρ τ a ≤ multV PD T₁.ρ τ a

def FonCmp : Prop :=
  Function.Bijective (algebraMap K₀ K) → ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ →
    (Dcris PD T.ρ).map (ιV PD (LL := LL) (V := T.V)) = DdR PD T.ρ ∧
    ∀ τ : K →ₐ[Qp] LL, finrank LL ↥(DdRE PD T.ρ τ) = finrank LL T.V ∧
      ∀ a : ℤ, FildR PD T.ρ τ a =
        (FilCris PD T.ρ a ⊓ DcrisL PD T.ρ (τ.comp (IsScalarTower.toAlgHom Qp K₀ K))).map
          (ιV PD (LL := LL) (V := T.V))

end Lit

def TToolAlg : Prop :=
  (∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (l : ℕ) [Fact l.Prime]
    (ϖ : O) (e : ℕ), Irreducible ϖ → 1 ≤ e → Associated (l : O) (ϖ ^ e) →
    ∀ (u₁ u₂ u ε : PowerSeries O), IsUnit u₁ → IsUnit u₂ → IsUnit u → IsUnit ε →
    ∀ (y X M η t : ℕ),
      ((t : ℝ) ≤ e * max 0 ((l : ℝ) * y - X) →
        (u₁ * PowerSeries.X * (PowerSeries.X + PowerSeries.C (l : O)) ^ (l - 1)) ^ y ∈
          Ideal.span {PowerSeries.C (ϖ ^ t),
            PowerSeries.X * (PowerSeries.X + PowerSeries.C (l : O)) ^ X}) ∧
      ((t : ℝ) ≤ e * max 0 ((l : ℝ) * y - η - M) →
        (u₁ * PowerSeries.X * (PowerSeries.X + PowerSeries.C (l : O)) ^ (l - 1)) ^ y ∈
          Ideal.span {PowerSeries.C (ϖ ^ t),
            PowerSeries.X ^ M * (PowerSeries.X + PowerSeries.C (l : O)) ^ η}) ∧
      ((t : ℝ) ≤ e * max 0 (((l : ℝ) - 1) * y - (X : ℝ) / l) →
        (u₂ * PowerSeries.X * (PowerSeries.X + PowerSeries.C (l : O)) ^ (l - 1) *
            (u * (PowerSeries.X + PowerSeries.C (l : O)) ^ l + PowerSeries.C (l : O) * ε) ^ (l - 1))
            ^ y ∈
          Ideal.span {PowerSeries.C (ϖ ^ t),
            PowerSeries.X * (PowerSeries.X + PowerSeries.C (l : O)) ^ X})) ∧
  ∀ (l y X M η : ℕ), 11 ≤ l →
    (y : ℝ) * l / ((l : ℝ) - 1) - max 0 ((l : ℝ) * y - X) ≤ ((X : ℝ) + 1) / ((l : ℝ) - 1) + 1 ∧
    (y : ℝ) * l / ((l : ℝ) - 1) - max 0 ((l : ℝ) * y - η - M) ≤
      ((M : ℝ) + η) / ((l : ℝ) - 1) + 1 ∧
    (y : ℝ) * l / ((l : ℝ) - 1) - max 0 (((l : ℝ) - 1) * y - (X : ℝ) / l) ≤
      (X : ℝ) / ((l : ℝ) - 1) ^ 2 + 1

def PowerSeriesDVRFactorisation : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (l : ℕ) [Fact l.Prime]
    (ϖ : O) (e : ℕ), Irreducible ϖ → 1 ≤ e → Associated (l : O) (ϖ ^ e) →
    ∀ (ε u : PowerSeries O), IsUnit ε → IsUnit u →
    ∀ (b y t : ℕ), 1 ≤ b → (b : ℝ) / (l : ℝ) ≤ (y : ℝ) →
      (PowerSeries.C (l : O) * ε + u * PowerSeries.X ^ l) ^ y ∈
        Ideal.span {PowerSeries.C (ϖ ^ t), (PowerSeries.X : PowerSeries O) ^ b} →
      (t : ℝ) / (e : ℝ) ≤ (y : ℝ) - (b : ℝ) / (l : ℝ) + 2 + Real.logb (l : ℝ) (y : ℝ)

def TheoremCPositiveDegree (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (k₁ k₂ k₃ k₄ k₅ C : ℝ) : Prop :=
  Formalism.MainNotions.RamifiedCoefficientChains.TheoremCConstantsRange D HW F (fun m => 1 ≤ m) k₁ k₂ k₃ k₄ k₅ C

def aux₃ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C : ℝ) : Prop := TheoremCPositiveDegree D HW F 32 4 10 4 (3 / 2) C

def adm1 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) : Prop := Formalism.MainNotions.DeltaInvariantLattices.thm1 D HW F Cm

def adm2 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.DeltaInvariantLattices.cons D HW F

def adm3 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.DeltaInvariantLattices.prop2 D HW F

def ArchimedeanSignatureMatching (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.DeltaInvariantLattices.lem3 D HW F

def adm5 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.LiftingTheory.ConclusionL D HW F

def adm6 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.LiftingTheory.ConclusionW D HW F

def adm7 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C : ℝ) : Prop := Formalism.MainNotions.LiftingTheory.WachAnnihilatorAll D HW F ∧ Formalism.MainNotions.LiftingTheory.WachResultConstant D HW F C

def adm8 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.LiftingTheory.ConclusionH D HW F

def adm9 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.LiftingTheory.ExistsUnitClasses D HW F

def adm10 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (CA CB CK : ℝ) : Prop := Formalism.MainNotions.LiftingTheory.LiftTheoremAllCases D HW F CA CB CK

def adm11 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C₀ : ℝ) : Prop := Formalism.MainNotions.RamifiedCoefficientChains.Conclusion2 D HW F C₀

def adm12 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hg : Good K 1 LL)
    [NeZero (Module.finrank ℚ_[l] ↥(K0 K))], RankFC ((HW l).W K 1 LL hg)

def adm13 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hg : Good K 1 LL)
    [NeZero (Module.finrank ℚ_[l] ↥(K0 K))], QTool ((HW l).W K 1 LL hg)

def adm14 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hg : Good K 1 LL)
    [NeZero (Module.finrank ℚ_[l] ↥(K0 K))], RTool ((HW l).W K 1 LL hg)

def adm15 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) : Prop :=
  TToolAlg ∧ ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hg : Good K 1 LL)
    [NeZero (Module.finrank ℚ_[l] ↥(K0 K))],
    TTool1 ((HW l).W K 1 LL hg) ∧ TTool2 ((HW l).W K 1 LL hg)

def adm16 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hg : Good K 1 LL)
    [NeZero (Module.finrank ℚ_[l] ↥(K0 K))], FTool ((HW l).W K 1 LL hg)

def adm17 (_D : D7) : Prop := PowerSeriesDVRFactorisation

def adm18 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hg : Good K 1 LL)
    [NeZero (Module.finrank ℚ_[l] ↥(K0 K))], LemmaG ((HW l).W K 1 LL hg)

def adm19 (D : D7) : Prop := Formalism.MainNotions.RamifiedCoefficientChains.DcrisExactStrictAll D.loc

def adm20 (D : D7) : Prop := Formalism.MainNotions.RamifiedCoefficientChains.admBK D.loc

def adm21 (D : D7) : Prop := Formalism.MainNotions.RamifiedCoefficientChains.H1fGeneratorCount D.loc

def adm22 (D : D7) : Prop := Formalism.MainNotions.RamifiedCoefficientChains.BlochKatoExtensionCriterion D.loc

def adm23 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hg : Good K 1 LL)
    [NeZero (Module.finrank ℚ_[l] ↥(K0 K))], RMult ((HW l).W K 1 LL hg)

def FrobeniusExpansionCongruence (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hg : Good K 1 LL)
    [NeZero (Module.finrank ℚ_[l] ↥(K0 K))], THor ((HW l).W K 1 LL hg)

def HerrExtensionClause (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.HerrCohomologyExtensions.adm16 D HW F

def adm26 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.HerrCohomologyExtensions.adm18 D HW F

def HerrCocycleExtensionClass (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.LiftingTheory.adm17 D HW F ∧ Formalism.MainNotions.LiftingTheory.adm18 D HW F

def FontaineFormalProperties (D : D7) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l),
    FonDim ((D.loc l).PD K) ↥LL.1 ↥(OL LL) ∧ FonStrict ((D.loc l).PD K) ↥LL.1 ↥(OL LL) ∧
      FonCmp ((D.loc l).PD K) ↥LL.1 ↥(OL LL)

def admitted (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (CR CA CB CK C₀ : ℝ) : Prop :=
  adm1 D HW F Cm ∧ adm2 D HW F ∧ adm3 D HW F ∧ ArchimedeanSignatureMatching D HW F ∧ adm5 D HW F ∧ adm6 D HW F ∧ adm7 D HW F CR ∧ adm8 D HW F ∧ adm9 D HW F ∧
    adm10 D HW F CA CB CK ∧ adm11 D HW F C₀ ∧ adm12 D HW F Cm ∧ adm13 D HW F Cm ∧ adm14 D HW F Cm ∧ adm15 D HW F Cm ∧ adm16 D HW F Cm ∧
    adm17 D ∧ adm18 D HW F Cm ∧ adm19 D ∧ adm20 D ∧ adm21 D ∧ adm22 D ∧ adm23 D HW F Cm ∧ FrobeniusExpansionCongruence D HW F Cm ∧ HerrExtensionClause D HW F ∧
    adm26 D HW F ∧ HerrCocycleExtensionClass D HW F ∧ FontaineFormalProperties D

def Stmt (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (C CR CA CB CK C₀ : ℝ) : Prop := admitted D HW F Cm CR CA CB CK C₀ → aux₃ D HW F C

def ShareAbsoluteConstant : Prop :=
  ∀ CR CA CB CK C₀ : ℝ, ∃ C : ℝ, ∀ D : D7, ∀ HW : HWOf D.loc, ∀ F : FonOf D.loc D.locA HW, ∀ Cm : CmpOf D.loc D.locA HW F, Stmt D HW F Cm C CR CA CB CK C₀

theorem theorem_c_mono_constant (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) {C C' : ℝ} (hC : C ≤ C') (h : aux₃ D HW F C) : aux₃ D HW F C' := by
  intro l _ K LL hg _ d T₁ T₂ F b S η m hS hm
  obtain ⟨e, he, h2, h3⟩ := h l K LL hg d T₁ T₂ F b S η m hS hm
  refine ⟨e, le_trans he ?_, h2, h3⟩
  unfold Formalism.MainNotions.RamifiedCoefficientChains.eBd
  have hlam : 0 ≤ Formalism.MainNotions.RamifiedCoefficientChains.lam ((D.loc l).PD K).p (Formalism.MainNotions.RamifiedCoefficientChains.hpar _ b S + η) := by
    unfold Formalism.MainNotions.RamifiedCoefficientChains.lam
    have h11 : 11 ≤ ((D.loc l).PD K).p := hS.2.1
    have h1 : (1 : ℝ) < (((D.loc l).PD K).p : ℝ) := by
      exact_mod_cast (by omega : 1 < ((D.loc l).PD K).p)
    rcases Nat.eq_zero_or_pos (Formalism.MainNotions.RamifiedCoefficientChains.hpar _ b S + η) with h0 | h0
    · rw [h0]; simp
    · have h2 : (1 : ℝ) ≤ 2 * ((Formalism.MainNotions.RamifiedCoefficientChains.hpar _ b S + η : ℕ) : ℝ) := by
        have : (1 : ℝ) ≤ ((Formalism.MainNotions.RamifiedCoefficientChains.hpar _ b S + η : ℕ) : ℝ) := by exact_mod_cast h0
        linarith
      have := Real.logb_nonneg h1 h2
      linarith
  nlinarith

end Formalism.MainNotions.CrystallineLiftingInputs
