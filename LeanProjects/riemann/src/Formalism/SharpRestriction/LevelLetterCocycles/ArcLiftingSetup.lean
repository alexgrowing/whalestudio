import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.WindowSums.Statement
import Formalism.SharpRestriction.LevelLetterCocycles.CrystallineMapLemmas
import Formalism.SharpRestriction.LevelLetterCocycles.LiftingTheory
import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices
import Formalism.SharpRestriction.LevelLetterCocycles.LocalTheoryWindows
import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains

noncomputable section

open Classical

namespace Formalism.MainNotions.ArcLiftingSetup

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module TensorProduct

section Core

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

def lA (_W : LocWach PD LL O v n) : LetA O n := ((PD.p : ℕ) : LetA O n)

def qA (W : LocWach PD LL O v n) : LetA O n := W.π₀ + lA W

def ps (W : LocWach PD LL O v n) (s : ℕ) : LetA O n := (W.φA ^ s) (qA W)

def PiPs (W : LocWach PD LL O v n) : Submonoid (LetA O n) :=
  Submonoid.closure (insert W.π₀ (Set.range (ps W)))

def Ps (W : LocWach PD LL O v n) : Submonoid (LetA O n) :=
  Submonoid.closure (Set.range (ps W))

def InFN (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (f : LetA O n) (x : W.DD T) : Prop :=
  ∃ y ∈ W.NΔ T, x = f • y

def InFNc (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (c : ZMod n) (f : LetA O n)
    (x : W.DD T) : Prop :=
  ∃ y ∈ W.NΔ T, (letE (O := O) c : LetA O n) • y = y ∧ x = f • y

def InLet (_W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (c : ZMod n) (x : _W.DD T) : Prop :=
  (letE (O := O) c : LetA O n) • x = x

def IsΔ (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (x : W.DD T) : Prop :=
  ∀ δ ∈ W.DelF, W.γD T δ x = x

def SATcore (W : LocWach PD LL O v n) : Prop :=
  Formalism.MainNotions.LiftingTheory.CaseA W →
  ∀ (T : LocLat G Qp LL O) (f f' : LetA O n), IsCrys PD T.ρ → f ∈ PiPs W → f' ∈ PiPs W → ∀ x : W.DD T,
    f' • x ∈ W.NΔ T → (∃ k : ℕ, InFN W T f (lA W ^ k • x)) → InFN W T f x

def CocΔ (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) : Submodule O (W.DD T × W.DD T) :=
  W.wachCocyclesDelta T

def Cls (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (M : ℕ) (y : W.DD T) (x : LatticeCohomology T.L) :
    Prop :=
  ∃ (z : W.DD T) (h : (y, z) ∈ CocΔ W T), InFN W T (W.π₀ ^ M) z ∧ W.clK T ⟨(y, z), h⟩ = x

def JumpsLe (PD : PeriodData G Qp K₀ K B BdR) (T : LocLat G Qp LL O) (h : ℕ) : Prop :=
  ∀ τ a, IsJumpV PD T.ρ τ a → |a| ≤ (h : ℤ)

def FirstWachFiltration (W : LocWach PD LL O v n) : Prop :=
  Formalism.MainNotions.LiftingTheory.CaseA W →
  ∀ (h M : ℕ), h < (PD.p - 1) * M →
  (∀ (T : LocLat G Qp LL O), IsCrys PD T.ρ → JumpsLe PD T h →
    (∀ x ∈ W.NΔ T, InFN W T (W.π₀ ^ M * qA W) (W.φD T (W.π₀ ^ M • x))) ∧
    (∀ z, InFN W T (W.π₀ ^ M) z →
      ∃ x, InFN W T (W.π₀ ^ M) x ∧ W.φD T x - x = z ∧
        ∀ x', InFN W T (W.π₀ ^ M) x' → W.φD T x' - x' = z → x' = x) ∧
    (∀ (c : ZMod n) (y : W.DD T), InLet W T c y → IsΔ W T y →
      InFNc W T c (W.π₀ ^ M) (W.γ T y - y) → ∃ x, Cls W T M y x) ∧
    (∀ (c : ZMod n) (y₁ y₂ : W.DD T) (x₁ x₂ : LatticeCohomology T.L), InLet W T c y₁ → InLet W T c y₂ →
      Cls W T M y₁ x₁ → Cls W T M y₂ x₂ → Cls W T M (y₁ + y₂) (x₁ + x₂)) ∧
    (∀ (c : ZMod n) (y : W.DD T), InLet W T c y → IsΔ W T y → InFNc W T c (W.π₀ ^ M) y →
      Cls W T M y 0)) ∧
  (∀ (T T' : LocLat G Qp LL O) (f : LatHom T.L T'.L), IsCrys PD T.ρ → IsCrys PD T'.ρ →
    JumpsLe PD T h → JumpsLe PD T' h →
    ∀ (c : ZMod n) (y : W.DD T) (x : LatticeCohomology T.L), InLet W T c y → Cls W T M y x →
      Cls W T' M (W.map f y) (f.H1map x))

def SecondWachFiltration (W : LocWach PD LL O v n) : Prop :=
  Formalism.MainNotions.LiftingTheory.CaseA W →
  ∀ (h M : ℕ), h < (PD.p - 1) * M → ∀ (T : LocLat G Qp LL O), IsCrys PD T.ρ → JumpsLe PD T h →
    ∀ (c : ZMod n) (y : W.DD T) (x : LatticeCohomology T.L) (Λ : LetA O n), Λ ∈ Ps W → InLet W T c y →
      InFNc W T c 1 (Λ • y) → Cls W T M y x → x ∈ latticeFiniteCohomology PD T.L

def PPO (W : LocWach PD LL O v n) (ell : ℕ) (JS : Finset ℤ) : Polynomial O :=
  (∏ i ∈ JS.erase 0, (Polynomial.X ^ (PD.p ^ ell) -
      Polynomial.C (((W.χΓ W.gam) ^ (i * (PD.p : ℤ) ^ ell) : Oˣ) : O))) *
    ∑ k ∈ Finset.range (PD.p ^ ell), Polynomial.X ^ k

def KillerModCore (W : LocWach PD LL O v n) : Prop :=
  Formalism.MainNotions.LiftingTheory.CaseA W →
  ∀ (T : LocLat G Qp LL O) (c : ZMod n) (ell : ℕ) (JS : Finset ℤ) (w : W.DD T),
    IsCrys PD T.ρ → InLet W T c w → InFNc W T c W.π₀ (W.γ T w - w) →
    InFNc W T c W.π₀ (Polynomial.aeval (W.γ T) (PPO W ell JS) w - (PPO W ell JS).eval 1 • w)

end Core

structure ArcP (n : ℕ) where
  G₀ : ℕ
  S : ℕ
  η : ℕ
  h : ℕ
  j : ℕ
  ty : ZMod n → Formalism.MainNotions.LocalTheoryWindows.LT
  cuts : Finset (ZMod n)
  len : ZMod n → ℕ

def ArcP.OK {n : ℕ} (A : ArcP n) : Prop :=
  A.cuts.Nonempty ∧ 1 ≤ A.j ∧
  (∀ c ∈ A.cuts, 1 ≤ A.len c ∧ A.len c ≤ n ∧ c - ((A.len c : ℕ) : ZMod n) ∈ A.cuts ∧
    ∀ d : ℕ, 1 ≤ d → d < A.len c → c - (d : ZMod n) ∉ A.cuts) ∧
  (∀ c ∈ A.cuts, A.j ≤ A.len c) ∧
  (∀ i, (A.ty i).ok A.η) ∧ A.G₀ ≤ A.h ∧ 1 ≤ A.h ∧
  (∀ i, (A.ty i).thick → (A.ty i).size + A.S ≤ A.h) ∧
  ((∀ c ∈ A.cuts, ∀ k : ℕ, 1 ≤ k → k ≤ A.j → A.ty (c + (k : ZMod n)) = Formalism.MainNotions.LocalTheoryWindows.LT.thin) ∨
    (A.j = 1 ∧ (∀ i, (A.ty i).thick) ∧ ∀ c ∈ A.cuts, (A.ty (c + 1)).size + A.S ≤ A.G₀))

def ArcP.M {n : ℕ} (A : ArcP n) (l : ℕ) : ℕ := 2 * A.h / (l - 1) + 1

def ArcP.σ {n : ℕ} (A : ArcP n) (l : ℕ) : ℕ :=
  ⌈(((2 * A.G₀ : ℕ) : ℝ) + (A.M l : ℝ) / (l : ℝ) ^ (A.j - 1)) * l / ((l : ℝ) - 1) ^ 2 + 1⌉₊

def ArcP.Hs {n : ℕ} (A : ArcP n) (a : ZMod n) (e s : ℕ) : ℕ :=
  if A.ty (a - (s : ZMod n)) = Formalism.MainNotions.LocalTheoryWindows.LT.thin ∨ e - s ≤ A.j then A.G₀ else A.h

def ArcP.JS {n : ℕ} (A : ArcP n) (c : ZMod n) : Finset ℤ :=
  (if ∃ s < A.len c, A.ty (c - (s : ZMod n)) = Formalism.MainNotions.LocalTheoryWindows.LT.thin then
      Finset.Icc (-(2 * A.G₀ : ℤ)) A.G₀ else ∅) ∪
    (Finset.range (A.len c)).biUnion fun s =>
      match A.ty (c - (s : ZMod n)) with
      | .thin => ∅
      | .up b => Finset.Ico (-(b : ℤ) - A.S) (-(b : ℤ))
      | .down b => Finset.Ico (b : ℤ) ((b : ℤ) + A.S)

section ThetaShiftProofs

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

def Win (W : LocWach PD LL O v n) (A : ArcP n) (T : LocLat G Qp LL O) : Prop :=
  IsCrys PD T.ρ ∧ ∀ i, Formalism.MainNotions.TruncatedSeriesCountingBounds.JumpsAt W T i ((A.ty i).win A.G₀ A.S A.η)

def InI (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (c : ZMod n) (w : W.DD T) : Prop :=
  InLet W T c w ∧ IsΔ W T w ∧ InFNc W T c W.π₀ (W.γ T w - w)

def Pp (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (c : ZMod n) (e : ℕ) :
    AddSubgroup (W.DD T) :=
  AddSubgroup.closure {z | ∃ a ∈ W.AΔ, ∃ x, Formalism.MainNotions.LiftingTheory.InNΔi W T c x ∧ z = a • ((W.φD T) ^ e) x}

def InFP (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (c : ZMod n) (e : ℕ) (f : LetA O n)
    (x : W.DD T) : Prop :=
  ∃ y ∈ Pp W T c e, x = f • y

def SATPcore (W : LocWach PD LL O v n) : Prop :=
  Formalism.MainNotions.LiftingTheory.CaseA W →
  ∀ (T : LocLat G Qp LL O) (c : ZMod n) (e : ℕ) (f f' : LetA O n), IsCrys PD T.ρ → f ∈ PiPs W →
    f' ∈ PiPs W → ∀ x : W.DD T,
      InFP W T c e 1 (f' • x) → (∃ k : ℕ, InFP W T c e f (lA W ^ k • x)) → InFP W T c e f x

def abelian₂ (W : LocWach PD LL O v n) (A : ArcP n) (a : ZMod n) (e : ℕ) : LetA O n :=
  ∏ s ∈ Finset.range e, ps W s ^ A.Hs a e s

def InFr (W : LocWach PD LL O v n) (a : ZMod n) (num den : LetA O n) (f : W.EE) : Prop :=
  ∃ u ∈ W.AΔ, algebraMap (LetA O n) W.EE den * f = algebraMap (LetA O n) W.EE (letE a * num * u)

def InId (W : LocWach PD LL O v n) (a : ZMod n) (e : ℕ) (α : ℕ → ℤ) (f : W.EE) : Prop :=
  InFr W a (∏ s ∈ Finset.range e, ps W s ^ (α s).toNat) (∏ s ∈ Finset.range e, ps W s ^ (-(α s)).toNat) f

def lE (W : LocWach PD LL O v n) (k : ℕ) : W.EE := ((PD.p : ℕ) : W.EE) ^ k

def IsHor (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (c : ZMod n) {d : ℕ}
    (b : Fin d → W.DD T) (sol : Fin d → ℕ → Fin d → LL) : Prop :=
  Formalism.MainNotions.LiftingTheory.IsFrameΔ W T c b ∧
    ∀ k, Formalism.MainNotions.LiftingTheory.IsSol W T c b 0 (sol k) ∧ sol k 0 = Pi.single k 1

def IsHorTr (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) {d : ℕ} (b : Fin d → W.DD T)
    (sol : Fin d → ℕ → Fin d → LL) (R κ : ℕ) (k : Fin d) (x : W.DD T) : Prop :=
  ∃ y : ℕ → Fin d → O, (∀ r < R, ∀ m, algebraMap O LL (y r m) = (PD.p : LL) ^ κ * sol k r m) ∧
    x = ∑ r ∈ Finset.range R, W.π₀ ^ r • Formalism.MainNotions.LiftingTheory.vecB W T b (y r)

def RepVV (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (c' : ZMod n) (e M : ℕ) (Λ : LetA O n)
    {d : ℕ} (b : Fin d → W.DD T) (sol : Fin d → ℕ → Fin d → LL) (x : W.DD T) (f : Fin d → W.EE) :
    Prop :=
  ∃ (κ κ' : ℕ) (Hh : Fin d → W.DD T) (a : Fin d → LetA O n),
    (∀ k, IsHorTr W T b sol M κ k (Hh k)) ∧
    (∀ k, a k ∈ W.AΔ ∧ algebraMap (LetA O n) W.EE Λ * f k = algebraMap (LetA O n) W.EE (a k)) ∧
    InFP W T c' e (W.π₀ * Λ ^ 2)
      (lA W ^ κ' • (lA W ^ κ • Λ • x - ∑ k, a k • ((W.φD T) ^ e) (Hh k)))

def cmpD (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (x : W.DD T) : T.V ⊗[Qp] B :=
  if h : x ∈ W.N T then W.cmp T ⟨x, h⟩ else 0

def dv (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (e : ℕ) {d : ℕ} (b : Fin d → W.DD T)
    (c₀ : Fin d → LL) : T.V ⊗[Qp] B :=
  ∑ m, c₀ m • ((φVB PD (LL := LL) (V := T.V)) ^ e) (cmpD W T (b m))

def dvO (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (e : ℕ) {d : ℕ} (b : Fin d → W.DD T)
    (c₀ : Fin d → O) : T.V ⊗[Qp] B :=
  dv W T e b fun m => algebraMap O LL (c₀ m)

def FilS (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (a : ZMod n) (s : ℕ) (u : ℤ) :
    Submodule LL (T.V ⊗[Qp] B) :=
  (FilCris PD T.ρ u ⊓ DcrisL PD T.ρ (W.emb (a - (s : ZMod n)))).map
    (((φVB PD (LL := LL) (V := T.V)) ^ s : Module.End LL (T.V ⊗[Qp] B)) :
      T.V ⊗[Qp] B →ₗ[LL] T.V ⊗[Qp] B)

def SecIn (W : LocWach PD LL O v n) (a : ZMod n) (e : ℕ) {d : ℕ} (cond : (ℕ → ℤ) → (Fin d → O) → Prop)
    (f : Fin d → W.EE) : Prop :=
  ∃ (I : ℕ) (g : Fin I → W.EE) (c₀ : Fin I → Fin d → O) (α : Fin I → ℕ → ℤ),
    (∀ i, InId W a e (α i) (g i) ∧ cond (α i) (c₀ i)) ∧
    ∀ k, f k = ∑ i, g i * algebraMap O W.EE (c₀ i k)

def condNN (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (a : ZMod n) (e : ℕ) {d : ℕ}
    (b : Fin d → W.DD T) (α : ℕ → ℤ) (c₀ : Fin d → O) : Prop :=
  ∀ s < e, dvO W T e b c₀ ∈ FilS W T a s (-(α s))

def InNL (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (a : ZMod n) (e : ℕ) (Λ : LetA O n) {d : ℕ}
    (b : Fin d → W.DD T) (f : Fin d → W.EE) : Prop :=
  (∀ k, InFr W a 1 Λ (f k)) ∧ ∃ κ : ℕ, SecIn W a e (condNN W T a e b) fun k => lE W κ * f k

def InvNL (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (a : ZMod n) (e : ℕ) (Λ : LetA O n) {d : ℕ}
    (b : Fin d → W.DD T) (f : Fin d → W.EE) : Prop :=
  ∃ g, InNL W T a e Λ b g ∧ ∀ k, W.γE W.gam (f k) - f k = algebraMap (LetA O n) W.EE W.π₀ * g k

def IsTr (W : LocWach PD LL O v n) (A : ArcP n) (T : LocLat G Qp LL O) (c : ZMod n)
    (w τ : W.DD T) : Prop :=
  InFP W T c A.j W.π₀ τ ∧
  ∃ (d : ℕ) (b : Fin d → W.DD T) (cf : ℕ → Fin d → LL), Formalism.MainNotions.LiftingTheory.IsFrameΔ W T c b ∧
    Formalism.MainNotions.LiftingTheory.IsSol W T c b (W.γ T w - w) cf ∧ cf 0 = 0 ∧
    ∃ (κ κ' : ℕ) (y : ℕ → Fin d → O),
      (∀ r < A.M PD.p, ∀ m, algebraMap O LL (y r m) = (PD.p : LL) ^ κ * cf r m) ∧
      InFP W T c A.j (Formalism.MainNotions.LiftingTheory.JJ W A.j (2 * A.G₀) (A.M PD.p))
        (lA W ^ κ' • (lA W ^ κ • τ - lA W ^ (A.σ PD.p) • ((W.φD T) ^ A.j)
          (∑ r ∈ Finset.range (A.M PD.p), W.π₀ ^ r • Formalism.MainNotions.LiftingTheory.vecB W T b (y r))))

def IsRho (W : LocWach PD LL O v n) (A : ArcP n) (T : LocLat G Qp LL O) (c : ZMod n)
    (w : W.DD T) (x : LatticeCohomology T.L) : Prop :=
  ∃ τ, IsTr W A T c w τ ∧
    Cls W T (A.M PD.p) (lA W ^ (A.σ PD.p) • ((W.φD T) ^ A.j) w - τ) x

def RelayCore (W : LocWach PD LL O v n) : Prop :=
  Formalism.MainNotions.LiftingTheory.CaseA W → 5 ≤ PD.p → ∀ A : ArcP n, A.OK → ∀ c ∈ A.cuts,
  (∀ T : LocLat G Qp LL O, Win W A T →
    (∀ y ∈ Pp W T c A.j,
      InFNc W T (c + (A.j : ZMod n)) (W.π₀ ^ A.M PD.p)
        (Formalism.MainNotions.LiftingTheory.JJ W A.j (2 * A.G₀) (A.M PD.p) • y) ∧
      InFNc W T (c + (A.j : ZMod n)) 1 ((∏ s ∈ Finset.range A.j, ps W s ^ A.G₀) • y)) ∧
    (∀ w, InI W T c w →
      (∃ τ, IsTr W A T c w τ) ∧
      (∀ τ τ', IsTr W A T c w τ → IsTr W A T c w τ' →
        InFP W T c A.j (Formalism.MainNotions.LiftingTheory.JJ W A.j (2 * A.G₀) (A.M PD.p)) (τ - τ')) ∧
      (∀ τ, IsTr W A T c w τ →
        InFNc W T (c + (A.j : ZMod n)) (W.π₀ ^ A.M PD.p)
          (W.γ T (lA W ^ (A.σ PD.p) • ((W.φD T) ^ A.j) w - τ) -
            (lA W ^ (A.σ PD.p) • ((W.φD T) ^ A.j) w - τ))) ∧
      (∃ x, IsRho W A T c w x) ∧
      (∀ x x', IsRho W A T c w x → IsRho W A T c w x' → x = x') ∧
      (InFNc W T c W.π₀ w → IsRho W A T c w 0) ∧
      (∀ (Λ' : LetA O n) (x : LatticeCohomology T.L), Λ' ∈ Ps W → InFNc W T c 1 (Λ' • w) → IsRho W A T c w x →
        x ∈ latticeFiniteCohomology PD T.L)) ∧
    (∀ w₁ w₂ x₁ x₂, InI W T c w₁ → InI W T c w₂ → IsRho W A T c w₁ x₁ → IsRho W A T c w₂ x₂ →
      IsRho W A T c (w₁ + w₂) (x₁ + x₂))) ∧
  (∀ (T T' : LocLat G Qp LL O) (f : LatHom T.L T'.L), Win W A T → Win W A T' →
    ∀ w x, InI W T c w → IsRho W A T c w x → IsRho W A T' c (W.map f w) (f.H1map x))

def ArcCore (W : LocWach PD LL O v n) : Prop :=
  Formalism.MainNotions.LiftingTheory.CaseA W → 5 ≤ PD.p → ∀ A : ArcP n, A.OK → ∀ c ∈ A.cuts, ∀ e : ℕ, A.j ≤ e → e ≤ A.len c →
  let c' : ZMod n := c - ((A.len c : ℕ) : ZMod n)
  let a : ZMod n := c' + (e : ZMod n)
  let Λ : LetA O n := abelian₂ W A a e
  let M : ℕ := A.M PD.p
  let σ : ℕ := A.σ PD.p
  (∃ u ∈ W.AΔ, (W.φA ^ (e - A.j)) (Formalism.MainNotions.LiftingTheory.JJ W A.j (2 * A.G₀) M) = W.π₀ * Λ ^ 2 * u) ∧
  ∀ T : LocLat G Qp LL O, Win W A T →
    (∀ y ∈ Pp W T c' e, InFNc W T a 1 (Λ • y)) ∧
    (∀ x, InFNc W T a 1 x → InFP W T c' e 1 (Λ • x)) ∧
    (∀ x, InFP W T c' e 1 (Λ • x) → (∃ k : ℕ, InFNc W T a 1 (lA W ^ k • x)) → InFNc W T a 1 x) ∧
    ∀ (d : ℕ) (b : Fin d → W.DD T) (sol : Fin d → ℕ → Fin d → LL), IsHor W T c' b sol →
      (LinearIndependent LL (fun k : Fin d => dv W T e b (Pi.single k 1)) ∧
        Submodule.span LL (Set.range fun k : Fin d => dv W T e b (Pi.single k 1)) =
          DcrisL PD T.ρ (W.emb a)) ∧
      (∀ x, InFP W T c' e 1 (Λ • x) →
        ∃ f, (∀ k, InFr W a 1 Λ (f k)) ∧ RepVV W T c' e M Λ b sol (lA W ^ σ • x) f) ∧
      (∀ f : Fin d → W.EE, (∀ k, InFr W a 1 Λ (f k)) →
        ∃ x, InFP W T c' e 1 (Λ • x) ∧ RepVV W T c' e M Λ b sol x fun k => lE W σ * f k) ∧
      (∀ x, InFNc W T a 1 x → ∃ f, InNL W T a e Λ b f ∧ RepVV W T c' e M Λ b sol (lA W ^ σ • x) f) ∧
      (∀ f, InNL W T a e Λ b f →
        ∃ x, InFNc W T a 1 x ∧ RepVV W T c' e M Λ b sol x fun k => lE W σ * f k) ∧
      (∀ x, InFP W T c' e 1 (Λ • x) → RepVV W T c' e M Λ b sol x 0 → InFP W T c' e (W.π₀ * Λ) x) ∧
      (∀ x (k : ℕ) f, InFP W T c' e 1 (Λ • x) → RepVV W T c' e M Λ b sol (lA W ^ k • x) f →
        (∀ m, InFr W a 1 Λ (f m)) →
        (InFNc W T a 1 x ↔ ∃ κ : ℕ, SecIn W a e (condNN W T a e b) fun m => lE W κ * f m))

def ArcLCore (W : LocWach PD LL O v n) : Prop :=
  Formalism.MainNotions.LiftingTheory.CaseA W → ∀ (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L), Formalism.MainNotions.LiftingTheory.Sur W F →
    ∀ (c' : ZMod n) (rr e : ℕ), Formalism.MainNotions.LiftingTheory.KillsΔ W F c' (Formalism.MainNotions.LiftingTheory.lp W rr) →
    ∀ x₂, Formalism.MainNotions.LiftingTheory.InNΔi W T₂ c' x₂ → ∃ x₁, Formalism.MainNotions.LiftingTheory.InNΔi W T₁ c' x₁ ∧
      Formalism.MainNotions.TruncatedSeriesCountingBounds.crisMap B F.f (((φVB PD (LL := LL) (V := T₁.V)) ^ e) (cmpD W T₁ x₁)) =
        ((PD.p : LL) ^ rr) • ((φVB PD (LL := LL) (V := T₂.V)) ^ e) (cmpD W T₂ x₂)

def condPole (W : LocWach PD LL O v n) (A : ArcP n) (T : LocLat G Qp LL O) (c : ZMod n) {d : ℕ}
    (b : Fin d → W.DD T) (α : ℕ → ℤ) (c₀ : Fin d → O) : Prop :=
  ∀ s < A.len c,
    match A.ty (c - (s : ZMod n)) with
    | .thin => -(A.G₀ : ℤ) ≤ α s
    | .up bs => -((bs : ℤ) + A.S) ≤ α s
    | .down _ => 0 ≤ α s ∨ dvO W T (A.len c) b c₀ ∈ FilS W T c s (-(A.η : ℤ))

def PoleOK (W : LocWach PD LL O v n) (A : ArcP n) (T : LocLat G Qp LL O) (c : ZMod n) {d : ℕ}
    (b : Fin d → W.DD T) (sol : Fin d → ℕ → Fin d → LL) (w : W.DD T) : Prop :=
  ∃ (κ : ℕ) (f : Fin d → W.EE),
    RepVV W T (c - ((A.len c : ℕ) : ZMod n)) (A.len c) (A.M PD.p) (abelian₂ W A c (A.len c)) b sol
      (lA W ^ κ • w) f ∧
    SecIn W c (A.len c) (condPole W A T c b) f

def SplitCore (W : LocWach PD LL O v n) : Prop :=
  Formalism.MainNotions.LiftingTheory.CaseA W → 5 ≤ PD.p → ∀ A : ArcP n, A.OK →
  ∀ (T₂ Y : LocLat G Qp LL O) (ι : LatHom T₂.L Y.L) (π : LatHom Y.L W.one.L), Win W A T₂ →
    IsCrys PD Y.ρ → ∀ (cc : G → T₂.V) (hc : cc ∈ latticeCocycles T₂.L), Formalism.MainNotions.LiftingTheory.IsExtOf W ι π cc →
    ∀ rr : ℕ, (∀ c ∈ A.cuts, Formalism.MainNotions.LiftingTheory.KillsΔ W π c (Formalism.MainNotions.LiftingTheory.lp W rr)) →
    ∃ (w : ZMod n → W.DD T₂) (x : ZMod n → LatticeCohomology T₂.L),
      (∀ c ∈ A.cuts, InI W T₂ c (w c) ∧
        InFP W T₂ (c - ((A.len c : ℕ) : ZMod n)) (A.len c) 1 (abelian₂ W A c (A.len c) • w c) ∧
        IsRho W A T₂ c (w c) (x c) ∧
        ∀ (d : ℕ) (b : Fin d → W.DD T₂) (sol : Fin d → ℕ → Fin d → LL),
          IsHor W T₂ (c - ((A.len c : ℕ) : ZMod n)) b sol → PoleOK W A T₂ c b sol (w c)) ∧
      ((((PD.p : ℕ) : O) ^ (rr + 2 * A.σ PD.p)) •
            (Submodule.Quotient.mk (⟨cc, hc⟩ : ↥(latticeCocycles T₂.L)) : LatticeCohomology T₂.L) = ∑ c ∈ A.cuts, x c ∨
        (((PD.p : ℕ) : O) ^ (rr + 2 * A.σ PD.p)) •
            (Submodule.Quotient.mk (⟨cc, hc⟩ : ↥(latticeCocycles T₂.L)) : LatticeCohomology T₂.L) = -∑ c ∈ A.cuts, x c)

def PPγ (W : LocWach PD LL O v n) (ell : ℕ) (JS : Finset ℤ) (f : W.EE) : W.EE :=
  Polynomial.aeval ((W.γE W.gam).toLinearMap : Module.End O W.EE) (PPO W ell JS) f

def KillerLevCore (W : LocWach PD LL O v n) : Prop :=
  Formalism.MainNotions.LiftingTheory.CaseA W → ∀ (ell : ℕ) (JS : Finset ℤ),
  v (algebraMap O LL ((PPO W ell JS).eval 1)) =
      ((ell + ∑ i ∈ JS.erase 0, (ell + 1 + padicValInt PD.p i) : ℕ) : WithTop ℚ) ∧
  ∀ (a : ZMod n) (α : ℕ → ℤ) (s : ℕ), s < ell → ∀ f : W.EE, InId W a ell α f →
    (α s ∈ JS → α s ≠ 0 →
      ∃ κ : ℕ, InId W a ell (Function.update α s (α s + 1)) (lE W κ * PPγ W ell JS f)) ∧
    (α s = 0 →
      ∃ κ : ℕ, InId W a ell (Function.update α s 1) (lE W κ * PPγ W ell JS (W.γE W.gam f - f))) ∧
    (∀ N : ℕ, ∃ κ : ℕ, InId W a ell (Function.update α s (α s + N))
      (lE W κ * Polynomial.aeval ((W.γE W.gam).toLinearMap : Module.End O W.EE)
        (∏ i ∈ Finset.Ico (α s) (α s + N), (Polynomial.X ^ (PD.p ^ ell) -
          Polynomial.C (((W.χΓ W.gam) ^ (i * (PD.p : ℤ) ^ ell) : Oˣ) : O))) f))

def prodTy (W : LocWach PD LL O v n) (A : ArcP n) (c : ZMod n) (F : Formalism.MainNotions.LocalTheoryWindows.LT → ℕ) : LetA O n :=
  ∏ s ∈ Finset.range (A.len c), ps W s ^ F (A.ty (c - (s : ZMod n)))

def mmDen (W : LocWach PD LL O v n) (A : ArcP n) (c : ZMod n) : LetA O n :=
  prodTy W A c fun | .thin => A.G₀ | .up b => b + A.S | .down _ => 0

def downB (W : LocWach PD LL O v n) (A : ArcP n) (c : ZMod n) : LetA O n :=
  prodTy W A c fun | .thin => 0 | .up _ => 0 | .down b => b

def nnNum (W : LocWach PD LL O v n) (A : ArcP n) (c : ZMod n) : LetA O n :=
  prodTy W A c fun | .thin => A.G₀ | .up _ => 0 | .down b => b + A.S

def nnDen (W : LocWach PD LL O v n) (A : ArcP n) (c : ZMod n) : LetA O n :=
  prodTy W A c fun | .thin => 0 | .up b => b | .down _ => 0

def UnivNNCore (W : LocWach PD LL O v n) : Prop :=
  Formalism.MainNotions.LiftingTheory.CaseA W → 5 ≤ PD.p → ∀ A : ArcP n, A.OK → ∀ c ∈ A.cuts,
  ∀ T : LocLat G Qp LL O, Win W A T →
  ∀ (d : ℕ) (b : Fin d → W.DD T) (sol : Fin d → ℕ → Fin d → LL),
    IsHor W T (c - ((A.len c : ℕ) : ZMod n)) b sol →
    ∀ c₀ : Fin d → O,
      (∀ s < A.len c, ∀ bs, A.ty (c - (s : ZMod n)) = Formalism.MainNotions.LocalTheoryWindows.LT.up bs →
        dvO W T (A.len c) b c₀ ∈ FilS W T c s bs) →
      ∀ g : W.EE, InFr W c (nnNum W A c) (nnDen W A c) g →
        InNL W T c (A.len c) (abelian₂ W A c (A.len c)) b fun k => g * algebraMap O W.EE (c₀ k)

def UnivCore (PD : PeriodData G Qp K₀ K B BdR) [Fintype (K →ₐ[Qp] LL)] (W : LocWach PD LL O v n) :
    Prop :=
  Formalism.MainNotions.LiftingTheory.CaseA W → 5 ≤ PD.p → ∀ (A : ArcP n) (m : ℕ), A.OK →
  ∀ T₂ : LocLat G Qp LL O, Win W A T₂ →
  (∀ i, (A.ty i).thick → Formalism.MainNotions.TruncatedSeriesCountingBounds.lowCount W T₂ i A.η ≤ m) → ∀ c ∈ A.cuts,
  let ell : ℕ := A.len c
  let c' : ZMod n := c - ((A.len c : ℕ) : ZMod n)
  let Λ : LetA O n := abelian₂ W A c ell
  let M : ℕ := A.M PD.p
  let σ : ℕ := A.σ PD.p
  let JS : Finset ℤ := A.JS c
  ∃ (d : ℕ) (b : Fin d → W.DD T₂) (sol : Fin d → ℕ → Fin d → LL) (Rst : Finset (Fin d)),
    IsHor W T₂ c' b sol ∧ Rst.card ≤ m * Formalism.MainNotions.LocalTheoryWindows.ro A.ty A.len c ∧
    (∀ k ∉ Rst, ∀ s < ell, ∀ bs, A.ty (c - (s : ZMod n)) = Formalism.MainNotions.LocalTheoryWindows.LT.up bs →
      dv W T₂ ell b (Pi.single k 1) ∈ FilS W T₂ c s bs) ∧
    (∀ s < ell, ∀ bs, A.ty (c - (s : ZMod n)) = Formalism.MainNotions.LocalTheoryWindows.LT.down bs →
      FilS W T₂ c s (-(A.η : ℤ)) ≤
        Submodule.span LL ((fun k : Fin d => dv W T₂ ell b (Pi.single k 1)) '' (Rst : Set (Fin d)))) ∧
    (∀ w, InI W T₂ c w → InFP W T₂ c' ell 1 (Λ • w) → PoleOK W A T₂ c b sol w →
      ∃ f : Fin d → W.EE, (∀ k, InFr W c 1 Λ (f k)) ∧ RepVV W T₂ c' ell M Λ b sol (lA W ^ σ • w) f ∧
        (∀ k ∉ Rst,
          InFr W c 1 (mmDen W A c) (f k) ∧
          InFr W c (W.π₀ * downB W A c) (mmDen W A c) (W.γE W.gam (f k) - f k) ∧
          InFr W c (W.π₀ * nnNum W A c) (nnDen W A c)
            (W.γE W.gam (PPγ W ell JS (f k)) - PPγ W ell JS (f k)) ∧
          InFr W c 1 (nnDen W A c) (PPγ W ell JS (f k)) ∧
          ∀ s < ell, ∀ bs, A.ty (c - (s : ZMod n)) = Formalism.MainNotions.LocalTheoryWindows.LT.down bs →
            ∃ (κ : ℕ) (x : O), InFr W c (ps W s ^ (bs + A.S)) (nnDen W A c)
              (lE W κ * PPγ W ell JS (f k) -
                algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE x)) ∧
        InvNL W T₂ c ell Λ b (fun k => if k ∈ Rst then 0 else PPγ W ell JS (f k)) ∧
        InvNL W T₂ c ell Λ b (fun k => if k ∈ Rst then PPγ W ell JS (f k) else 0)) ∧
    (∃ (g₀ : ℕ) (J : Fin g₀ → Fin d → W.EE), g₀ ≤ m * Formalism.MainNotions.LocalTheoryWindows.ro A.ty A.len c * (ell + 1) ∧
      (∀ i, (∀ k, InFr W c 1 Λ (J i k)) ∧ (∀ k ∉ Rst, J i k = 0) ∧ InvNL W T₂ c ell Λ b (J i)) ∧
      ∀ f : Fin d → W.EE, (∀ k, InFr W c 1 Λ (f k)) → (∀ k ∉ Rst, f k = 0) → InvNL W T₂ c ell Λ b f →
        ∃ (o : Fin g₀ → O) (g : Fin d → W.EE), InNL W T₂ c ell Λ b g ∧
          ∀ k, f k - ∑ i, algebraMap O W.EE (o i) * J i k = algebraMap (LetA O n) W.EE W.π₀ * g k) ∧
    (∀ f : Fin d → W.EE, (∀ k, InFr W c 1 Λ (f k)) → InvNL W T₂ c ell Λ b f →
      ∃ u, InI W T₂ c u ∧ InFP W T₂ c' ell 1 (Λ • u) ∧
        RepVV W T₂ c' ell M Λ b sol u fun k => lE W σ * f k)

end ThetaShiftProofs

def R2 : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (l : ℕ), l.Prime → ∀ (e : ℕ) (u : Oˣ), 1 ≤ e → ((l : ℕ) : O) = (u : O) * ϖ ^ e →
    ∀ (f₁ : PowerSeries O) (a A' y B v₁ k : ℕ),
      ϖ ^ (e * v₁) ∣ PowerSeries.constantCoeff f₁ → ¬ ϖ ^ (e * v₁ + 1) ∣ PowerSeries.constantCoeff f₁ →
      y + A' + a + v₁ + 1 ≤ B →
      PowerSeries.C ((l : O) ^ a) * f₁ * (PowerSeries.X - PowerSeries.C (l : O)) ^ A' *
          PowerSeries.X ^ y ∈
        Ideal.span {PowerSeries.C (ϖ ^ k), (PowerSeries.X : PowerSeries O) ^ B} →
      (k : ℚ) / e < a + v₁ + 1

def KillerKap (C : ℝ) : Prop :=
  ∀ (l : ℕ), l.Prime → 5 ≤ l → ∀ (G S h ell ro : ℕ) (a : Fin ro → ℤ), G ≤ h → 1 ≤ h →
    (∀ k, -(2 * h : ℤ) ≤ a k ∧ a k + S ≤ 2 * h) →
    let JS := Finset.Icc (-(2 * G : ℤ)) G ∪ Finset.univ.biUnion fun k => Finset.Ico (a k) (a k + S)
    ((ell + ∑ i ∈ JS.erase 0, (ell + 1 + padicValInt l i) : ℕ) : ℝ) ≤
      C * (((G : ℝ) + ro * S + 1) * (ell + 1) + (ro + 1) * Real.logb l h)

section Theory

def AtCaseA (P : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (_ : Good K 1 LL), Prop) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hG : Good K 1 LL), CaseA K LL → 5 ≤ l → P l K LL hG

def SATL (LT : LocTheory) (A : ∀ (l : ℕ) [Fact l.Prime], LocAinf l (LT l)) (HW : HWOf LT) (F : FonOf LT A HW) : Prop := AtCaseA fun l _ K LL hG => SATcore ((HW l).W K 1 LL hG)

def SATPL (LT : LocTheory) (A : ∀ (l : ℕ) [Fact l.Prime], LocAinf l (LT l)) (HW : HWOf LT) (F : FonOf LT A HW) : Prop :=
  AtCaseA fun l _ K LL hG => SATPcore ((HW l).W K 1 LL hG)

def FirstFiltrationAtLevelOne (LT : LocTheory) (A : ∀ (l : ℕ) [Fact l.Prime], LocAinf l (LT l)) (HW : HWOf LT) (F : FonOf LT A HW) : Prop := AtCaseA fun l _ K LL hG => FirstWachFiltration ((HW l).W K 1 LL hG)

def SecondFiltrationAtLevelOne (LT : LocTheory) (A : ∀ (l : ℕ) [Fact l.Prime], LocAinf l (LT l)) (HW : HWOf LT) (F : FonOf LT A HW) : Prop := AtCaseA fun l _ K LL hG => SecondWachFiltration ((HW l).W K 1 LL hG)

def KillerModL (LT : LocTheory) (A : ∀ (l : ℕ) [Fact l.Prime], LocAinf l (LT l)) (HW : HWOf LT) (F : FonOf LT A HW) : Prop :=
  AtCaseA fun l _ K LL hG => KillerModCore ((HW l).W K 1 LL hG)

def KillerLevL (LT : LocTheory) (A : ∀ (l : ℕ) [Fact l.Prime], LocAinf l (LT l)) (HW : HWOf LT) (F : FonOf LT A HW) : Prop :=
  AtCaseA fun l _ K LL hG => KillerLevCore ((HW l).W K 1 LL hG)

def RelayL (LT : LocTheory) (A : ∀ (l : ℕ) [Fact l.Prime], LocAinf l (LT l)) (HW : HWOf LT) (F : FonOf LT A HW) : Prop := AtCaseA fun l _ K LL hG => RelayCore ((HW l).W K 1 LL hG)

def ArcL (LT : LocTheory) (A : ∀ (l : ℕ) [Fact l.Prime], LocAinf l (LT l)) (HW : HWOf LT) (F : FonOf LT A HW) (Cm : CmpOf LT A HW F) : Prop :=
  AtCaseA fun l _ K LL hG => ArcCore ((HW l).W K 1 LL hG) ∧ ArcLCore ((HW l).W K 1 LL hG)

def SplitL (LT : LocTheory) (A : ∀ (l : ℕ) [Fact l.Prime], LocAinf l (LT l)) (HW : HWOf LT) (F : FonOf LT A HW) (Cm : CmpOf LT A HW F) : Prop := AtCaseA fun l _ K LL hG => SplitCore ((HW l).W K 1 LL hG)

def UnivL (LT : LocTheory) (A : ∀ (l : ℕ) [Fact l.Prime], LocAinf l (LT l)) (HW : HWOf LT) (F : FonOf LT A HW) (Cm : CmpOf LT A HW F) : Prop :=
  AtCaseA fun l _ K LL hG => UnivNNCore ((HW l).W K 1 LL hG) ∧
    ∀ [Fintype (↥K.1 →ₐ[ℚ_[l]] ↥LL.1)], UnivCore ((LT l).PD K) ((HW l).W K 1 LL hG)

end Theory

def aux₃ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C : ℝ) : Prop := Formalism.MainNotions.TruncatedSeriesCountingBounds.Conclusion1 D HW F C

def adm1 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) : Prop := Formalism.MainNotions.DeltaInvariantLattices.UsedLocalConclusion D HW F Cm

def adm2 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (CR CA CB CK : ℝ) : Prop := Formalism.MainNotions.LiftingTheory.aux₃ D HW F CR CA CB CK

def adm3 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C : ℝ) : Prop := Formalism.MainNotions.LocalTheoryWindows.Conclusion1 D HW F C

def ArchimedeanSignatureMatching (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C : ℝ) : Prop := Formalism.MainNotions.LocalTheoryWindows.Conclusion2 D HW F C

def adm5 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := SATL D.loc D.locA HW F

def adm6 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := FirstFiltrationAtLevelOne D.loc D.locA HW F

def adm7 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := SecondFiltrationAtLevelOne D.loc D.locA HW F

def adm8 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C : ℝ) : Prop :=
  Formalism.WindowSums.KillerVal ∧ Formalism.WindowSums.KillerKills ∧ KillerLevL D.loc D.locA HW F ∧ KillerModL D.loc D.locA HW F ∧ KillerKap C

def adm9 (_D : D7) : Prop := R2

def adm10 (D : D7) : Prop := Formalism.MainNotions.LocalTheoryWindows.H1fGeneratorBoundAll D.loc

def adm11 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := RelayL D.loc D.locA HW F

def adm12 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) : Prop := ArcL D.loc D.locA HW F Cm

def adm13 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) : Prop := SplitL D.loc D.locA HW F Cm

def adm14 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) : Prop := UnivL D.loc D.locA HW F Cm

def adm15 (D : D7) : Prop := Formalism.MainNotions.TruncatedSeriesCountingBounds.adm9 D

def adm16 (D : D7) : Prop := Formalism.MainNotions.RamifiedCoefficientChains.adm15 D

def SaturationFrobeniusPullback (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := SATPL D.loc D.locA HW F

def AdmSatP (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F

def SaturationPullback (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := AdmSatP D HW F → SaturationFrobeniusPullback D HW F

def admitted (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (CR CA CB CK Ckap : ℝ) : Prop :=
  adm1 D HW F Cm ∧ adm2 D HW F CR CA CB CK ∧ adm5 D HW F ∧ SaturationFrobeniusPullback D HW F ∧ adm8 D HW F Ckap ∧ adm9 D ∧
    adm10 D ∧ adm11 D HW F ∧ adm12 D HW F Cm ∧ adm13 D HW F Cm ∧ adm14 D HW F Cm ∧ adm15 D ∧ adm16 D

def Stmt (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (C CR CA CB CK Ckap : ℝ) : Prop :=
  admitted D HW F Cm CR CA CB CK Ckap → aux₃ D HW F C

end Formalism.MainNotions.ArcLiftingSetup
