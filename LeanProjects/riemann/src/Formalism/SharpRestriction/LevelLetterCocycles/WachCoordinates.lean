import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
import Formalism.WeaklyAdmissibleFiltrations.Statement
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LiftingTheory
import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices
import Formalism.SharpRestriction.LevelLetterCocycles.LocalTheoryWindows
import Formalism.WindowSums.Statement

noncomputable section

namespace Formalism.MainNotions.WachCoordinates

open Formalism.WeaklyAdmissibleFiltrations Module

export Formalism.MainNotions.LocalTheoryWindows (LT LT.thin LT.up LT.down LT.thick LT.size LT.win LT.ok CutsOK thickLv ro)

export Formalism.MainNotions.TruncatedSeriesCountingBounds (Thick Clusters ColLeR)

def ThickLe2 {n : ℕ} (ty : ZMod n → LT) (cuts : Finset (ZMod n)) (arcLen : ZMod n → ℕ) : Prop :=
  ∀ c ∈ cuts, ro ty arcLen c ≤ 2

def WordOK {n : ℕ} (l a₀ : ℕ) (ty : ZMod n → LT) (cuts : Finset (ZMod n)) (arcLen : ZMod n → ℕ) :
    Prop :=
  ∀ c ∈ cuts, ∀ s₀ s₁ : ℕ, s₀ < s₁ → s₁ < arcLen c → ∀ b₀ b₁ : ℕ,
    (ty (c - (s₁ : ZMod n)) = LT.down b₁ → ty (c - (s₀ : ZMod n)) = LT.up b₀ → b₀ < l * b₁) ∧
    (ty (c - (s₁ : ZMod n)) = LT.up b₁ → ty (c - (s₀ : ZMod n)) = LT.down b₀ →
      2 * b₀ ≤ l * b₁ ∧ 2 * a₀ < b₁)

def SizesOK {n : ℕ} (g S h : ℕ) (ty : ZMod n → LT) : Prop :=
  ∀ i, (ty i).ok g ∧ (ty i).size + S ≤ h ∨ ty i = LT.thin

def gPar (G S η : ℕ) : ℕ := max (max (max G S) η) 1

def Mpar (l g h : ℕ) : ℕ := (h + 2 * g) / (l - 1) + 1

def sigPar (l g h j : ℕ) : ℕ :=
  ⌈(((3 * g : ℕ) : ℝ) + (Mpar l g h : ℝ) / (l : ℝ) ^ (j - 1)) * l / ((l : ℝ) - 1) ^ 2 + 1⌉₊

def Hmax (n : ℕ) [NeZero n] (H : ZMod n → ℕ) : ℕ := Finset.univ.sup H

def ccPar (l Hm : ℕ) : ℕ := ⌈1 + Real.logb l ((Hm : ℝ) + 1)⌉₊

def sBd (l n : ℕ) [NeZero n] (H : ZMod n → ℕ) (i : ZMod n) : ℝ :=
  ∑' a : ℕ, ((H (i + ((a + 1 : ℕ) : ZMod n)) : ℝ) + ccPar l (Hmax n H) + 3) / ((l : ℝ) - 1) ^ a

def rF (l n : ℕ) [NeZero n] (H : ZMod n → ℕ) (i : ZMod n) : ℕ :=
  ⌊min (⌊sBd l n H i⌋₊ : ℝ) (Hmax n H : ℝ) * l / ((l : ℝ) - 1) ^ 2⌋₊ + ccPar l (Hmax n H)

def rrPar (l n : ℕ) [NeZero n] (H₁ H₂ : ZMod n → ℕ) (cuts : Finset (ZMod n)) : ℕ :=
  cuts.sup fun c => max (rF l n H₁ c) (rF l n H₂ c)

def wins (g h : ℕ) : Finset (Finset ℤ) :=
  (((Finset.Icc (-(2 * h : ℤ)) (2 * h)) ×ˢ Finset.range (3 * g + 1)).filter
      fun p => p.1 + (p.2 : ℤ) ≤ 2 * h + 1).image fun p => Finset.Ico p.1 (p.1 + (p.2 : ℤ))

def vPP1 (l ell : ℕ) (JS : Finset ℤ) : ℕ := ell + ∑ i ∈ JS.erase 0, (ell + 1 + padicValInt l i)

def kapPar (l g h ell : ℕ) : ℕ :=
  (wins g h ×ˢ wins g h ×ˢ wins g h).sup fun w => vPP1 l ell (w.1 ∪ w.2.1 ∪ w.2.2)

def ellMax {n : ℕ} (cuts : Finset (ZMod n)) (arcLen : ZMod n → ℕ) : ℕ := cuts.sup arcLen

def initialExponentBound (l n : ℕ) [NeZero n] (j g h : ℕ) (H₁ H₂ : ZMod n → ℕ) (cuts : Finset (ZMod n))
    (arcLen : ZMod n → ℕ) : ℕ :=
  2 * sigPar l g h j + rrPar l n H₁ H₂ cuts + 2 * g * ellMax cuts arcLen

def ePar (l n : ℕ) [NeZero n] (j g h : ℕ) (H₁ H₂ : ZMod n → ℕ) (cuts : Finset (ZMod n))
    (arcLen : ZMod n → ℕ) : ℕ :=
  2 * rrPar l n H₁ H₂ cuts + 4 * sigPar l g h j + 2 * initialExponentBound l n j g h H₁ H₂ cuts arcLen +
    2 * kapPar l g h (ellMax cuts arcLen)

def ThmEBound (C : ℝ) : Prop :=
  ∀ (l : ℕ), l.Prime → 5 ≤ l → ∀ (n : ℕ) [NeZero n] (j G S η h : ℕ) (ty : ZMod n → LT)
    (cuts : Finset (ZMod n)) (arcLen : ZMod n → ℕ) (H₁ H₂ : ZMod n → ℕ),
    CutsOK n j ty cuts arcLen → gPar G S η ≤ h →
    (∀ i, H₁ i ≤ 2 * h ∧ H₂ i ≤ 2 * h) →
    (∀ c ∈ cuts, ∀ k : ℕ, 1 ≤ k → k ≤ j →
      H₁ (c + (k : ZMod n)) ≤ 2 * G ∧ H₂ (c + (k : ZMod n)) ≤ 2 * G) →
    (ePar l n j (gPar G S η) h H₁ H₂ cuts arcLen : ℝ) ≤
      C * ((h : ℝ) / ((l : ℝ) - 1) ^ (j + 1) + (gPar G S η : ℝ) * ellMax cuts arcLen +
        Real.logb l h)

section Local

open Formalism.BasicNotions

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]

def JumpsAtE (T : LocLat G Qp LL O) {n : ℕ} (emb : ZMod n → (K₀ →ₐ[Qp] LL)) (i : ZMod n)
    (S : Set ℤ) : Prop :=
  ∀ τ : K →ₐ[Qp] LL, τ.comp (IsScalarTower.toAlgHom Qp K₀ K) = emb i → JumpsInV PD T.ρ τ S

def KindJumps (T : LocLat G Qp LL O) {n : ℕ} (emb : ZMod n → (K₀ →ₐ[Qp] LL)) (G S η : ℕ)
    (ty : ZMod n → LT) : Prop :=
  ∀ i : ZMod n, JumpsAtE PD T emb i ((ty i).win G S η)

def CrysLat (T : LocLat G Qp LL O) : Prop :=
  FiniteDimensional LL T.V ∧ IsModuleTopology LL T.V ∧ (∀ x, Continuous fun g => T.ρ g x) ∧
    IsCrys PD T.ρ

variable (LL O) in

def HodgeExact : Prop :=
  (∀ (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L), CrysLat PD T₁ → CrysLat PD T₂ → F.Onto →
    ∀ (τ : K →ₐ[Qp] LL) (a : ℤ), IsJumpV PD T₂.ρ τ a → IsJumpV PD T₁.ρ τ a) ∧
  (∀ (T₀ T₁ T₂ : LocLat G Qp LL O) (ι : LatHom T₀.L T₁.L) (π : LatHom T₁.L T₂.L),
    IsSESLat (Qp := Qp) ι π → CrysLat PD T₁ →
      CrysLat PD T₀ ∧ CrysLat PD T₂ ∧ ∀ (τ : K →ₐ[Qp] LL) (a : ℤ),
        IsJumpV PD T₁.ρ τ a ↔ IsJumpV PD T₀.ρ τ a ∨ IsJumpV PD T₂.ρ τ a) ∧
  (∀ T : LocLat G Qp LL O, (∀ g x, T.ρ g x = x) →
    ∀ (τ : K →ₐ[Qp] LL) (a : ℤ), IsJumpV PD T.ρ τ a → a = 0)

variable [Fintype (K →ₐ[Qp] LL)]

def ThmELiftAt (n : ℕ) [NeZero n] (emb : ZMod n → (K₀ →ₐ[Qp] LL))
    (v : AddValuation LL (WithTop ℚ)) : Prop :=
  Letters PD LL v emb → 5 ≤ PD.p →
  ∀ (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L),
    GoodCoeffs (K := K) (Qp := Qp) (LL := LL) (O := O) (V := T₁.V) →
    CrysLat PD T₁ → CrysLat PD T₂ → F.Onto →
    ∀ (j Gp S η h : ℕ) (ty : ZMod n → LT) (cuts : Finset (ZMod n)) (arcLen : ZMod n → ℕ)
      (Mb₁ hb₁ Mb₂ hb₂ : ZMod n → ℕ),
      KindJumps PD T₁ emb Gp S η ty →
      (∀ τ : K →ₐ[Qp] LL, JumpsInV PD T₁.ρ τ (Set.Icc (-(h : ℤ)) h)) →
      gPar Gp S η ≤ h → SizesOK (gPar Gp S η) S h ty →
      CutsOK n j ty cuts arcLen → ThickLe2 ty cuts arcLen →
      (∀ i, JumpsAtE PD T₁ emb i (Set.Icc (-(Mb₁ i : ℤ)) (hb₁ i))) →
      (∀ i, JumpsAtE PD T₂ emb i (Set.Icc (-(Mb₂ i : ℤ)) (hb₂ i))) →
      WordOK PD.p (initialExponentBound PD.p n j (gPar Gp S η) h (Mb₁ + hb₁) (Mb₂ + hb₂) cuts arcLen) ty cuts
        arcLen →
      F.LiftF PD (ePar PD.p n j (gPar Gp S η) h (Mb₁ + hb₁) (Mb₂ + hb₂) cuts arcLen)

open Classical in

def hCor {n : ℕ} (b w S η : ℕ) (sz : ZMod n → ℕ) : ℕ :=
  if ∃ i, b ≤ sz i ∧ sz i ≤ b + η then b + η + S else w + S + η

def CorAAt (n : ℕ) [NeZero n] (emb : ZMod n → (K₀ →ₐ[Qp] LL))
    (v : AddValuation LL (WithTop ℚ)) (C : ℝ) : Prop :=
  Letters PD LL v emb → 11 ≤ PD.p →
  ∀ (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L),
    GoodCoeffs (K := K) (Qp := Qp) (LL := LL) (O := O) (V := T₁.V) →
    CrysLat PD T₁ → CrysLat PD T₂ → F.Onto →
    ∀ (r b w S η j : ℕ) (typ : ZMod n → Bool) (sz : ZMod n → ℕ),
      finrank LL T₂.V = r → 1 ≤ j → j + 1 ≤ n →
      (∀ i, JumpsAtE PD T₁ emb i (if typ i then (LT.up (sz i)).win 0 S η
        else (LT.down (sz i)).win 0 S η)) →
      (∀ i, Thick b η sz i ∨ sz i ≤ w) →
      C * ((j : ℝ) + 1) * (((w + S + η : ℕ) : ℝ) + 1) ≤ b →
      Clusters j (Thick b η sz) →
      ColLeR PD F (C * ((n : ℝ) + 1) * r *
        ((hCor b w S η sz : ℝ) / ((PD.p : ℝ) - 1) ^ (j + 1) +
          (((w + S + η : ℕ) : ℝ) + 1) * ((j : ℝ) + 1) + Real.logb PD.p (hCor b w S η sz : ℝ)))

def BCAt {LL' O' : Type} [Field LL'] [Algebra Qp LL'] [TopologicalSpace LL'] [CommRing O'] [Algebra O' LL']
    (ι : LL →ₐ[Qp] LL') : Prop :=
  ∀ (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L),
    CrysLat PD T₁ → CrysLat PD T₂ → F.Onto →
    ∃ (T₁' T₂' : LocLat G Qp LL' O') (F' : LatHom T₁'.L T₂'.L),
      CrysLat PD T₁' ∧ CrysLat PD T₂' ∧ F'.Onto ∧
      (∀ (τ : K →ₐ[Qp] LL) (a : ℤ),
        (IsJumpV PD T₁'.ρ (ι.comp τ) a ↔ IsJumpV PD T₁.ρ τ a) ∧
        (IsJumpV PD T₂'.ρ (ι.comp τ) a ↔ IsJumpV PD T₂.ρ τ a)) ∧
      finrank LL' T₂'.V = finrank LL T₂.V ∧
      (∀ e : ℕ, F'.LiftF PD e → F.LiftF PD e) ∧
      (∀ x : ℝ, ColLeR PD F' x → ColLeR PD F x)

end Local

section Tools

open Formalism.BasicNotions TensorProduct

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

def qP : LetA O n := W.π₀ + ((PD.p : ℕ) : LetA O n)

def pS (s : ℕ) : LetA O n := (W.φA ^ s) (qP W)

def DDΔ (T : LocLat G Qp LL O) : Set (W.DD T) := {x | ∀ δ ∈ W.DelF, W.γD T δ x = x}

def InLetter (T : LocLat G Qp LL O) (c : ZMod n) (x : W.DD T) : Prop :=
  (letE c : LetA O n) • x = x

def mulSet (T : LocLat G Qp LL O) (a : LetA O n) (S : Submodule O (W.DD T)) : Set (W.DD T) :=
  {x | ∃ y ∈ S, x = a • y}

def IsPs (f : LetA O n) : Prop :=
  ∃ (k : ℕ → ℕ) (m : ℕ), f = ∏ s ∈ Finset.range m, pS W s ^ k s

def IsPiPs (f : LetA O n) : Prop := ∃ (a : ℕ) (g : LetA O n), IsPs W g ∧ f = W.π₀ ^ a * g

abbrev ZΔ (T : LocLat G Qp LL O) : Type := ↥(W.wachCocyclesDelta T)

def HerrCocycleAtLetter (T : LocLat G Qp LL O) (M : ℕ) (c : ZMod n) (x : ZΔ W T) : Prop :=
  InLetter W T c (x : W.DD T × W.DD T).1 ∧
    W.γD T W.gamK (x : W.DD T × W.DD T).1 - (x : W.DD T × W.DD T).1 ∈
      mulSet W T (W.π₀ ^ M) (W.NΔ T) ∧
    (x : W.DD T × W.DD T).2 ∈ mulSet W T (W.π₀ ^ M) (W.NΔ T)

def ToolsAlg : Prop :=
  (∃ u : LetA O n, IsUnit u ∧ W.φA W.π₀ = u * W.π₀ * qP W ^ (PD.p - 1)) ∧
  (∀ s : ℕ, ∃ (u : LetA O n) (P : Polynomial O), IsUnit u ∧ P.Monic ∧ P.natDegree = PD.p ^ s ∧
      (∀ k < PD.p ^ s, ((PD.p : ℕ) : O) ∣ P.coeff k) ∧ pS W s = u * Polynomial.aeval W.π₀ P) ∧
  (∀ s : ℕ, pS W s - ((PD.p : ℕ) : LetA O n) ∈ Ideal.span {W.π₀}) ∧
  (∀ s : ℕ, 1 ≤ s → pS W s - ((PD.p : ℕ) : LetA O n) ∈ Ideal.span {qP W})

def FilLev (T : LocLat G Qp LL O) (c : ZMod n) (s : ℕ) (u : ℤ) : Submodule LL (T.V ⊗[Qp] BdR) :=
  ((FilCris PD T.ρ u ⊓ DcrisL PD T.ρ (W.emb (c - (s : ZMod n)))).map
    ((φVB PD (LL := LL) (V := T.V) : Module.End LL (T.V ⊗[Qp] B)) ^ s)).map
      (ιV PD (LL := LL) (V := T.V))

def LevelMapHodgeFiltration : Prop :=
  ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → ∀ (c : ZMod n) (s : ℕ) (ζ : LL),
    IsPrimitiveRoot ζ (PD.p ^ (s + 1)) →
    (∀ (x : ↥(W.N T)) (k : ℤ), W.levN T c ζ x k ∈ FilLev W T c s (-k)) ∧
    ∀ (k : ℤ), ∀ w ∈ FilLev W T c s (-k), ∃ (x : ↥(W.N T)) (a : LL), a ≠ 0 ∧
      (∀ j < k, a • W.levN T c ζ x j ∈ FilLev W T c s (-j + 1)) ∧
      a • W.levN T c ζ x k - w ∈ FilLev W T c s (-k + 1)

def Sat : Prop :=
  ∀ (T : LocLat G Qp LL O) (f f' : LetA O n), IsCrys PD T.ρ → IsPiPs W f → IsPiPs W f' →
    ∀ x : W.DD T, x ∈ DDΔ W T → f' • x ∈ W.NΔ T →
      (∃ k : ℕ, ((PD.p : ℕ) : LetA O n) ^ k • x ∈ mulSet W T f (W.NΔ T)) →
      x ∈ mulSet W T f (W.NΔ T)

def F1 : Prop :=
  ∀ (h M : ℕ), h < (PD.p - 1) * M →
  (∀ (T : LocLat G Qp LL O), IsCrys PD T.ρ →
    (∀ τ : K →ₐ[Qp] LL, JumpsInV PD T.ρ τ (Set.Icc (-(h : ℤ)) h)) →
    (∀ x ∈ W.NΔ T, W.φD T (W.π₀ ^ M • x) ∈ mulSet W T (W.π₀ ^ M * qP W) (W.NΔ T)) ∧
    (∀ w ∈ mulSet W T (W.π₀ ^ M) (W.NΔ T), ∃! z : W.DD T,
      z ∈ mulSet W T (W.π₀ ^ M) (W.NΔ T) ∧ W.φD T z - z = w) ∧
    (∀ (c : ZMod n) (x : ZΔ W T), HerrCocycleAtLetter W T M c x →
      (x : W.DD T × W.DD T).1 ∈ mulSet W T (W.π₀ ^ M) (W.NΔ T) → W.clK T x = 0) ∧
    (∀ (c : ZMod n) (x₁ x₂ x₃ : ZΔ W T), HerrCocycleAtLetter W T M c x₁ → HerrCocycleAtLetter W T M c x₂ → HerrCocycleAtLetter W T M c x₃ →
      (x₃ : W.DD T × W.DD T).1 = (x₁ : W.DD T × W.DD T).1 + (x₂ : W.DD T × W.DD T).1 →
      W.clK T x₃ = W.clK T x₁ + W.clK T x₂)) ∧
  (∀ (T T' : LocLat G Qp LL O) (F : LatHom T.L T'.L), IsCrys PD T.ρ → IsCrys PD T'.ρ →
    (∀ τ : K →ₐ[Qp] LL, JumpsInV PD T.ρ τ (Set.Icc (-(h : ℤ)) h)) →
    (∀ τ : K →ₐ[Qp] LL, JumpsInV PD T'.ρ τ (Set.Icc (-(h : ℤ)) h)) →
    ∀ (c : ZMod n) (x : ZΔ W T) (x' : ZΔ W T'), HerrCocycleAtLetter W T M c x → HerrCocycleAtLetter W T' M c x' →
      (x' : W.DD T' × W.DD T').1 = W.map F (x : W.DD T × W.DD T).1 →
      W.clK T' x' = F.H1map (W.clK T x))

def F2 : Prop :=
  ∀ (h M : ℕ), h < (PD.p - 1) * M →
  ∀ (T : LocLat G Qp LL O), IsCrys PD T.ρ →
    (∀ τ : K →ₐ[Qp] LL, JumpsInV PD T.ρ τ (Set.Icc (-(h : ℤ)) h)) →
    ∀ (c : ZMod n) (x : ZΔ W T), HerrCocycleAtLetter W T M c x →
      (∃ Λ : LetA O n, IsPs W Λ ∧ Λ • (x : W.DD T × W.DD T).1 ∈ W.NΔ T) →
      W.clK T x ∈ latticeFiniteCohomology PD T.L

def PPO (l : ℕ) (χ : Oˣ) (ell : ℕ) (JS : Finset ℤ) : Polynomial O :=
  (∏ i ∈ JS.erase 0, (Polynomial.X ^ (l ^ ell) -
      Polynomial.C ((χ ^ (i * (l : ℤ) ^ ell) : Oˣ) : O))) *
    ∑ k ∈ Finset.range (l ^ ell), Polynomial.X ^ k

def KillerMod : Prop :=
  ∀ (T : LocLat G Qp LL O) (c : ZMod n) (γ : W.Gam) (χ : Oˣ) (ell : ℕ) (JS : Finset ℤ)
    (w : W.DD T), IsCrys PD T.ρ →
    w ∈ DDΔ W T → InLetter W T c w → W.γD T γ w - w ∈ mulSet W T W.π₀ (W.NΔ T) →
    Polynomial.aeval (W.γD T γ) (PPO PD.p χ ell JS) w - (PPO PD.p χ ell JS).eval 1 • w ∈
      mulSet W T W.π₀ (W.NΔ T)

end Tools

section Theory

open Formalism.BasicNotions Formalism.BasicNotions.Loc

def LiftingTheoremLocalTheory (Th : LocTheory) (C : ℝ) : Prop :=
  (∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (n : ℕ) [NeZero n]
      (emb : ZMod n → (↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1)),
      haveI : FiniteDimensional ℚ_[l] ↥K.1 := K.2
      letI : Fintype (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) := Fintype.ofFinite _
      ThmELiftAt ((Th l).PD K) (O := ↥(OL LL)) n emb ((Th l).v LL)) ∧
    ThmEBound C

def LocalCorollaryLifting (Th : LocTheory) (C : ℝ) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (n : ℕ) [NeZero n]
    (emb : ZMod n → (↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1)),
    haveI : FiniteDimensional ℚ_[l] ↥K.1 := K.2
    letI : Fintype (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) := Fintype.ofFinite _
    CorAAt ((Th l).PD K) (O := ↥(OL LL)) n emb ((Th l).v LL) C

def admBC (Th : LocTheory) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K LL LL' : FinExt l) (hLL : LL.1 ≤ LL'.1),
    BCAt ((Th l).PD K) (LL := ↥LL.1) (O := ↥(OL LL)) (O' := ↥(OL LL'))
      (IntermediateField.inclusion hLL)

def HodgeExactAllExtensions (Th : LocTheory) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l), HodgeExact ((Th l).PD K) ↥LL.1 ↥(OL LL)

end Theory

section Record

open Formalism.BasicNotions Formalism.BasicNotions.Loc

def Conclusion1 (D : D7) (C : ℝ) : Prop := LiftingTheoremLocalTheory D.loc C

def Conclusion2 (D : D7) (C : ℝ) : Prop := LocalCorollaryLifting D.loc C

def adm1 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) : Prop := Formalism.MainNotions.DeltaInvariantLattices.UsedLocalConclusion D HW F Cm

def adm2 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.LiftingTheory.ConclusionL D HW F

def adm3 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.LiftingTheory.ConclusionW D HW F

def ArchimedeanSignatureMatching (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C : ℝ) : Prop := Formalism.MainNotions.LiftingTheory.WachResultConstant D HW F C

def adm5 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.LiftingTheory.ConclusionH D HW F

def adm6 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.LiftingTheory.ExistsUnitClasses D HW F

def AtCaseA (P : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (_ : CaseA K LL), Prop) :
    Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (h : CaseA K LL), 5 ≤ l → P l K LL h

def adm7 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) : Prop :=
  AtCaseA fun l _ K LL h => ToolsAlg ((HW l).W K 1 LL h.2.2) ∧ LevelMapHodgeFiltration ((HW l).W K 1 LL h.2.2)

def adm8 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := AtCaseA fun l _ K LL h => Sat ((HW l).W K 1 LL h.2.2)

def adm9 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := AtCaseA fun l _ K LL h => F1 ((HW l).W K 1 LL h.2.2)

def adm10 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := AtCaseA fun l _ K LL h => F2 ((HW l).W K 1 LL h.2.2)

def adm11 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  Formalism.WindowSums.KillerVal ∧ Formalism.WindowSums.KillerKills ∧
    AtCaseA fun l _ K LL h => KillerMod ((HW l).W K 1 LL h.2.2)

def adm12 (D : D7) : Prop := Formalism.MainNotions.LocalTheoryWindows.H1fGeneratorBoundAll D.loc

def adm13 (D : D7) : Prop := admBC D.loc

def adm14 (D : D7) : Prop := HodgeExactAllExtensions D.loc

def adm15 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.DeltaInvariantLattices.ConclusionE D HW F

def adm16 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.LiftingTheory.adm17 D HW F ∧ Formalism.MainNotions.LiftingTheory.adm18 D HW F

def admitted (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (C : ℝ) : Prop :=
  adm1 D HW F Cm ∧ adm2 D HW F ∧ adm3 D HW F ∧ ArchimedeanSignatureMatching D HW F C ∧ adm5 D HW F ∧ adm6 D HW F ∧ adm7 D HW F Cm ∧ adm8 D HW F ∧ adm9 D HW F ∧
    adm10 D HW F ∧ adm11 D HW F ∧ adm12 D ∧ adm13 D ∧ adm14 D ∧ adm15 D HW F ∧ adm16 D HW F

def Stmt (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (C C₁ C₂ : ℝ) : Prop :=
  admitted D HW F Cm C → Conclusion1 D C₁ ∧ Conclusion2 D C₂

def RealisationStatementAll : Prop :=
  ∃ C₁ C₀ : ℝ, ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (C : ℝ), admitted D HW F Cm C → Conclusion1 D C₁ ∧ ∀ C₂ : ℝ, C₀ ≤ C₂ → Conclusion2 D C₂

theorem closed_form_iff_threshold_form : RealisationStatementAll ↔ ∃ C₁ C₀ : ℝ, ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (C C₂ : ℝ), C₀ ≤ C₂ → Stmt D HW F Cm C C₁ C₂ := by
  constructor
  · rintro ⟨C₁, C₀, h⟩
    exact ⟨C₁, C₀, fun D HW F Cm C C₂ hC₂ hA =>
      ⟨(h D HW F Cm C hA).1, (h D HW F Cm C hA).2 C₂ hC₂⟩⟩
  · rintro ⟨C₁, C₀, h⟩
    exact ⟨C₁, C₀, fun D HW F Cm C hA =>
      ⟨(h D HW F Cm C C₀ le_rfl hA).1, fun C₂ hC₂ => (h D HW F Cm C C₂ hC₂ hA).2⟩⟩

end Record

end Formalism.MainNotions.WachCoordinates
