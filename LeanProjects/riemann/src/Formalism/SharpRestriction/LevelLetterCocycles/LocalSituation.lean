import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.WeaklyAdmissibleFiltrations.StatementTor
import Formalism.GaloisCohomology.LocalTateDualityK

noncomputable section

namespace Formalism.MainNotions.LocalSituation

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Module TensorProduct

def vZ (l : ℕ) (z : ℤ) : ℕ := padicValInt l z

def n0 (l H0 : ℕ) : ℕ := sInf {n : ℕ | H0 ≤ l ^ n * (l - 1)}

def mN (l s H0 : ℕ) : ℕ := 2 * s + n0 l H0 + 1

def rI (l m : ℕ) (U : Set ℤ) (i : ℤ) : ℕ :=
  ∑ᶠ (u : ℤ) (_ : u ∈ U) (_ : u ≠ i), (m + vZ l (u - i))

def cLL (l m vdeg : ℕ) (U : Set ℤ) (a b : ℤ) : ℕ :=
  vdeg + ∑ i ∈ Finset.Ico a b, (2 + max 1 (rI l m U i))

def cTB (l s e gK c : ℕ) : ℕ :=
  c + (e + 2) * s + padicValNat l e + e / (l - 1) + 1 + (s + padicValNat l (e + 1)) + gK

structure Sit where
  G : Type
  [grp : Group G]
  [topG : TopologicalSpace G]
  Qp : Type
  K₀ : Type
  K : Type
  [fQp : Field Qp]
  [fK₀ : Field K₀]
  [fK : Field K]
  [a1 : Algebra Qp K₀]
  [a2 : Algebra Qp K]
  [a3 : Algebra K₀ K]
  [t1 : IsScalarTower Qp K₀ K]
  B : Type
  BdR : Type
  [rB : CommRing B]
  [rdR : CommRing BdR]
  [aQB : Algebra Qp B]
  [aKB : Algebra K₀ B]
  [tB : IsScalarTower Qp K₀ B]
  [aQdR : Algebra Qp BdR]
  [unramifiedBaseDeRham : Algebra K₀ BdR]
  [aKdR : Algebra K BdR]
  [deRhamFirstCompat : IsScalarTower Qp K BdR]
  [deRhamSecondCompat : IsScalarTower K₀ K BdR]
  [deRhamThirdCompat : IsScalarTower Qp K₀ BdR]
  PD : PeriodData G Qp K₀ K B BdR
  LL : Type
  [fLL : Field LL]
  [aLL : Algebra Qp LL]
  [topLL : TopologicalSpace LL]
  O : Type
  [rO : CommRing O]
  [aO : Algebra O LL]
  v : AddValuation LL (WithTop ℚ)
  n : ℕ
  W : LocWach PD LL O v n
  RA : Type
  RW : Type
  [rRA : CommRing RA]
  [rRW : CommRing RW]
  [aRA : Algebra O RA]
  [aRW : Algebra O RW]
  inclR : RA →ₐ[O] RW
  φR : RW →ₐ[O] RW
  gR : G → (RW →ₐ[O] RW)
  πA : RA
  degKj : ℕ → ℕ
  degK : ℕ
  IK : Subgroup G

attribute [instance] Sit.grp Sit.topG Sit.fQp Sit.fK₀ Sit.fK Sit.a1 Sit.a2 Sit.a3 Sit.t1
  Sit.rB Sit.rdR Sit.aQB Sit.aKB Sit.tB Sit.aQdR Sit.unramifiedBaseDeRham Sit.aKdR Sit.deRhamFirstCompat Sit.deRhamSecondCompat
  Sit.deRhamThirdCompat Sit.fLL Sit.aLL Sit.topLL Sit.rO Sit.aO Sit.rRA Sit.rRW Sit.aRA Sit.aRW

def sit (LT : LocTheory) (HW : HWOf LT) (l : ℕ) [Fact l.Prime] (AI : LocAinf l (LT l)) (K : FinExt l)
    (s : ℕ) (LL : FinExt l) (h : Good K s LL) : Sit where
  G := ↥(GK K)
  Qp := ℚ_[l]
  K₀ := ↥(K0 K)
  K := ↥K.1
  B := (LT l).R.B
  BdR := (LT l).R.BdR
  PD := (LT l).PD K
  LL := ↥LL.1
  O := ↥(OL LL)
  v := (LT l).v LL
  n := Module.finrank ℚ_[l] ↥(K0 K)
  W := (HW l).W K s LL h
  RA := RA LL
  RW := RW LL
  inclR := inclR LL
  φR := φRW LL
  gR g := AI.gRW LL (g : GQ l)
  πA := (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (WittVector.teichmuller l (AI.εroot s) - 1)
  degKj j := Module.finrank ℚ_[l] ↥(Ks K j)
  degK := Module.finrank ℚ_[l] ↥K.1
  IK := IK K

section Local

variable (S : Sit)

abbrev Sit.Comparison₂ : Type 1 := EtTie S.W S.RA S.RW S.inclR S.φR S.gR S.πA

variable (E : S.Comparison₂)

abbrev ell : ℕ := S.PD.p

def vdegMs (m : ℕ) : ℕ := padicValNat (ell S) (S.degKj m) - padicValNat (ell S) (S.degKj S.W.s)

def gK : ℕ := padicValNat (ell S) (S.degKj S.W.s) - padicValNat (ell S) S.degK

def Jset (Y : LocLat S.G S.Qp S.LL S.O) : Set ℤ :=
  {a | DdR S.PD Y.ρ ⊓ FilV S.PD (LL := S.LL) (V := Y.V) (a + 1) ≠
      DdR S.PD Y.ρ ⊓ FilV S.PD (LL := S.LL) (V := Y.V) a}

def IsCrysOn (H : Subgroup S.G) (Y : LocLat S.G S.Qp S.LL S.O) : Prop :=
  finrank S.LL ↥(⨅ g : H, LinearMap.ker (actVB S.PD Y.ρ (g : S.G) - LinearMap.id)) =
    finrank S.Qp S.K₀ * finrank S.LL Y.V

def NBasis (Y : LocLat S.G S.Qp S.LL S.O) (N : Submodule (LetA S.O S.n) (S.W.DD Y)) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (b : Basis ι (LetA S.O S.n) ↥N),
    LinearIndependent S.RW (fun i => E.jD Y (b i : S.W.DD Y)) ∧
    Submodule.span S.RW (Set.range fun i => E.jD Y (b i : S.W.DD Y)) = ⊤

def phiSpan (Y : LocLat S.G S.Qp S.LL S.O) (N : Submodule (LetA S.O S.n) (S.W.DD Y)) :
    Submodule (LetA S.O S.n) (S.W.DD Y) :=
  Submodule.span (LetA S.O S.n) (S.W.φD Y '' (N : Set (S.W.DD Y)))

theorem phiSpan_rec {S : Sit} (Y : LocLat S.G S.Qp S.LL S.O) : phiSpan S Y (S.W.N Y) = S.W.φpull Y := rfl

def WClauses (Y : LocLat S.G S.Qp S.LL S.O) (M0 h0 : ℕ) (N : Submodule (LetA S.O S.n) (S.W.DD Y)) :
    Prop :=
  NBasis S E Y N ∧
  (∀ x ∈ N, S.W.Q ^ M0 • S.W.φD Y x ∈ N) ∧
  (∀ y ∈ N, S.W.Q ^ h0 • y ∈ phiSpan S Y N) ∧
  (∀ g ∈ S.W.GKs, ∀ x ∈ N, S.W.γD Y (S.W.resΓ g) x ∈ N) ∧
  (∀ g ∈ S.W.GKs, ∀ x ∈ N, S.W.γD Y (S.W.resΓ g) x - x ∈
      (Ideal.span {(letπ : LetA S.O S.n)}) • N) ∧
  (∀ f : LatHom Y.L Y.L, ∀ x ∈ N, S.W.map f x ∈ N)

def HypW (Y : LocLat S.G S.Qp S.LL S.O) (M0 h0 : ℕ) : Prop :=
  IsCrysOn S S.W.GKs Y ∧ (∀ a ∈ Jset S Y, -(M0 : ℤ) ≤ a ∧ a ≤ h0) ∧
  ∃ N : Submodule (LetA S.O S.n) (S.W.DD Y), WClauses S E Y M0 h0 N

theorem HypW_of_rec {S : Sit} {E : S.Comparison₂} {Y : LocLat S.G S.Qp S.LL S.O} {M0 h0 : ℕ}
    (hc : IsCrysOn S S.W.GKs Y) (hj : ∀ a ∈ Jset S Y, -(M0 : ℤ) ≤ a ∧ a ≤ h0)
    (hN : WClauses S E Y M0 h0 (S.W.N Y)) : HypW S E Y M0 h0 :=
  ⟨hc, hj, _, hN⟩

def cTBY (Y : LocLat S.G S.Qp S.LL S.O) (M0 h0 e : ℕ) : ℕ :=
  cTB (ell S) S.W.s e (gK S)
    (cLL (ell S) (mN (ell S) S.W.s (M0 + h0)) (vdegMs S (mN (ell S) S.W.s (M0 + h0))) (Jset S Y)
      0 ((e : ℤ) + 1))

def TBat : Prop :=
  ∀ (e M0 h0 : ℕ) (Yt Y Z Ve : LocLat S.G S.Qp S.LL S.O) (ι : LatHom Y.L Yt.L) (π : LatHom Yt.L Z.L),
    IsSESLat (Qp := S.Qp) ι π →
    finrank S.LL Z.V = 1 → (∀ g x, Z.ρ g x = x) →
    finrank S.LL Ve.V = 1 →
    (∀ g x, Ve.ρ g x = ((algebraMap S.Qp S.LL (S.PD.χ g : S.Qp))⁻¹) ^ e • x) →
    IsCrysOn S S.W.GKs Yt → HypW S E Y M0 h0 →
    ∀ yt ∈ Yt.L.T, (∀ z ∈ Z.L.T, ∃ a : S.O, z = a • π.f yt) →
    ∀ φ : ↥Y.L.T →ₗ[S.O] (Ve.V ⧸ Ve.L.T), (∀ g y, φ (actT Y.L g y) = actD Ve.L g (φ y)) →
    ∀ f : S.G → ↥Y.L.T, (∀ g, ι.f (f g : Y.V) = Yt.ρ g yt - yt) →
      (fun g => ((ell S : S.O) ^ cTBY S Y M0 h0 e) • φ (f g)) ∈ HfD S.PD Ve.L

def TBeAt : Prop :=
  ∀ (e : ℕ) (Ve : LocLat S.G S.Qp S.LL S.O), finrank S.LL Ve.V = 1 →
    (∀ g x, Ve.ρ g x = ((algebraMap S.Qp S.LL (S.PD.χ g : S.Qp))⁻¹) ^ e • x) →
    (∀ n : ℕ, Module.length S.O ↥(Submodule.torsionBy S.O (DivisibleCohomology Ve.L ⧸ divisibleFiniteCohomology S.PD Ve.L)
        ((ell S : S.O) ^ n)) ≤ (((finrank S.Qp S.K + 1) * n : ℕ) : ℕ∞) * lenOl S.PD (O := S.O)) ∧
    (0 < e → HfD S.PD Ve.L = BD Ve.L) ∧
    (e = 0 → ∀ c : S.G → Ve.V ⧸ Ve.L.T, c ∈ HfD S.PD Ve.L ↔
      (c ∈ divisibleCocycles Ve.L ∧ ∃ x, ∀ g ∈ S.IK, c g = actD Ve.L g x - x))

theorem TBeAt.len {S : Sit} (h : TBeAt S) (e n : ℕ) (Ve : LocLat S.G S.Qp S.LL S.O)
    (h1 : finrank S.LL Ve.V = 1)
    (hχ : ∀ g x, Ve.ρ g x = ((algebraMap S.Qp S.LL (S.PD.χ g : S.Qp))⁻¹) ^ e • x) :
    Module.length S.O ↥(Submodule.torsionBy S.O (DivisibleCohomology Ve.L ⧸ divisibleFiniteCohomology S.PD Ve.L) ((ell S : S.O) ^ n)) ≤
      (((finrank S.Qp S.K + 1) * n : ℕ) : ℕ∞) * lenOl S.PD (O := S.O) :=
  (h e Ve h1 hχ).1 n

def c0 (T : LocLat S.G S.Qp S.LL S.O) (τ : S.K →ₐ[S.Qp] S.LL) (M0 h0 : ℕ) : ℕ :=
  2 + ∑ᶠ (u : ℤ) (_ : IsJumpV S.PD T.ρ τ u), (mN (ell S) S.W.s (M0 + h0) + vZ (ell S) u)

def H0at : Prop :=
  ∀ (M0 h0 : ℕ) (T : LocLat S.G S.Qp S.LL S.O) (τ : S.K →ₐ[S.Qp] S.LL),
    HypW S E T M0 h0 → ¬ IsJumpV S.PD T.ρ τ 0 →
    ∀ x : T.V ⧸ T.L.T, (∀ g, actD T.L g x = x) → ((ell S : S.O) ^ c0 S T τ M0 h0) • x = 0

def HerrAat : Prop :=
  (ell S = 2 → ∃ i : S.K, i ^ 2 = -1) →
  ∀ T : LocLat S.G S.Qp S.LL S.O,
    Function.Surjective (S.W.clK T) ∧
    (∀ pr : S.W.wachCocyclesDelta T, S.W.clK T pr = 0 ↔ ∃ m, (∀ δ ∈ S.W.DelF, S.W.γD T δ m = m) ∧
      (pr : S.W.DD T × S.W.DD T) = (S.W.φD T m - m, S.W.γD T S.W.gamK m - m)) ∧
    ∀ (T' : LocLat S.G S.Qp S.LL S.O) (f : LatHom T.L T'.L) (pr : S.W.wachCocyclesDelta T) (pr' : S.W.wachCocyclesDelta T'),
      (pr' : S.W.DD T' × S.W.DD T') = (S.W.map f (pr : S.W.DD T × S.W.DD T).1,
        S.W.map f (pr : S.W.DD T × S.W.DD T).2) →
      S.W.clK T' pr' = f.H1map (S.W.clK T pr)

def HerrAsat : Prop :=
  ∀ T : LocLat S.G S.Qp S.LL S.O,
    Function.Surjective (S.W.cl T) ∧
      ∀ w : ↥(S.W.divisibleCocycles T), S.W.cl T w = 0 ↔
        ∃ m : S.W.DD T, (w : S.W.DD T × S.W.DD T) = (S.W.φD T m - m, S.W.γ T m - m)

def HerrBat : Prop :=
  ∀ (M0 h0 : ℕ) (T : LocLat S.G S.Qp S.LL S.O),
    NBasis S E T (S.W.N T) →
    (∀ x ∈ S.W.N T, S.W.Q ^ M0 • S.W.φD T x ∈ S.W.N T) →
    (∀ y ∈ S.W.N T, S.W.Q ^ h0 • y ∈ S.W.φpull T) →
    (∀ x ∈ S.W.N T, ∃ x' ∈ S.W.N T, S.W.γ T x - x = (letπ : LetA S.O S.n) • x') →
      (∀ x ∈ S.W.N T, ∃ x' ∈ S.W.N T, S.W.γ T x - x = S.W.X • x') ∧
      ∀ pr : S.W.divisibleCocycles T, S.W.Q ^ M0 • (pr : S.W.DD T × S.W.DD T).1 ∈ S.W.N T →
        (∃ n' ∈ S.W.N T, (pr : S.W.DD T × S.W.DD T).2 = S.W.X • n') →
        S.W.cl T pr = 0 →
        ∃ m ∈ S.W.N T, (pr : S.W.DD T × S.W.DD T) = (S.W.φD T m - m, S.W.γ T m - m)

def Hker : Subgroup S.G := S.W.resΓ.ker

def DDeq (AT : ∀ T : LocLat S.G S.Qp S.LL S.O, Submodule S.O (TW S.RW T)) : Prop :=
  ∀ T, Set.range (E.jD T) =
    {x | x ∈ AT T ∧ ∀ g : S.G, g ∈ Hker S → TWact (S.gR g) T g x = x}

def FNat (AT : ∀ T : LocLat S.G S.Qp S.LL S.O, Submodule S.O (TW S.RW T)) : Prop :=
  ∀ T : LocLat S.G S.Qp S.LL S.O,
    (∀ x ∈ AT T, ∃ b ∈ AT T, TWmap S.φR T b - b = x) ∧
    (∀ b : TW S.RW T, TWmap S.φR T b = b → ∃ t : ↥T.L.T, b = (1 : S.RW) ⊗ₜ[S.O] t) ∧
    ∀ c : ↥(latticeCocycles (resLat T (Hker S))), ∃ b ∈ AT T, ∀ (σ : ↥(Hker S)) (t : ↥T.L.T),
      (t : T.V) = (c : ↥(Hker S) → T.V) σ →
        (1 : S.RW) ⊗ₜ[S.O] t = TWact (S.gR σ) T (σ : S.G) b - b

def Htl (T : LocLat S.G S.Qp S.LL S.O) : Submodule S.O (TW S.RW T) where
  carrier := {x | ∀ g : S.G, g ∈ Hker S → TWact (S.gR g) T g x = x}
  add_mem' := by
    intro a b ha hb g hg
    simp only [Set.mem_setOf_eq, map_add, ha g hg, hb g hg]
  zero_mem' := by
    intro g _
    simp only [map_zero]
  smul_mem' := by
    intro c x hx g hg
    simp only [Set.mem_setOf_eq, map_smul, hx g hg]

def FNatW : Prop := FNat S (fun _ => ⊤)

def DecW : Prop :=
  ∀ T : LocLat S.G S.Qp S.LL S.O,
    (∀ y ∈ Htl S T, ∃ d ∈ Htl S T, y - (TWmap S.φR T d - d) ∈ LinearMap.range (E.jD T)) ∧
    (∀ z ∈ Htl S T, TWmap S.φR T z - z ∈ LinearMap.range (E.jD T) → z ∈ LinearMap.range (E.jD T))

end Local

section BK

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] [TopologicalSpace Qp]
    (PD : PeriodData G Qp K₀ K B BdR)

def bkADim : Prop :=
  ∀ (LL : Type) [Field LL] [Algebra Qp LL] [TopologicalSpace LL] (O : Type) [CommRing O]
    [Algebra O LL], GoodO (Qp := Qp) LL O →
  ∀ A : GRep G Qp LL O, IsDR PD A.ρ →
    (finrank LL (FiniteCohomology PD A.ρ) : ℤ) = finrank LL ↥(H0V A.ρ) +
      ((finrank LL ↥(DdR PD A.ρ) : ℤ) - finrank LL ↥(DdR PD A.ρ ⊓ FilV PD (LL := LL) (V := A.V) 0))

def bkARightExact : Prop :=
  ∀ (LL : Type) [Field LL] [Algebra Qp LL] [TopologicalSpace LL] (O : Type) [CommRing O]
    [Algebra O LL], GoodO (Qp := Qp) LL O →
  ∀ (A A' : GRep G Qp LL O) (f : A.V →ₗ[LL] A'.V), (∀ g x, f (A.ρ g x) = A'.ρ g (f x)) →
    Function.Surjective f → IsCrys PD A.ρ → IsCrys PD A'.ρ →
    ∀ c' ∈ finiteCocycles PD A'.ρ, ∃ c ∈ finiteCocycles PD A.ρ, (fun g => f (c g)) - c' ∈ B1 A'.ρ

def liftQ {LL O V : Type} [Field LL] [CommRing O] [Algebra O LL] [AddCommGroup V] [Module LL V]
    [Module O V] [IsScalarTower O LL V] {ρ : Representation LL G V} (L : Lattice (O := O) ρ)
    (I : Submodule O ↥L.T) (c : ↥L.T ⧸ I) : V :=
  ((Submodule.Quotient.mk_surjective I c).choose : V)

def bkC : Prop :=
  ∀ (LL : Type) [Field LL] [Algebra Qp LL] [TopologicalSpace LL] (O : Type) [CommRing O]
    [Algebra O LL], GoodO (Qp := Qp) LL O →
  ∀ L1 : Lattice (O := O) (charRep (cycLL PD LL)), L1.T = LinearMap.range (Algebra.linearMap O LL) →
  ∀ (A A' : GRep G Qp LL O) (LA : Lattice (O := O) A.ρ) (LA' : Lattice (O := O) A'.ρ)
    (P : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDR PD A.ρ → IsDualLat1 PD LA LA' P →
  ∀ (ϖ : O), Irreducible ϖ → ∀ (r : ℕ)
    (hI : StableSub LA (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T))
    (hI' : StableSub LA' (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA'.T)),
    let cup := fun (c : G → ↥LA.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T))
        (c' : G → ↥LA'.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA'.T)) (x : G × G) =>
      (algebraMap O LL ϖ)⁻¹ ^ r * P (liftQ LA _ (c x.1)) (A'.ρ x.1 (liftQ LA' _ (c' x.2)))
    (∀ c ∈ quotientCocycles LA _ hI, (c ∈ HfQ PD LA _ hI ↔ ∀ c' ∈ HfQ PD LA' _ hI', CobO PD L1 (cup c c'))) ∧
    (∀ c' ∈ quotientCocycles LA' _ hI', (c' ∈ HfQ PD LA' _ hI' ↔ ∀ c ∈ HfQ PD LA _ hI, CobO PD L1 (cup c c')))

def bkAll : Prop := bkACore PD ∧ bkADim PD ∧ bkARightExact PD ∧ bkBCore PD ∧ bkC PD

def TateFilteredInvariants : Prop :=
  ∀ (LL : Type) [Field LL] [Algebra Qp LL] [TopologicalSpace LL] (O : Type) [CommRing O]
    [Algebra O LL], GoodO (Qp := Qp) LL O →
  ∀ A : GRep G Qp LL O, IsDR PD A.ρ → ∀ (a b : ℤ) (z : A.V ⊗[Qp] BdR),
    z ∈ FilV PD (LL := LL) (V := A.V) a →
    (∀ g, actVdR PD A.ρ g z - z ∈ FilV PD (LL := LL) (V := A.V) b) →
    ∃ w ∈ DdR PD A.ρ ⊓ FilV PD (LL := LL) (V := A.V) a, z - w ∈ FilV PD (LL := LL) (V := A.V) b

def contCore : Prop :=
  ∀ (LL : Type) [Field LL] [Algebra Qp LL] [TopologicalSpace LL] (O : Type) [CommRing O]
    [Algebra O LL], GoodO (Qp := Qp) LL O →
  ∀ (A : GRep G Qp LL O) (k : ℕ) (x : Fin k → A.V ⊗[Qp] B) (β : Fin k → G → LL),
    (∀ i, Continuous (β i)) → ∀ (x' : A.V ⊗[Qp] B) (f : G → A.V),
    (∀ g, f g ⊗ₜ[Qp] (1 : B) = ∑ i, β i g • x i + (actVB PD A.ρ g x' - x')) → Continuous f

def fontCore : Prop :=
  ∀ (LL : Type) [Field LL] [Algebra Qp LL] [TopologicalSpace LL] (O : Type) [CommRing O]
    [Algebra O LL], GoodO (Qp := Qp) LL O →
  ∀ A : GRep G Qp LL O,
    (Module.Finite LL ↥(Dcris PD A.ρ) ∧
      finrank LL ↥(Dcris PD A.ρ) ≤ finrank Qp K₀ * finrank LL A.V) ∧
    (Module.Finite LL ↥(DdR PD A.ρ) ∧ finrank LL ↥(DdR PD A.ρ) ≤ finrank Qp K * finrank LL A.V) ∧
    (IsCrys PD A.ρ → IsDR PD A.ρ)

def filDualCore : Prop :=
  ∀ (LL : Type) [Field LL] [Algebra Qp LL] [TopologicalSpace LL] (O : Type) [CommRing O]
    [Algebra O LL], GoodO (Qp := Qp) LL O →
  ∀ (A A' : GRep G Qp LL O) (P : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDR PD A.ρ →
    IsDual1 PD A.ρ A'.ρ P →
    finrank LL ↥(DdR PD A'.ρ ⊓ FilV PD (LL := LL) (V := A'.V) 0) +
      finrank LL ↥(DdR PD A.ρ ⊓ FilV PD (LL := LL) (V := A.V) 0) = finrank LL ↥(DdR PD A.ρ)

end BK

section Xi

variable {O G WC : Type} [CommRing O] [Group G] [CommRing WC] [Algebra O WC]
  (AA : Subalgebra O WC) (act : G →* (WC ≃ₐ[O] WC)) (ξ : WCˣ)

def Mxi (a : ℤ) : Submodule O WC :=
  (Subalgebra.toSubmodule AA).map (LinearMap.mulLeft O ((ξ ^ a : WCˣ) : WC))

def XiOK : Prop :=
  (∀ g, ∀ x ∈ AA, act g x ∈ AA) ∧ (ξ : WC) ∈ AA ∧
    ∀ g, ∃ u : WCˣ, (u : WC) ∈ AA ∧ ((u⁻¹ : WCˣ) : WC) ∈ AA ∧ act g ξ = u * ξ

variable {AA act ξ}

theorem zpow_mem (h : XiOK AA act ξ) (u : WCˣ) (hu : (u : WC) ∈ AA) (hu' : ((u⁻¹ : WCˣ) : WC) ∈ AA) :
    ∀ a : ℤ, ((u ^ a : WCˣ) : WC) ∈ AA := by
  intro a
  induction a using Int.induction_on with
  | zero => simpa using AA.one_mem
  | succ k ih =>
    rw [zpow_add_one, Units.val_mul]; exact AA.mul_mem ih hu
  | pred k ih =>
    rw [zpow_sub_one, Units.val_mul]; exact AA.mul_mem ih hu'

theorem act_inv (g : G) (u : WCˣ) (hg : act g ξ = u * ξ) :
    act g ((ξ⁻¹ : WCˣ) : WC) = (((u * ξ)⁻¹ : WCˣ) : WC) := by
  have h2 : act g ((ξ⁻¹ : WCˣ) : WC) * ((u * ξ : WCˣ) : WC) = 1 := by
    rw [Units.val_mul, ← hg, ← map_mul, Units.inv_mul, map_one]
  calc act g ((ξ⁻¹ : WCˣ) : WC)
      = act g ((ξ⁻¹ : WCˣ) : WC) * (((u * ξ : WCˣ) : WC) * (((u * ξ)⁻¹ : WCˣ) : WC)) := by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
    _ = (((u * ξ)⁻¹ : WCˣ) : WC) := by rw [← mul_assoc, h2, one_mul]

theorem act_zpow (g : G) (a : ℤ) (u : WCˣ) (hg : act g ξ = u * ξ) :
    act g ((ξ ^ a : WCˣ) : WC) = (((u * ξ) ^ a : WCˣ) : WC) := by
  induction a using Int.induction_on with
  | zero => simp
  | succ k ih =>
    rw [zpow_add_one, zpow_add_one, Units.val_mul, Units.val_mul, map_mul, ih, hg]
    simp only [Units.val_mul]
  | pred k ih =>
    rw [zpow_sub_one, zpow_sub_one, Units.val_mul, Units.val_mul, map_mul, ih, act_inv g u hg]

theorem Mxi_stable (h : XiOK AA act ξ) (g : G) (a : ℤ) :
    ∀ x ∈ Mxi AA ξ a, act g x ∈ Mxi AA ξ a := by
  rintro x ⟨y, hy, rfl⟩
  obtain ⟨u, hu, hu', hg⟩ := h.2.2 g
  refine ⟨((u ^ a : WCˣ) : WC) * act g y, AA.mul_mem (zpow_mem h u hu hu' a) (h.1 g y hy), ?_⟩
  simp only [LinearMap.mulLeft_apply, map_mul]
  rw [act_zpow g a u hg, mul_zpow, Units.val_mul]
  ring

theorem Mxi_anti (h : XiOK AA act ξ) {a b : ℤ} (hab : a ≤ b) : Mxi AA ξ b ≤ Mxi AA ξ a := by
  rintro x ⟨y, hy, rfl⟩
  obtain ⟨k, rfl⟩ := Int.exists_add_of_le hab
  refine ⟨((ξ ^ (k : ℤ) : WCˣ) : WC) * y, AA.mul_mem ?_ hy, ?_⟩
  · rw [zpow_natCast, Units.val_pow_eq_pow_val]; exact AA.pow_mem h.2.1 k
  · simp only [LinearMap.mulLeft_apply]
    rw [zpow_add, Units.val_mul]; ring

def actM (h : XiOK AA act ξ) (a : ℤ) (g : G) : Mxi AA ξ a →ₗ[O] Mxi AA ξ a :=
  ((act g).toLinearMap).restrict (Mxi_stable h g a)

abbrev Qab (AA : Subalgebra O WC) (ξ : WCˣ) (a b : ℤ) : Type :=
  Mxi AA ξ a ⧸ (Mxi AA ξ b).comap (Mxi AA ξ a).subtype

def actQab (h : XiOK AA act ξ) (a b : ℤ) (g : G) : Qab AA ξ a b →ₗ[O] Qab AA ξ a b :=
  Submodule.mapQ _ _ (actM h a g) (fun x hx => by
    simp only [Submodule.mem_comap] at hx ⊢
    exact Mxi_stable h g b _ hx)

theorem actQab_one (h : XiOK AA act ξ) (a b : ℤ) : actQab h a b 1 = LinearMap.id := by
  ext x
  simp only [actQab, actM, map_one]
  rfl

theorem actQab_mul (h : XiOK AA act ξ) (a b : ℤ) (g g' : G) :
    actQab h a b (g * g') = actQab h a b g ∘ₗ actQab h a b g' := by
  ext x
  simp only [actQab, actM, map_mul]
  rfl

def repX {T : Type} [AddCommGroup T] [Module O T] (ρT : G →* (T →ₗ[O] T))
    (h : XiOK AA act ξ) (a b : ℤ) : Representation O G (T ⊗[O] Qab AA ξ a b) where
  toFun g := TensorProduct.map (ρT g) (actQab h a b g)
  map_one' := by rw [map_one, actQab_one]; exact TensorProduct.map_id
  map_mul' g g' := by rw [map_mul, actQab_mul]; exact TensorProduct.map_comp _ _ _ _

end Xi

section Coc

variable {R G X : Type} [CommRing R] [Group G] [TopologicalSpace G] [AddCommGroup X] [Module R X]
  [TopologicalSpace X] (ρ : Representation R G X)

def IsCoc (f : G → X) : Prop := Continuous f ∧ ∀ g h, f (g * h) = f g + ρ g (f h)

def IsCob (f : G → X) : Prop := ∃ x : X, ∀ g, f g = ρ g x - x

def TorsKilledBy (ℓ r : R) : Prop :=
  ∀ f : G → X, IsCoc ρ f → (∃ k : ℕ, IsCob ρ (ℓ ^ k • f)) → IsCob ρ (r • f)

end Coc

abbrev AinfL (LT : LocTheory) (l : ℕ) [Fact l.Prime] : Type := LocAinf l (LT l)

section AinfC

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P)

def xiU : (WCb l)ˣ := AI.isUnit_inclW_ξ.unit

theorem inclW_act (g : GQ l) (a : Ainf l) :
    AI.actWCbHom g (inclW l a) = inclW l (AI.actWHom g a) := by
  ext n
  change (WittVector.map (autCb l (AI.actT g)).toRingHom
      (WittVector.map (algebraMap (OCb l) (Cb l)) a)).coeff n
    = (WittVector.map (algebraMap (OCb l) (Cb l)) (WittVector.map (AI.actT g).toRingHom a)).coeff n
  simp only [WittVector.map_coeff]
  exact autCb_alg l (AI.actT g) (a.coeff n)

def botExt (l : ℕ) [Fact l.Prime] : FinExt l := ⟨⊥, inferInstance⟩

theorem mem_GK_bot (g : GQ l) : g ∈ GK (botExt l) := by
  change g ∈ (⊥ : IntermediateField ℚ_[l] (Om l)).fixingSubgroup
  rw [IntermediateField.fixingSubgroup_bot]
  trivial

theorem xi_dvd_act (g : GQ l) (a : Ainf l) (h : ∃ b, a = AI.ξ * b) :
    ∃ b, AI.actWHom g a = AI.ξ * b := by
  have h1 := (AI.ainf_image_mem_filtration_one_iff (botExt l) a).mpr h
  apply (AI.ainf_image_mem_filtration_one_iff (botExt l) (AI.actWHom g a)).mp
  have h2 : AI.ιA (AI.actWHom g a) = P.actQ g (AI.ιA a) := AI.ιA_act g a
  have h3 := (P.PD (botExt l)).ι_comm ⟨g, mem_GK_bot g⟩ (AI.ιA a)
  rw [P.PD_ι, P.PD_ι, P.PD_actB, P.PD_actdR] at h3
  rw [h2, h3, ← P.PD_actdR (botExt l) ⟨g, mem_GK_bot g⟩]
  exact (P.PD (botExt l)).Fil_G _ 1 _ h1

theorem xiOK : XiOK (AinfSub l) AI.actWCbHom (xiU AI) := by
  refine ⟨?_, ⟨AI.ξ, rfl⟩, ?_⟩
  · rintro g x ⟨a, rfl⟩
    exact ⟨AI.actWHom g a, (inclW_act AI g a).symm⟩
  · intro g
    obtain ⟨b, hb⟩ := xi_dvd_act AI g AI.ξ ⟨1, (mul_one _).symm⟩
    obtain ⟨b', hb'⟩ := xi_dvd_act AI g⁻¹ AI.ξ ⟨1, (mul_one _).symm⟩
    have h1 : AI.ξ = AI.ξ * (b * AI.actWHom g b') := by
      have := congrArg (AI.actWHom g) hb'
      rw [← AlgEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one, AlgEquiv.one_apply, map_mul,
        hb] at this
      rw [← mul_assoc]; exact this
    have h2 : inclW l b * inclW l (AI.actWHom g b') = 1 := by
      have := congrArg (inclW l) h1
      rw [map_mul, map_mul] at this
      exact (AI.isUnit_inclW_ξ.mul_left_cancel (by rw [mul_one]; exact this)).symm
    refine ⟨⟨inclW l b, inclW l (AI.actWHom g b'), h2, by rw [mul_comm]; exact h2⟩, ⟨b, rfl⟩,
      ⟨AI.actWHom g b', rfl⟩, ?_⟩
    change AI.actWCbHom g (inclW l AI.ξ) = inclW l b * inclW l AI.ξ
    rw [inclW_act, hb, map_mul, mul_comm]

theorem xiOK_res (K : FinExt l) : XiOK (AinfSub l) (AI.actWCbHom.comp (GK K).subtype) (xiU AI) :=
  ⟨fun g x hx => (xiOK AI).1 (g : GQ l) x hx, (xiOK AI).2.1, fun g => (xiOK AI).2.2 (g : GQ l)⟩

end AinfC

structure ThetaL {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) where
  θ : P.R.BdR → PadicComplex l
  θ_one : θ 1 = 1
  θ_add : ∀ x ∈ (P.PD (botExt l)).Fil 0, ∀ y ∈ (P.PD (botExt l)).Fil 0, θ (x + y) = θ x + θ y
  θ_mul : ∀ x ∈ (P.PD (botExt l)).Fil 0, ∀ y ∈ (P.PD (botExt l)).Fil 0, θ (x * y) = θ x * θ y
  θ_onto : ∀ c, ∃ x ∈ (P.PD (botExt l)).Fil 0, θ x = c
  θ_ker : ∀ x ∈ (P.PD (botExt l)).Fil 0, θ x = 0 ↔ x ∈ (P.PD (botExt l)).Fil 1
  θ_act : ∀ (g : GQ l), ∀ x ∈ (P.PD (botExt l)).Fil 0, θ (P.actQdR g x) = AI.actC g (θ x)
  θ_Om : ∀ x : Om l, θ (algebraMap (Om l) P.R.BdR x) = (x : PadicComplex l)
  θ_int : ∀ a : Ainf l, ‖θ (P.ιB (AI.ιA a))‖ ≤ 1
  θ_teich : ∀ (x : OCb l) (y : OC l),
    PreTilt.coeff 0 x = Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}) y →
      ‖θ (P.ιB (AI.ιA (WittVector.teichmuller l x))) - (y : PadicComplex l)‖ ≤ ‖(l : PadicComplex l)‖
  fil_succ_iff_mul_t : ∀ (a : ℤ) (x : P.R.BdR), x ∈ (P.PD (botExt l)).Fil (a + 1) ↔
    ∃ y ∈ (P.PD (botExt l)).Fil a, x = P.ιB P.tB * y
  t_μ : P.ιB (AI.ιA AI.μ) - P.ιB P.tB ∈ (P.PD (botExt l)).Fil 2

structure Ties (LT : LocTheory) (AI : ∀ (l : ℕ) [Fact l.Prime], AinfL LT l) (HW : HWOf LT)
    (E : FonOf LT AI HW) where
  th : ∀ (l : ℕ) [Fact l.Prime], ThetaL (LT l) (AI l)

abbrev zlMod {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] (LL : FinExt l)
    (T : LocLat G ℚ_[l] ↥LL.1 ↥(OL LL)) : Module ℤ_[l] ↥T.L.T :=
  Module.compHom ↥T.L.T (algebraMap ℤ_[l] ↥(OL LL))

def actTZ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] (LL : FinExt l)
    (T : LocLat G ℚ_[l] ↥LL.1 ↥(OL LL)) :
    letI := zlMod LL T
    G →* (↥T.L.T →ₗ[ℤ_[l]] ↥T.L.T) :=
  letI := zlMod LL T
  { toFun := fun g =>
      { toFun := actT T.L g
        map_add' := map_add _
        map_smul' := fun c x => (actT T.L g).map_smul (algebraMap ℤ_[l] ↥(OL LL) c) x }
    map_one' := by ext x; simp [actT]
    map_mul' := fun g h => by
      ext x
      change T.ρ (g * h) (x : T.V) = T.ρ g (T.ρ h (x : T.V))
      rw [map_mul]; rfl }

def logZl (l : ℕ) [Fact l.Prime] (u : ℚ_[l]) : ℚ_[l] :=
  (∑' k : ℕ, (-1 : ℚ_[l]) ^ k * (u ^ (l * (l - 1)) - 1) ^ (k + 1) / ((k : ℚ_[l]) + 1)) /
    ((l : ℚ_[l]) * ((l : ℚ_[l]) - 1))

def logChi {l : ℕ} [Fact l.Prime] (LT : LocTheory) (g : GQ l) : ℤ_[l] :=
  if h : ‖logZl l ((LT l).χQ g : ℚ_[l])‖ ≤ 1 then ⟨logZl l ((LT l).χQ g : ℚ_[l]), h⟩ else 0

def LLat (LT : LocTheory) (HW : HWOf LT) (AI : ∀ (l : ℕ) [Fact l.Prime], AinfL LT l) (C : ℝ) (l : ℕ)
    [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL)
    (E : EtSit (LT l) (AI l) K s LL h ((HW l).W K s LL h)) : Prop :=
  let S := sit LT HW l (AI l) K s LL h
  ∀ (M0 h0 : ℕ) (T : LocLat S.G S.Qp S.LL S.O) (a b : ℤ), HypW S E.tie T M0 h0 → a < b →
    letI := zlMod LL T
    letI : TopologicalSpace (↥T.L.T ⊗[ℤ_[l]] Qab (AinfSub l) (xiU (AI l)) a b) :=
      (Ideal.span {(l : ℤ_[l])}).adicModuleTopology _
    let ρX := repX (actTZ LL T) (xiOK_res (AI l) K) a b
    let m := mN l s (M0 + h0)
    let c := cLL l m (padicValNat l (S.degKj m) - padicValNat l S.degK) (Jset S T) a b
    TorsKilledBy ρX (l : ℤ_[l]) ((l : ℤ_[l]) ^ c) ∧
    (∀ hh : ℕ, (∀ u ∈ Jset S T, -(hh : ℤ) ≤ u ∧ u ≤ hh) → -(hh : ℤ) ≤ a → b ≤ hh → M0 + h0 ≤ 2 * hh →
      (c : ℝ) ≤ m + ((b - a : ℤ) : ℝ) * (3 + (Jset S T).ncard * (m + Real.logb l (2 * hh))) ∧
      (m : ℝ) ≤ 2 * s + Real.logb l (2 * hh) + 2) ∧
    ∀ y : S.G → ↥T.L.T ⊗[ℤ_[l]] Qab (AinfSub l) (xiU (AI l)) a b, IsCoc ρX y →
      ∃ z, (∀ g, ρX g z = z) ∧ ∃ k : ℕ, IsCob ρX ((l : ℤ_[l]) ^ k •
        (((l : ℤ_[l]) ^ ⌈C * c * Real.log (2 * ((b - a : ℤ) : ℝ))⌉₊) • y -
          fun g : S.G => logChi LT (Subtype.val (show ↥(GK K) from g)) • z))

def LocalLiftingAinfEtale (D : Formalism.BasicNotions.D7) (AI : ∀ (l : ℕ) [Fact l.Prime], AinfL D.loc l) (HW : HWOf D.loc)
    (E : FonOf D.loc AI HW) (C : ℝ) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    LLat D.loc HW AI C l K s LL h ((E l).E K s LL h)

def Conclusion1 (D : Formalism.BasicNotions.D7) (AI : ∀ (l : ℕ) [Fact l.Prime], AinfL D.loc l) (C : ℝ) : Prop :=
  ∀ (HW : HWOf D.loc) (E : FonOf D.loc AI HW), LocalLiftingAinfEtale D AI HW E C

def LocalLiftingWachEtale (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C : ℝ) : Prop :=
  LocalLiftingAinfEtale D D.locA HW F C

def Conclusion2 (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    H0at (sit D.loc HW l (D.locA l) K s LL h) ((F l).E K s LL h).tie

def Conclusion4 (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    TBat (sit D.loc HW l (D.locA l) K s LL h) ((F l).E K s LL h).tie ∧
      TBeAt (sit D.loc HW l (D.locA l) K s LL h)

def Conclusion5 (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l), bkAll ((D.loc l).PD K)

def Conclusion6 (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    HerrAat (sit D.loc HW l (D.locA l) K s LL h) ∧ HerrAsat (sit D.loc HW l (D.locA l) K s LL h) ∧
      ((HW l).W K s LL h).ClNat ∧
      HerrBat (sit D.loc HW l (D.locA l) K s LL h) ((F l).E K s LL h).tie

def adm1 (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (u : (D.loc l).R.B) (w : (D.loc l).R.BdR),
    ∃ (x : (D.loc l).R.B) (y : (D.loc l).R.BdR), y ∈ ((D.loc l).PD K).Fil 0 ∧
      x - ((D.loc l).PD K).φ x = u ∧ ((D.loc l).PD K).ι x - y = w

def adm2 (_D : Formalism.BasicNotions.D7) : Prop := Formalism.GaloisCohomology.LocalTateDualityK

def adm3 (D : Formalism.BasicNotions.D7) : Prop := ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l), LocalTateTopDegree ((D.loc l).PD K)

def ArchimedeanSignatureMatching (_D : Formalism.BasicNotions.D7) : Prop := Formalism.GaloisCohomology.LocalEulerCharK

def adm5 (D : Formalism.BasicNotions.D7) : Prop := ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l), TateFilteredInvariants ((D.loc l).PD K)

def adm6 (D : Formalism.BasicNotions.D7) : Prop := ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l), contCore ((D.loc l).PD K)

def adm7 (D : Formalism.BasicNotions.D7) : Prop := ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l), fontCore ((D.loc l).PD K)

def adm8 (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l), drDualCore ((D.loc l).PD K) ∧ filDualCore ((D.loc l).PD K)

def adm9 (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    FNatW (sit D.loc HW l (D.locA l) K s LL h) ∧
      DecW (sit D.loc HW l (D.locA l) K s LL h) ((F l).E K s LL h).tie

def admitted (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  adm1 D ∧ adm2 D ∧ adm3 D ∧ ArchimedeanSignatureMatching D ∧ adm5 D ∧ adm6 D ∧ adm7 D ∧ adm8 D ∧ adm9 D HW F

def Stmt (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  admitted D HW F → Conclusion2 D HW F ∧ Conclusion4 D HW F ∧ Conclusion5 D ∧ Conclusion6 D HW F

def LocalLiftingPackage (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C : ℝ) : Prop :=
  admitted D HW F → LocalLiftingWachEtale D HW F C ∧ Conclusion2 D HW F ∧ Conclusion4 D HW F ∧ Conclusion5 D ∧ Conclusion6 D HW F

def LocalLiftingUniformConstant : Prop :=
  ∃ C : ℝ, ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), LocalLiftingPackage D HW F C

end Formalism.MainNotions.LocalSituation
