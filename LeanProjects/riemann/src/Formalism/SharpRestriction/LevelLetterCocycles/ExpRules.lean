import Formalism.SharpRestriction.LevelLetterCocycles.LatticeBoundsOfThreeParts
import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates

noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.Sh

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct Module
open Formalism.MainNotions.CrystallineLiftingInputs (DL InPN pullJ fMX TCase)
open Formalism.MainNotions.LiftingTheory (qp pk Over CaseA JumpsLet)
open Formalism.MainNotions.WachCoordinates (FilLev)
open Formalism.MainNotions.DeltaInvariantLattices (ιDi)

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

def conv {M : Type} [AddCommGroup M] [Module LL M] (f : PowerSeries LL) (d : ℤ → M) : ℤ → M :=
  fun k => ∑ᶠ j : ℕ, PowerSeries.coeff j f • d (k - j)

def IsExp (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) (x : W.DD T)
    (d : ℤ → T.V ⊗[Qp] BdR) : Prop :=
  (∃ m : ℤ, ∀ k < m, d k = 0) ∧ ∃ (a : LetA O n) (ha : a • x ∈ W.N T), W.lev i ζ a ≠ 0 ∧
    ∀ k : ℤ, W.levN T i ζ ⟨a • x, ha⟩ k = conv (W.lev i ζ a) d k

def ExpRing (W : LocWach PD LL O v n) : Prop :=
  CaseA W → ∀ (i : ZMod n) (ζ : LL), IsPrimitiveRoot ζ PD.p →
    (∃ u : PowerSeries LL, IsUnit u ∧ W.lev i ζ (qp W) = u * PowerSeries.X) ∧
    PowerSeries.constantCoeff (W.lev i ζ W.π₀) = -(PD.p : LL) ∧ IsUnit (W.lev i ζ (pk W 1))

def ExpRules (W : LocWach PD LL O v n) : Prop :=
  CaseA W → ∀ (T : LocLat G Qp LL O), IsCrys PD T.ρ → ∀ (i : ZMod n) (ζ : LL), IsPrimitiveRoot ζ PD.p →
    (∀ (x : W.DD T) (a : LetA O n), a • x ∈ W.N T → W.lev i ζ a ≠ 0 → ∃! d, IsExp W T i ζ x d) ∧
    (∀ x d, DL W T i x → IsExp W T i ζ x d → ∀ k, d k ∈ ιDi W T i) ∧
    (∀ x y d e, IsExp W T i ζ x d → IsExp W T i ζ y e → IsExp W T i ζ (x + y) (d + e)) ∧
    (∀ (c : O) x d, IsExp W T i ζ x d → IsExp W T i ζ (c • x) (fun k => algebraMap O LL c • d k)) ∧
    (∀ (a : LetA O n) x d, IsExp W T i ζ x d → IsExp W T i ζ (a • x) (conv (W.lev i ζ a) d)) ∧
    (∀ x d, IsExp W T i ζ x d →
      IsExp W T i ζ (W.γ T x) (fun k => (algebraMap O LL (W.χΓ W.gam : O)) ^ k • d k)) ∧
    ∀ (T' : LocLat G Qp LL O) (F : LatHom T.L T'.L), IsCrys PD T'.ρ → ∀ x d, IsExp W T i ζ x d →
      IsExp W T' i ζ (W.map F x)
        (fun k => AlgebraTensorModule.map F.f (LinearMap.id : BdR →ₗ[Qp] BdR) (d k))

def ExpCrit (W : LocWach PD LL O v n) : Prop :=
  CaseA W → ∀ (T : LocLat G Qp LL O), IsCrys PD T.ρ → ∀ (i : ZMod n) (ζ : LL), IsPrimitiveRoot ζ PD.p →
    ∀ (x : W.DD T) (d : ℤ → T.V ⊗[Qp] BdR), DL W T i x → IsExp W T i ζ x d →
      ((∃ k : ℕ, qp W ^ k • x ∈ W.N T) → (x ∈ W.N T ↔ ∀ k, d k ∈ FilLev W T i 0 (-k))) ∧
      ((∃ k : ℕ, qp W ^ k • x ∈ pullJ W T (i - 1) 1) → (x ∈ pullJ W T (i - 1) 1 ↔ ∀ k < 0, d k = 0))

def LemK (W : LocWach PD LL O v n) : Prop :=
  CaseA W → ∀ (T : LocLat G Qp LL O), IsCrys PD T.ρ → ∀ (i : ZMod n) (ζ : LL), IsPrimitiveRoot ζ PD.p →
    ∀ (x : W.DD T) (d : ℤ → T.V ⊗[Qp] BdR), DL W T i x → IsExp W T i ζ x d →
      (∃ j : ℕ, ((PD.p : ℕ) : O) ^ j • (W.γ T x - x) ∈ W.N T) →
      (∀ k, k ≠ 0 → d k ∈ FilLev W T i 0 (-k)) ∧
      ∀ y : ℕ, qp W ^ y • x ∈ W.N T →
        d 0 ∈ FilLev W T i 0 (-(y : ℤ)) ∧ (x ∈ W.N T ↔ d 0 ∈ FilLev W T i 0 0)

def FilDim (W : LocWach PD LL O v n) : Prop :=
  CaseA W → ∀ (T : LocLat G Qp LL O), IsCrys PD T.ρ → ∀ (i : ZMod n) (τ : K →ₐ[Qp] LL), Over W τ i →
    finrank LL ↥(ιDi W T i) = finrank LL T.V ∧
    ∀ a b : ℤ, a ≤ b → (finrank LL ↥(FilLev W T i 0 a) : ℤ) - finrank LL ↥(FilLev W T i 0 b) =
      ∑ u ∈ Finset.Ico a b, multV PD T.ρ τ u

def at0 (W : LocWach PD LL O v n) (f : PowerSeries O) : LetA O n := fun _ => PowerSeries.subst W.π₀₁ f

def IsBas (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (i : ZMod n) {r : ℕ} (e : Fin r → W.DD T) : Prop :=
  (∀ k, e k ∈ W.N T ∧ DL W T i (e k)) ∧
    ∀ x ∈ W.N T, DL W T i x → ∃! a : Fin r → PowerSeries O, x = ∑ k, at0 W (a k) • e k

def BasTool [NeZero n] (W : LocWach PD LL O v n) : Prop :=
  CaseA W → ∀ (T : LocLat G Qp LL O), IsCrys PD T.ρ → ∀ i : ZMod n,
    (∃ e : Fin (finrank LL T.V) → W.DD T, IsBas W T i e) ∧
    ∀ (r : ℕ) (e : Fin r → W.DD T), IsBas W T i e → ∀ j : ℕ,
      (∀ x ∈ pullJ W T i j, DL W T (i + (j : ZMod n)) x →
        ∃! a : Fin r → PowerSeries O, x = ∑ k, at0 W (a k) • ((W.φD T) ^ j) (e k)) ∧
      ∀ (x : W.DD T) (s : ℕ), ((PD.p : ℕ) : O) ^ s • x ∈ pullJ W T i j → x ∈ pullJ W T i j

def DetTool [NeZero n] (W : LocWach PD LL O v n) : Prop :=
  CaseA W → ∀ (T : LocLat G Qp LL O) (Mi hi : ZMod n → ℕ), IsCrys PD T.ρ → JumpsLet W T Mi hi →
    ∀ (i : ZMod n) (τ : K →ₐ[Qp] LL), Over W τ i → ∀ (r : ℕ) (e e' : Fin r → W.DD T),
      IsBas W T i e → IsBas W T (i - 1) e' → ∀ (M : ℕ) (P : Matrix (Fin r) (Fin r) (PowerSeries O)),
        (∀ k, qp W ^ M • W.φD T (e' k) = ∑ m, at0 W (P m k) • e m) →
        ∃ (u : PowerSeries O) (w : ℕ), IsUnit u ∧
          P.det = u * (PowerSeries.X + ((PD.p : ℕ) : PowerSeries O)) ^ w ∧
          (w : ℤ) = (M : ℤ) * r + ∑ a ∈ Finset.Icc (-(Mi i : ℤ)) (hi i : ℤ), a * multV PD T.ρ τ a

def ZTool [NeZero n] (W : LocWach PD LL O v n) : Prop :=
  CaseA W → 11 ≤ PD.p → ∀ (j X σ : ℕ), TCase PD.p j 1 X σ →
    ∀ (T : LocLat G Qp LL O), IsCrys PD T.ρ → ∀ (i : ZMod n) (r : ℕ) (e : Fin r → W.DD T) (he : IsBas W T i e),
      ∃ Z Z' R : Matrix (Fin r) (Fin r) (PowerSeries O),
        (∀ m k, PowerSeries.constantCoeff (Z m k) = if m = k then ((PD.p : ℕ) : O) ^ σ else 0) ∧
        Z * Z' = ((PD.p : ℕ) : PowerSeries O) ^ (2 * σ) • (1 : Matrix (Fin r) (Fin r) (PowerSeries O)) +
          (PowerSeries.X * (PowerSeries.X + ((PD.p : ℕ) : PowerSeries O)) ^ X) • R ∧
        ∀ k, (∃ p ∈ pullJ W T i j,
            W.γ T (∑ m, at0 W (Z m k) • ((W.φD T) ^ j) (e m)) - ∑ m, at0 W (Z m k) • ((W.φD T) ^ j) (e m) =
              fMX W 1 X • p) ∧
          ∀ (ζ : LL), IsPrimitiveRoot ζ PD.p → ∀ d,
            IsExp W T (i + (j : ZMod n)) ζ (∑ m, at0 W (Z m k) • ((W.φD T) ^ j) (e m)) d →
            ∀ s : ℤ, s < X → d s = if s = 0 then (PD.p : LL) ^ σ • ιV PD (LL := LL) (V := T.V)
              ((φVB PD (LL := LL) (V := T.V))^[j] (W.cmp T ⟨e k, (he.1 k).1⟩)) else 0

def ExtData (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (Mi hi : ZMod n → ℕ) (a N : ℕ) {FF : Type} [AddCommGroup FF]
    [Module O FF] (g : FF →ₗ[O] ↥(latticeFiniteCocycles PD T.L)) (y z : FF →ₗ[O] W.DD T) (μ ν : ZMod n → FF →ₗ[O] W.DD T) : Prop :=
  (∀ f, ∃ (x : ↥(W.wachCocyclesDelta T)) (hκ : (g f : G → T.V) ∈ latticeCocycles T.L), (x : W.DD T × W.DD T) = (y f, z f) ∧
    W.clK T x = Submodule.Quotient.mk (⟨(g f : G → T.V), hκ⟩ : ↥(latticeCocycles T.L))) ∧
  ∀ (i : ZMod n) (f : FF), DL W T i (μ i f) ∧ DL W T i (ν i f) ∧
    InPN W T 1 (((PD.p : ℕ) : O) ^ N • ((letE i : LetA O n) • z f) + (W.γ T (μ i f) - μ i f)) ∧
    qp W ^ Mi i • (((PD.p : ℕ) : O) ^ N • ((letE i : LetA O n) • y f) + W.φD T (μ (i - 1) f) - μ i f) ∈ W.N T ∧
    (∃ s : ℕ, ((PD.p : ℕ) : O) ^ s • (qp W ^ hi i •
      (((PD.p : ℕ) : O) ^ N • ((letE i : LetA O n) • y f) + W.φD T (μ (i - 1) f) - μ i f)) ∈
        pullJ W T (i - 1) 1) ∧
    ((PD.p : ℕ) : O) ^ N • ν i f - qp W ^ a • μ i f ∈ W.N T

def ExtTool [NeZero n] (W : LocWach PD LL O v n) : Prop :=
  ∀ (d : ℕ) (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b : ZMod n → ℕ) (S η m : ℕ),
    SetCS W d T₁ T₂ F b S η m →
    ∀ (FF : Type) [AddCommGroup FF] [Module O FF] [Module.Free O FF] [Module.Finite O FF]
      (g : FF →ₗ[O] ↥(latticeFiniteCocycles PD T₂.L)),
      ∃ (N : ℕ) (y z : FF →ₗ[O] W.DD T₂) (μ ν : ZMod n → FF →ₗ[O] W.DD T₂),
        ExtData W T₂ (MiW d b S η) (hiW d b S η) ⌈aR PD.p (hpar n b S + η)⌉₊ N g y z μ ν

end Formalism.MainNotions.RamifiedCoefficientChains.Sh

end
