import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPowMod

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBX

def transl {S : Scheme.{0}} {A : Over S} [GrpObj A] (x : 𝟙_ (Over S) ⟶ A) : A.left ⟶ A.left := ((toUnit A ≫ x) * 𝟙 A).left

section Generic

variable {K : Type} [Field K] {P P₂ : PolAV (Sp K)} {n : ℕ}

def TransSec (x : 𝟙_ (Over (Sp K)) ⟶ P.A) (s s' : (lbPow P.L n).Sec) : Prop :=
  ∃ io : LB.Iso ((lbPow P.L n).pull (transl x)) (lbPow P.L n), io.IsGen ∧ SecMaps io (secPull s (transl x)) s'

def TransMap (x : 𝟙_ (Over (Sp K)) ⟶ P.A) {r : ℕ} (b : Fin r → (lbPow P.L n).Sec) (u : (Fin r → K) ≃ₗ[K] (Fin r → K)) : Prop :=
  ∃ io : LB.Iso ((lbPow P.L n).pull (transl x)) (lbPow P.L n), io.IsGen ∧
    ∀ c, SecMaps io (secPull (secComb P.A.hom c b) (transl x)) (secComb P.A.hom (u c) b)

def GenPull (a : P.A ⟶ P₂.A) (θ : (lbPow P₂.L 1).Sec) (e : (lbPow P.L n).Sec) : Prop :=
  ∃ ga : LB.Iso ((lbPow P₂.L 1).pull a.left) (lbPow P.L n), ga.IsGen ∧ SecMaps ga (secPull θ a.left) e

def Eig (a : P.A ⟶ P₂.A) (e₀ : (lbPow P.L n).Sec) {d : ℕ} (e : Fin d → (lbPow P.L n).Sec) : Prop :=
  ∃ z : Fin d → Tor P n, (Function.Injective fun i => (z i).1 ≫ a) ∧ (∀ t : Tor P n, ∃ i, t.1 ≫ a = (z i).1 ≫ a) ∧
    ∀ i, TransSec (z i).1 e₀ (e i)

def Chars (a : P.A ⟶ P₂.A) {d : ℕ} (e : Fin d → (lbPow P.L n).Sec) (χ : Fin d → (𝟙_ (Over (Sp K)) ⟶ P.A) → Kˣ) : Prop :=
  (∀ i h h', h ≫ a = 1 → h' ≫ a = 1 → χ i (h * h') = χ i h * χ i h') ∧
  (∀ i i', (∀ h, h ≫ a = 1 → χ i h = χ i' h) → i = i') ∧
  ∀ h, h ≫ a = 1 → (∃ io : LB.Iso ((lbPow P.L n).pull (transl h)) (lbPow P.L n), io.IsGen) ∧
    ∀ io : LB.Iso ((lbPow P.L n).pull (transl h)) (lbPow P.L n), io.IsGen → ∃ l : Kˣ, ∀ i,
      SecMaps io (secPull (e i) (transl h)) (secSmul P.A.hom ((l * χ i h : Kˣ) : K) (e i))

abbrev boxLB (P : PolAV (Sp K)) (n : ℕ) {k : ℕ} (pr : Fin k → (P₂.A ⟶ P.A)) : LB P₂.A.left :=
  LB.LinComb (lbPow P.L n) (K := Fin k) (fun u => (pr u).left) fun _ => 1

def IsBox {k : ℕ} {pr : Fin k → (P₂.A ⟶ P.A)} (ga : LB.Iso (boxLB P n pr) (lbPow P₂.L n)) (s : Fin k → (lbPow P.L n).Sec)
    (s' : (lbPow P₂.L n).Sec) : Prop :=
  ∃ t : (boxLB P n pr).Sec, (∀ j : Fin k → (lbPow P.L n).ι, t.f j =
    ∏ u, ((pr u).left.appLE _ _ (LB.wchart_le (lbPow P.L n) (fun u => (pr u).left) j u)).hom ((s u).f (j u))) ∧
    SecMaps ga t s'

end Generic

section Model

variable {R K : Type} [CommRing R] [Field K] [Algebra R K] {P P₂ : PolAV (Sp K)} {N N₂ n : ℕ}

def PullsTo {m : TGrp R K P N} {m₂ : TGrp R K P₂ N₂} (B : TBun m n) (B₂ : TBun m₂ 1) (a' : m.AA ⟶ m₂.AA)
    (θ : (lbPow P₂.L 1).Sec) (e : (lbPow P.L n).Sec) : Prop :=
  ∃ ga : LB.Iso (B₂.M.L.pull a'.left) B.M.L, ga.IsGen ∧ ∃ (c : K) (t₂ : B₂.M.L.Sec) (t : B.M.L.Sec), c ≠ 0 ∧
    SecMaps B₂.w (secPull t₂ m₂.φ) (secSmul P₂.A.hom c θ) ∧ SecMaps ga (secPull t₂ a'.left) t ∧
    SecMaps B.w (secPull t m.φ) (secSmul P.A.hom c e)

def IsSub (m' : TGrp R K P N₂) (m : TGrp R K P N) (i : m'.AA ⟶ m.AA) : Prop :=
  IsMonHom i ∧ IsOpenImmersion i.left ∧ m'.φ ≫ i.left = m.φ ∧ Set.range (m'.j ≫ i).left = Set.range m.j.left

def IsGlued {G : Over (Sp R)} (φ₀ : P.A.left ⟶ G.left) (X : Over (Sp R)) (φ : P.A.left ⟶ X.left) (io : Tor P N → (G ⟶ X)) : Prop :=
  IsSeparated X.hom ∧ IsPullback φ P.A.hom X.hom (spMap (algebraMap R K)) ∧ (∀ x, IsOpenImmersion (io x).left) ∧
  (∀ z : X.left, ∃ x, z ∈ Set.range (io x).left) ∧ ∀ x, φ₀ ≫ (io x).left = transl x.1 ≫ φ

end Model

def LocMem {K : Type} [Field K] [NumberField K] {r : ℕ} (E : Submodule (𝓞 K) (Fin r → K))
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (x : Fin r → K) : Prop :=
  ∃ s : 𝓞 K, s ∉ v.asIdeal ∧ s • x ∈ E

def LocPrim (κ : GlobalTheory.KeyCl.Rule) : Prop :=
  ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [CharZero K] [Algebra R K]
    [IsFractionRing R K], Finite (IsLocalRing.ResidueField R) → ∀ (x : KeyIn K),
    (letI := x.P.isAb.comm; GlobalTheory.ZH.HypS x.P.A x.P.L) →
    ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (φ : x.P.A.left ⟶ G.left) (M : RigLB G)
      (w : LB.Iso (M.L.pull φ) (lbPow x.P.L (1 ^ 2))) (y : Fin x.P.g → (epsR R ⟶ G)),
      IsSemiAbelian G → IsGrpPullback x.P.A G (spMap (algebraMap R K)) φ → Nonempty (CubicalStr G M) → w.IsGen →
      GlobalTheory.MBLow.RigPow (algebraMap R K) w x.rig → IsLieBasis y → (∀ i, IsVecOver (algebraMap R K) φ (y i) (x.v i)) →
      ∀ s : (lbPow x.P.L (1 ^ 2)).Sec, (∀ (i : x.P.L.ι) (h : (lbPow x.P.L (1 ^ 2)).U (fun _ => i) ≤ x.P.L.U i),
        s.f (fun _ => i) = resG _ h (x.th.f i)) → (∃ t : M.L.Sec, SecMaps w (secPull t φ) s) →
      ∃ r : R, algebraMap R K r * (κ K x : K) = 1

end GlobalTheory.MBX

end
