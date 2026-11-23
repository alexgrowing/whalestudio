import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatHalfSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFlagFrame

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains GlobalTheory.BundleChernComparison GlobalTheory.ChainPts
open GlobalTheory.LineNorm (IsTanBasis)
open GlobalTheory.Twist (resM)
open Formalism.MainNotions.DIV.Cons (intO SCF)

namespace GlobalTheory.OmegaHT

section Forms

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  (t : SAB H X) (p : ℕ)

def CutsHT {A : Type} [CommRing A] (x : Sp A ⟶ X) {g n : ℕ} (e : Fin g → (Sp (DualNumber A) ⟶ t.G.left))
    (η : Fin n → Fin g → A) : Prop :=
  ∀ (C : SCF p) (κ : A →+* ↥(intO ↥C.S)) (a : Fin g → ↥C.S) (v : Sp (DualNumber ↥C.S) ⟶ t.G.left),
    IsCombAtG t (spMap ((intO ↥C.S).subtype.comp κ) ≫ x)
      (fun i => spMap (dualMap ((intO ↥C.S).subtype.comp κ)) ≫ e i) a v →
      (v ∈ latHT t p (spMap ((intO ↥C.S).subtype.comp κ) ≫ x) ↔ ∀ j, ‖∑ i, (κ (η j i) : ↥C.S) * a i‖ ≤ 1)

def SpansP {A : Type} [CommRing A] {g n : ℕ} (η : Fin n → Fin g → A) : Prop :=
  ∃ M : Fin g → Fin n → A, ∀ i k, ∑ j, M i j * η j k = if i = k then (p : A) else 0

def LocGen {S : Scheme.{0}} (ρ : S ⟶ X) : Prop :=
  ∀ z : S, ∃ (V : S.affineOpens) (g n : ℕ) (e : Fin g → (Sp (DualNumber Γ(S, V.1)) ⟶ t.G.left))
    (η : Fin n → Fin g → Γ(S, V.1)), z ∈ V.1 ∧ IsTanBasis t (R := Γ(S, V.1)) (V.2.fromSpec ≫ ρ) e ∧ SpansP p η ∧
      CutsHT t p (A := Γ(S, V.1)) (V.2.fromSpec ≫ ρ) e η

def LocBasis {S : Scheme.{0}} (ρ : S ⟶ X) : Prop :=
  ∀ z : S, ∃ (V : S.affineOpens) (g : ℕ) (e : Fin g → (Sp (DualNumber Γ(S, V.1)) ⟶ t.G.left))
    (η : Fin g → Fin g → Γ(S, V.1)), z ∈ V.1 ∧ IsTanBasis t (R := Γ(S, V.1)) (V.2.fromSpec ≫ ρ) e ∧ SpansP p η ∧
      CutsHT t p (A := Γ(S, V.1)) (V.2.fromSpec ≫ ρ) e η

end Forms

def crd {X : Scheme.{0}} {F : X.Modules} {r : ℕ} {V V' : X.Opens} {s : Fin r → Γ(F, V')} (hs : GlobalTheory.VB.IsFrame s)
    (σ : Γ(F, V)) (i : Fin r) : Γ(X, V ⊓ V') :=
  (hs.basis inf_le_right).repr (resM F inf_le_left σ) i

theorem coef_true {X : Scheme.{0}} {F : X.Modules} {r : ℕ} {V V' : X.Opens} {e : Fin r → Γ(F, V)} {s : Fin r → Γ(F, V')}
    (he : GlobalTheory.VB.IsFrame e) (hs : GlobalTheory.VB.IsFrame s) (l i : Fin r) : coef true he hs l i = crd hs (e l) i := rfl

def LocInSpan {X : Scheme.{0}} {F : X.Modules} {r : ℕ} {V V' : X.Opens} (η : Fin r → Γ(F, V)) (η' : Fin r → Γ(F, V')) :
    Prop :=
  ∀ z : X, z ∈ V → z ∈ V' → ∃ (U : X.Opens) (h : U ≤ V) (h' : U ≤ V'), z ∈ U ∧
    ∀ j, resM F h' (η' j) ∈ Submodule.span Γ(X, U) (Set.range fun l => resM F h (η l))

def SectionsSatisfyAtPrime (p : ℕ) {X : Scheme.{0}} {F : X.Modules} {r : ℕ} {V : X.Opens} (η : Fin r → Γ(F, V)) : Prop :=
  ∃ f : Fin r → Γ(F, V), GlobalTheory.VB.IsFrame f ∧ ∀ i, (p : Γ(X, V)) • f i ∈ Submodule.span Γ(X, V) (Set.range η)

section Model

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

def CutsSec (Z : LocM.Mdl Y i₀) {X : Scheme.{0}} (h : X ⟶ Z.X) {r : ℕ} (x : Fin r → Letter Dw) (b : Bool) {F : X.Modules}
    {s : ∀ a : Fin Z.m, Fin r → Γ(F, h ⁻¹ᵁ (Z.U a).1)} (hs : ∀ a, GlobalTheory.VB.IsFrame (s a)) {V : X.Opens} {n : ℕ}
    (η : Fin n → Γ(F, V)) : Prop :=
  ∀ (y : Z.Pt) (w : Sp ↥(intO ↥y.C.S) ⟶ X), w ≫ h = y.z → ∀ (a : Fin Z.m) (φ : Γ(Z.X, (Z.U a).1) →+* ↥y.C.S),
    spMap φ ≫ Z.chart a = y.gen → ⊤ ≤ w ⁻¹ᵁ V →
      ∀ (cf : Fin r → ↥y.C.S) (v : Sp (DualNumber ↥y.C.S) ⟶ (Y Z.i).t.G.left),
        IsCombAtG (Y Z.i).t (y.gen ≫ Z.π) (fun i => (Z.fr a).bc φ (x i).1 (x i).2) cf v →
          (v ∈ lat (Y Z.i).t p (y.gen ≫ Z.π) b ↔
            ∀ j, ‖∑ i, cf i * valF (spMap (intO ↥y.C.S).subtype ≫ w) _ (crd (hs a) (η j) i)‖ ≤ 1)

def HasDualFrames (Z : LocM.Mdl Y i₀) {X : Scheme.{0}} (h : X ⟶ Z.X) {r : ℕ} (x : Fin r → Letter Dw) {F : X.Modules}
    {s : ∀ a : Fin Z.m, Fin r → Γ(F, h ⁻¹ᵁ (Z.U a).1)} (hs : ∀ a, GlobalTheory.VB.IsFrame (s a)) : Prop :=
  ∀ (V : X.affineOpens) (g : ℕ) (e : Fin g → (Sp (DualNumber Γ(X, V.1)) ⟶ (Y Z.i).t.G.left)),
    IsTanBasis (Y Z.i).t (R := Γ(X, V.1)) (V.2.fromSpec ≫ h ≫ Z.π) e →
      ∃ f : Fin g → Γ(F, V.1), GlobalTheory.VB.IsFrame f ∧ ∀ (k : Type) [Field k] (κ : Γ(X, V.1) →+* k) (a : Fin Z.m)
        (φ : Γ(Z.X, (Z.U a).1) →+* k), spMap φ ≫ Z.chart a = spMap κ ≫ V.2.fromSpec ≫ h →
        ∀ (cf : Fin r → k) (v : Sp (DualNumber k) ⟶ (Y Z.i).t.G.left),
          IsCombAtG (Y Z.i).t (spMap κ ≫ V.2.fromSpec ≫ h ≫ Z.π) (fun i => (Z.fr a).bc φ (x i).1 (x i).2) cf v →
          IsCombAtG (Y Z.i).t (spMap κ ≫ V.2.fromSpec ≫ h ≫ Z.π) (fun l => spMap (dualMap κ) ≫ e l)
            (fun l => ∑ i, cf i * valF (spMap κ ≫ V.2.fromSpec) _ (crd (hs a) (f l) i)) v

def ToOpen (Z : LocM.Mdl Y i₀) {X : Scheme.{0}} (h : X ⟶ Z.X) : Prop :=
  ∀ η : X, (∀ y : X, y ⤳ η → y = η) → h η ∈ Z.opn

end Model

def RootSt : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (B : Vert.Model O),
    GlobalTheory.IsNormalScheme B.X → ∀ (p : ℕ) [Fact p.Prime] (a : ℕ), 0 < a →
    ∃ (B' : Vert.Model O) (f : Vert.Model.Hom B' B) (π : Γ(B'.X, ⊤)),
      GlobalTheory.IsNormalScheme B'.X ∧ f.relDim = 0 ∧ IsRootOfP p π a

def RingSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) [IsLocallyNoetherian X] (t : SAB H X),
    X.IsSeparated → ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CharZero A]
    [IsAlgClosed (FractionRing A)] (x : Sp A ⟶ X) (g : ℕ) (e : Fin g → (Sp (DualNumber A) ⟶ t.G.left)),
    IsTanBasis t x e → ∃ (n : ℕ) (η : Fin n → Fin g → A), SpansP p η ∧ CutsHT t p x e η

def GenSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) [IsLocallyNoetherian X] (t : SAB H X),
    X.IsSeparated → ∀ (p : ℕ) [Fact p.Prime], ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (B : Vert.Model O),
    GlobalTheory.IsNormalScheme B.X → ∀ ρ : B.X ⟶ X,
    ∃ (B' : Vert.Model O) (f : Vert.Model.Hom B' B), GlobalTheory.IsNormalScheme B'.X ∧ f.relDim = 0 ∧ LocGen t p (f.f ≫ ρ)

def BasisSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (p : ℕ) [Fact p.Prime],
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (B : Vert.Model O),
    GlobalTheory.IsNormalScheme B.X → ∀ ρ : B.X ⟶ X, LocGen t p ρ →
    ∃ (B' : Vert.Model O) (f : Vert.Model.Hom B' B), GlobalTheory.IsNormalScheme B'.X ∧ f.relDim = 0 ∧ LocBasis t p (f.f ≫ ρ)

def LinkSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p)
    (Z : LocM.Mdl Y i₀) (X : Scheme.{0}) (h : X ⟶ Z.X) (r : ℕ) (x : Fin r → Letter Dw), Function.Bijective x →
    ∃ (F : X.Modules) (s : ∀ a : Fin Z.m, Fin r → Γ(F, h ⁻¹ᵁ (Z.U a).1)) (k : IsLat Z h x true false F s),
      GlobalTheory.VB.IsVB F r ∧ HasDualFrames Z h x k.frame

def SpanSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p)
    (Z : LocM.Mdl Y i₀), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ [IsDiscreteValuationRing (Z.i.c.V W)]
    (B : Vert.Model (Z.i.c.V W)), GlobalTheory.IsNormalScheme B.X → ∀ h : B.X ⟶ Z.X, ToOpen Z h →
    ∀ (r : ℕ) (x : Fin r → Letter Dw), ∀ (b : Bool) (F : B.X.Modules)
    (s : ∀ a : Fin Z.m, Fin r → Γ(F, h ⁻¹ᵁ (Z.U a).1)) (hs : ∀ a, GlobalTheory.VB.IsFrame (s a)) (V V' : B.X.Opens)
    (η : Fin r → Γ(F, V)) (η' : Fin r → Γ(F, V')), SectionsSatisfyAtPrime p η → SectionsSatisfyAtPrime p η' → CutsSec Z h x b hs η →
    CutsSec Z h x b hs η' → LocInSpan η η'

def GlueSt : Prop :=
  ∀ (X : Scheme.{0}) (F : X.Modules) (r : ℕ) (J : Type) (V : J → X.Opens) (η : ∀ α, Fin r → Γ(F, V α)),
    (∀ z : X, ∃ α, z ∈ V α) →
    (∀ α (U : X.Opens) (h : U ≤ V α), LinearIndependent Γ(X, U) fun l => resM F h (η α l)) →
    (∀ α β, LocInSpan (η α) (η β)) →
    ∃ (G : X.Modules) (ι : G ⟶ F), GlobalTheory.VB.IsVB G r ∧
      ∀ α, ∃ e : Fin r → Γ(G, V α), GlobalTheory.VB.IsFrame e ∧ ∀ l, ι.app _ (e l) = η α l

def BundleSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p)
    (Z : LocM.Mdl Y i₀), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ [IsDiscreteValuationRing (Z.i.c.V W)]
    (B : Vert.Model (Z.i.c.V W)), GlobalTheory.IsNormalScheme B.X → ∀ h : B.X ⟶ Z.X, ToOpen Z h →
    ∀ (r : ℕ) (x : Fin r → Letter Dw), Function.Bijective x → LocBasis (Y Z.i).t p (h ≫ Z.π) →
    ∃ (F : B.X.Modules) (s : ∀ a : Fin Z.m, Fin r → Γ(F, h ⁻¹ᵁ (Z.U a).1)), GlobalTheory.VB.IsVB F r ∧ IsLat Z h x true true F s

def MapSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p)
    (Z : LocM.Mdl Y i₀), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ [IsDiscreteValuationRing (Z.i.c.V W)]
    (B : Vert.Model (Z.i.c.V W)), GlobalTheory.IsNormalScheme B.X → ∀ h : B.X ⟶ Z.X, ToOpen Z h →
    ∀ (r : ℕ) (x : Fin r → Letter Dw), Function.Bijective x → ∀ (b b' : Bool) (F F' : B.X.Modules)
    (s : ∀ a : Fin Z.m, Fin r → Γ(F, h ⁻¹ᵁ (Z.U a).1)) (s' : ∀ a : Fin Z.m, Fin r → Γ(F', h ⁻¹ᵁ (Z.U a).1)),
    GlobalTheory.VB.IsVB F r → GlobalTheory.VB.IsVB F' r → IsLat Z h x true b F s → IsLat Z h x true b' F' s' →
    ∀ (g : Γ(B.X, ⊤)) (c : 𝓞 E),
    (∀ (y : Z.Pt) (w : Sp ↥(intO ↥y.C.S) ⟶ B.X), w ≫ h = y.z → ∀ v : Sp (DualNumber ↥y.C.S) ⟶ (Y Z.i).t.G.left,
      IsTanAtG (Y Z.i).t (y.gen ≫ Z.π) v → v ∈ lat (Y Z.i).t p (y.gen ≫ Z.π) b' →
        spMap (epsMul (valF (spMap (intO ↥y.C.S).subtype ≫ w) ⊤ g)) ≫ v ≫ ((Y Z.i).t.act.act c).left ∈
          lat (Y Z.i).t p (y.gen ≫ Z.π) b) →
    ∃ φ : F ⟶ F', ∀ (a : Fin Z.m) (i : Fin r), φ.app _ (s a i) =
      (resG B.X le_top g * (h.app (Z.U a).1).hom (Z.alg a (embK Z.i.c (x i).1 c))) • s' a i

def ExtSt : Prop :=
  ∀ (X : Scheme.{0}) [IsIntegral X] (F G : X.Modules) (r m : ℕ) (A : X.Opens) (s : Fin r → Γ(F, A)) (φ ψ : F ⟶ G),
    genericPoint X ∈ A → GlobalTheory.VB.IsFrame s → GlobalTheory.VB.IsVB G m → (∀ i, φ.app A (s i) = ψ.app A (s i)) → φ = ψ

end GlobalTheory.OmegaHT
