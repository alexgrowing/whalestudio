import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Desc

section Fields

variable {X Y V : Scheme.{0}} [IsIntegral X] [IsIntegral Y]

def gp (X : Scheme.{0}) [IsIntegral X] : Sp X.functionField ⟶ X := X.fromSpecStalk (genericPoint X)

def cst {R : Type} [CommRing R] (p : X ⟶ Sp R) : R →+* X.functionField :=
  (fnOf ⊤ trivial).comp (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)

def PFF (i : V ⟶ Y) (φ : V ⟶ X) (θ : X.functionField →+* Y.functionField) : Prop :=
  ∃ l : Sp Y.functionField ⟶ V, l ≫ i = gp Y ∧ l ≫ φ = spMap θ ≫ gp X

def PPull (i : V ⟶ Y) (φ : V ⟶ X) (θ : X.functionField →+* Y.functionField) (D : CartierDiv X) (D' : CartierDiv Y) : Prop :=
  ∀ (v : V) (g : X.functionFieldˣ), D.IsEqn (φ v) g → D'.IsEqn (i v) (Units.map θ.toMonoidHom g)

def Sec (D : CartierDiv X) (k : ℕ) : Set X.functionField := {u | ∀ x, (k • D).RegularAt x u}

def locus (D : CartierDiv X) (k : ℕ) (u : X.functionField) : Set X := {x | (k • D).GeneratesAt x u}

def AmpleDiv (D : CartierDiv X) : Prop :=
  ∀ x : X, ∃ k, 1 ≤ k ∧ ∃ u ∈ Sec D k, ∃ U : X.Opens, IsAffineOpen U ∧ (U : Set X) = locus D k u ∧ x ∈ U

def regSet (x : X) : Set X.functionField := {u | RegAt x u}

end Fields

def Vert {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) (f : R) (x : X) : Prop :=
  ringKrullDim (X.presheaf.stalk x) = 1 ∧ f ∈ (p x).asIdeal

section Spans

variable {R R₁ F F₁ : Type} [CommRing R] [CommRing R₁] [CommRing F] [CommRing F₁]

def spanBy (c : R₁ →+* F₁) (T : Set F₁) : Set F₁ :=
  {v | ∃ (n : ℕ) (r : Fin n → R₁) (t : Fin n → F₁), (∀ i, t i ∈ T) ∧ v = ∑ i, c (r i) * t i}

def LinDisj (c₀ : R →+* F) (c : R₁ →+* F₁) (θ : F →+* F₁) : Prop :=
  ∀ (n : ℕ) (u : Fin n → F), (∀ r : Fin n → R, ∑ i, c₀ (r i) * u i = 0 → r = 0) →
    ∀ r : Fin n → R₁, ∑ i, c (r i) * θ (u i) = 0 → r = 0

def GaussAt (c : R₁ →+* F₁) (q : Ideal R₁) (θ : F →+* F₁) (W : Set F) (W₁ : Set F₁) : Prop :=
  ∀ v : F₁, (∃ d : R₁, d ≠ 0 ∧ c d * v ∈ spanBy c (Set.range θ)) →
    (v ∈ W₁ ↔ ∃ s : R₁, s ∉ q ∧ c s * v ∈ spanBy c (θ '' W))

structure GradedFam (c₀ : R →+* F) (N : ℕ → Set F) : Prop where
  one : (1 : F) ∈ N 0
  zero : ∀ k, (0 : F) ∈ N k
  add : ∀ k, ∀ a ∈ N k, ∀ b ∈ N k, a + b ∈ N k
  smul : ∀ k (r : R), ∀ a ∈ N k, c₀ r * a ∈ N k
  mul : ∀ k l, ∀ a ∈ N k, ∀ b ∈ N l, a * b ∈ N (k + l)

end Spans

structure IsModel {R F : Type} [CommRing R] [Field F] (c₀ : R →+* F) (N : ℕ → Set F) {P : Scheme.{0}} [IsIntegral P]
    (p : P ⟶ Sp R) (ψ : P.functionField →+* F) (Dp : ℕ → F → P.Opens) : Prop where
  sep : IsSeparated p
  const : ψ.comp (cst p) = c₀
  affine : ∀ k, 1 ≤ k → ∀ b ∈ N k, IsAffineOpen (Dp k b)
  cover : ∀ z : P, ∃ k, 1 ≤ k ∧ ∃ b ∈ N k, z ∈ Dp k b
  gen : ∀ k, 1 ≤ k → ∀ b ∈ N k, (genericPoint P ∈ Dp k b ↔ b ≠ 0)
  ring : ∀ k, 1 ≤ k → ∀ b ∈ N k, b ≠ 0 → ∀ u : F,
    (∃ v, (∀ z ∈ Dp k b, RegAt z v) ∧ ψ v = u) ↔ ∃ m, ∃ a ∈ N (k * m), u = a / b ^ m
  mem : ∀ k, 1 ≤ k → ∀ b ∈ N k, ∀ z ∈ Dp k b, ∀ l, 1 ≤ l → ∀ a ∈ N l,
    (z ∈ Dp l a ↔ ∃ v, UnitAt z v ∧ ψ v = a ^ k / b ^ l)

def MulAgree {S₁ S₂ P : Scheme.{0}} (H₁ : Over S₁) [GrpObj H₁] (H₂ : Over S₂) [GrpObj H₂] (h₁ : H₁.left ⟶ P)
    (h₂ : H₂.left ⟶ P) : Prop :=
  ∀ (T : Scheme.{0}) (t₁ : T ⟶ S₁) (t₂ : T ⟶ S₂) (a b : Over.mk t₁ ⟶ H₁) (a' b' : Over.mk t₂ ⟶ H₂),
    a.left ≫ h₁ = a'.left ≫ h₂ → b.left ≫ h₁ = b'.left ≫ h₂ → (a * b).left ≫ h₁ = (a' * b').left ≫ h₂

def OneAgree {S S₁ S₂ P : Scheme.{0}} (s₁ : S₁ ⟶ S) (s₂ : S₂ ⟶ S) (H₁ : Over S₁) [GrpObj H₁] (H₂ : Over S₂) [GrpObj H₂]
    (h₁ : H₁.left ⟶ P) (h₂ : H₂.left ⟶ P) : Prop :=
  ∀ (T : Scheme.{0}) (t₁ : T ⟶ S₁) (t₂ : T ⟶ S₂), t₁ ≫ s₁ = t₂ ≫ s₂ →
    (1 : Over.mk t₁ ⟶ H₁).left ≫ h₁ = (1 : Over.mk t₂ ⟶ H₂).left ≫ h₂

def OpenIn {S S₁ P Y : Scheme.{0}} (h : Y ⟶ P) (q : Y ⟶ S₁) (p : P ⟶ S) (s : S₁ ⟶ S) : Prop :=
  ∃ w : h ≫ p = q ≫ s, IsOpenImmersion (pullback.lift h q w)

structure Chart {X S : Scheme.{0}} (j : X ⟶ S) (A : Over X) [GrpObj A] (x : S) where

  R : Type
  [cr : CommRing R]
  [reg : IsRegularLocalRing R]
  [dom : IsDomain R]
  complete : IsAdicComplete (maximalIdeal R) R
  charZero : CharZero R

  ξ : Sp R ⟶ S
  centre : ξ (closedPoint R) = x
  etc : IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom
  unr : ((residue R).comp (Scheme.stalkClosedPointTo ξ).hom).FormallyUnramified

  G : Over (Sp R)
  [grp : GrpObj G]
  semi : IsSemiAbelian G

  y : Sp (FractionRing R) ⟶ X
  hy : y ≫ j = jK R ≫ ξ

  α : pullback G.hom (jK R) ⟶ A.left
  gen : IsGrpPullback ((Over.pullback (jK R)).obj G) A y α

attribute [instance] Chart.cr Chart.reg Chart.dom Chart.grp

abbrev awayMap {R : Type} [CommRing R] (f : R) : Sp (Localization.Away f) ⟶ Sp R :=
  spMap (algebraMap R (Localization.Away f))

structure Setup where

  R : Type
  [cr : CommRing R]
  [dom : IsDomain R]
  [noeth : IsNoetherianRing R]
  [normal : IsIntegrallyClosed R]

  f : R
  hf : f ≠ 0

  A : Over (Sp (Localization.Away f))
  [grp : GrpObj A]
  ab : IsAbelianScheme A
  [int : IsIntegral A.left]

  D : CartierDiv A.left
  amp : AmpleDiv D

  C : ∀ x : Sp R, Chart (awayMap f) A x
  [intC : ∀ x, IsIntegral (C x).G.left]

  ρ : ∀ x, R →+* (C x).R
  hρ : ∀ x, (C x).ξ = spMap (ρ x)
  flat : ∀ x, (ρ x).Flat

  V : ∀ x, (C x).G.left.Opens
  hV : ∀ x (z : (C x).G.left), z ∈ V x ↔ ρ x f ∉ ((C x).G.hom z).asIdeal

  φ : ∀ x, (V x).toScheme ⟶ A.left
  cart : ∀ x, IsPullback (φ x) ((V x).ι ≫ (C x).G.hom) (A.hom ≫ awayMap f) (spMap (ρ x))
  compat : ∀ x (T : Scheme.{0}) (t : T ⟶ pullback (C x).G.hom (jK (C x).R)) (t' : T ⟶ (V x).toScheme),
    t ≫ pullback.fst _ _ = t' ≫ (V x).ι → t ≫ (C x).α = t' ≫ φ x

  θ : ∀ x, A.left.functionField →+* (C x).G.left.functionField
  hθ : ∀ x, PFF (V x).ι (φ x) (θ x)

  D₁ : ∀ x, CartierDiv (C x).G.left
  pull : ∀ x, PPull (V x).ι (φ x) (θ x) D (D₁ x)
  noVert : ∀ x z, Vert (C x).G.hom (ρ x f) z → (D₁ x).IsEqn z 1
  amp₁ : ∀ x, AmpleDiv (D₁ x)

attribute [instance] Setup.cr Setup.dom Setup.noeth Setup.normal Setup.grp Setup.int Setup.intC

namespace Setup

variable (σ : Setup)

def c₀ : σ.R →+* σ.A.left.functionField := cst (σ.A.hom ≫ awayMap σ.f)

def W (x : Sp σ.R) : Set σ.A.left.functionField :=
  {u | ∀ z, Vert (σ.C x).G.hom (σ.ρ x σ.f) z → RegAt z (σ.θ x u)}

def N (k : ℕ) : Set σ.A.left.functionField := {u | u ∈ Sec σ.D k ∧ ∀ x, u ∈ σ.W x}

def Common : Prop :=
  ∀ (x x' : Sp σ.R) (Ω : Type) [Field Ω] (u : (σ.C x).R →+* Ω) (u' : (σ.C x').R →+* Ω),
    RingHom.ker u' = maximalIdeal _ → u.comp (σ.ρ x) = u'.comp (σ.ρ x') →
    ∃ (E : Type) (_ : CommRing E) (_ : IsRegularLocalRing E) (_ : IsDomain E) (a : (σ.C x).R →+* E) (b : (σ.C x').R →+* E)
      (v : E →+* Ω) (H : Over (Sp E)) (_ : GrpObj H) (_ : IsIntegral H.left) (πa : H.left ⟶ (σ.C x).G.left)
      (πb : H.left ⟶ (σ.C x').G.left) (θa : (σ.C x).G.left.functionField →+* H.left.functionField)
      (θb : (σ.C x').G.left.functionField →+* H.left.functionField),
      a.Flat ∧ b.Flat ∧ a.comp (σ.ρ x) = b.comp (σ.ρ x') ∧ RingHom.ker v = maximalIdeal E ∧ v.comp a = u ∧ v.comp b = u' ∧
      (RingHom.ker u).map a = maximalIdeal E ∧ IsSemiAbelian H ∧ IsGrpPullback H (σ.C x).G (spMap a) πa ∧
      IsGrpPullback H (σ.C x').G (spMap b) πb ∧ PFF (𝟙 _) πa θa ∧ PFF (𝟙 _) πb θb ∧ θa.comp (σ.θ x) = θb.comp (σ.θ x')

end Setup

structure Emb (σ : Setup) where

  P : Scheme.{0}
  [int : IsIntegral P]

  p : P ⟶ Sp σ.R
  sep : IsSeparated p

  ψ : P.functionField →+* σ.A.left.functionField

  ιA : σ.A.left ⟶ P
  cartA : IsPullback ιA σ.A.hom p (awayMap σ.f)
  ffA : PFF (𝟙 _) ιA ψ

  emb : ∀ x, (σ.C x).G.left ⟶ P
  openIn : ∀ x, OpenIn (emb x) (σ.C x).G.hom p (spMap (σ.ρ x))
  ff : ∀ x, PFF (𝟙 _) (emb x) ((σ.θ x).comp ψ)
  onV : ∀ x, σ.φ x ≫ ιA = (σ.V x).ι ≫ emb x

attribute [instance] Emb.int

def Emb.U {σ : Setup} (E : Emb σ) : Set E.P :=
  {z | ∃ (x : Sp σ.R) (y : (σ.C x).G.left), (σ.C x).G.hom y = closedPoint _ ∧ E.emb x y = z}

def Emb.LocGrp {σ : Setup} (E : Emb σ) (g : σ.R) (H : Over (Sp (Localization.Away g))) [GrpObj H] (h : H.left ⟶ E.P) : Prop :=
  Smooth H.hom ∧ QuasiCompact H.hom ∧ IsOpenImmersion h ∧ h ≫ E.p = H.hom ≫ awayMap g ∧ MulAgree H σ.A h E.ιA

def SqDec {S : Scheme.{0}} (A : Over S) [GrpObj A] (L M : LB A.left) : Prop :=
  ∃ (N a₀ r : ℕ) (a : Fin r → ℕ) (β : Fin r → (A ⟶ A)), 1 ≤ N ∧ 1 ≤ a₀ ∧ (∀ i, IsMonHom (β i)) ∧
    LBIso (lbPow L N) (LB.LinComb M (K := Option (Fin r)) (fun o => o.elim (𝟙 A.left) fun i => (β i).left)
      fun o => o.elim (a₀ : ℤ) fun i => (a i : ℤ))

def HasExt {X S : Scheme.{0}} (j : X ⟶ S) (A : Over X) [GrpObj A] : Prop :=
  ∃ (G : Over S) (_ : GrpObj G) (e : A.left ⟶ G.left), IsSemiAbelian G ∧ IsGrpPullback A G j e

theorem subset_spanBy {R₁ F₁ : Type} [CommRing R₁] [CommRing F₁] (c : R₁ →+* F₁) (T : Set F₁) : T ⊆ spanBy c T :=
  fun t ht => ⟨1, fun _ => 1, fun _ => t, fun _ => ht, by simp⟩

end GlobalTheory.Desc
