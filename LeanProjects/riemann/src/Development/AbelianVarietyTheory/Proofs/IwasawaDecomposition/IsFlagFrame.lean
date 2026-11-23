import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LineModel
import Development.AbelianVarietyTheory.Statements.HeightBoundStatement.HTBoundSt

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar
open Formalism.MainNotions.DIV.Cons (intO)
open MonObj

namespace GlobalTheory.LineNorm

attribute [local instance] Over.cartesianMonoidalCategory

section Models

variable {F : Type} [Field F] [NumberField F]

abbrev PtFn (Y : Var F) : Type := ∀ v : HeightOneSpectrum (𝓞 F), Ext v → AlgPt Y → ℝ

def FromModel (Y : Var F) (Δ : Y.Dv) (t : Y.X → Y.Fnˣ) (φ : PtFn Y) : Prop :=
  ∃ (M : GlobalTheory.TrueGeo.Model Y) (L : LB M.X) (m : ℕ+) (r : (L.pull M.j).ι → Y.Fnˣ), L.IsLB ∧
    Presents ((m : ℕ) • Δ) (L.pull M.j) r ∧
    ∀ (v : HeightOneSpectrum (𝓞 F)) (e : Ext v) (y : AlgPt Y) (yt : Sp e.O ⟶ M.X) (i : (L.pull M.j).ι),
      spMap e.O.subtype ≫ yt = y.1 ≫ M.j → ⊤ ≤ yt ⁻¹ᵁ L.U (i PUnit.unit) →
      ((m : ℕ) : ℝ) * φ v e y = Real.log (e.w (valAt y.1 (((t (below y.1))⁻¹ ^ (m : ℕ) * r i : Y.Fnˣ) : Y.Fn)))

def Generates {Y : Var F} (M : GlobalTheory.TrueGeo.Model Y) (t : Y.X → Y.Fnˣ) (V : M.X.Opens) (d : ℕ) {n : ℕ}
    (s : Fin n → Y.Fn) : Prop :=
  ∀ y : Y.X, M.j y ∈ V → (∀ i, RegAt y (s i * (((t y)⁻¹ ^ d : Y.Fnˣ) : Y.Fn))) ∧
    ∃ i, UnitAt y (s i * (((t y)⁻¹ ^ d : Y.Fnˣ) : Y.Fn))

def LocMax {Y : Var F} (M : GlobalTheory.TrueGeo.Model Y) (t : Y.X → Y.Fnˣ) (φ : PtFn Y) (z : M.X) : Prop :=
  ∃ (V : M.X.Opens) (d : ℕ+) (n : ℕ) (s : Fin n → Y.Fn), z ∈ V ∧ Generates M t V d s ∧
    ∀ (v : HeightOneSpectrum (𝓞 F)) (e : Ext v) (y : AlgPt Y) (yt : Sp e.O ⟶ M.X),
      spMap e.O.subtype ≫ yt = y.1 ≫ M.j → ⊤ ≤ yt ⁻¹ᵁ V →
      ((d : ℕ) : ℝ) * φ v e y =
        Real.log (⨆ i, e.w (valAt y.1 (s i * (((t (below y.1))⁻¹ ^ (d : ℕ) : Y.Fnˣ) : Y.Fn))))

end Models

section Tangent

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  (t : SAB H X)

def IsTanBasis {R : Type} [CommRing R] (x : Sp R ⟶ X) {g : ℕ} (e : Fin g → (Sp (DualNumber R) ⟶ t.G.left)) : Prop :=
  (∀ i, IsTanAtG t x (e i)) ∧ ∀ (S : Type) [CommRing S] (φ : R →+* S) (w : Sp (DualNumber S) ⟶ t.G.left),
    IsTanAtG t (spMap φ ≫ x) w →
      ∃! a : Fin g → S, IsCombAtG t (spMap φ ≫ x) (fun i => spMap (dualMap φ) ≫ e i) a w

def IsIndep {R : Type} [CommRing R] (x : Sp R ⟶ X) {m : ℕ} (u : Fin m → (Sp (DualNumber R) ⟶ t.G.left)) : Prop :=
  ∀ cf cf' w, IsCombAtG t x u cf w → IsCombAtG t x u cf' w → cf = cf'

def minor {R : Type} [CommRing R] {m g k : ℕ} (a : Fin m → Fin g → R) (hk : k ≤ m) (s : Fin k → Fin g) : R :=
  (Matrix.of fun l i => a (Fin.castLE hk l) (s i)).det

def DlogIs {O : Type} [CommRing O] {x : Sp O ⟶ X} (p n : ℕ) (c : TorsChar t x (p ^ n)) {g : ℕ}
    (e : Fin g → (Sp (DualNumber O) ⟶ t.G.left)) (h : Fin g → O) : Prop :=
  ∀ (a : Fin g → O) (v : Sp (DualNumber O) ⟶ t.G.left), IsCombAtG t x e a v →
    ∀ w : Over.mk (spMap (algebraMap O (DualNumber (O ⧸ Ideal.span {(p : O) ^ n}))) ≫ x) ⟶ t.G,
      w.left = spMap (dualMap (Ideal.Quotient.mk (Ideal.span {(p : O) ^ n}))) ≫ v →
        (c.χ _ w : DualNumber (O ⧸ Ideal.span {(p : O) ^ n})).snd =
          Ideal.Quotient.mk (Ideal.span {(p : O) ^ n}) (∑ i, h i * a i)

def SplitTors {R : Type} [CommRing R] (x : Sp R ⟶ X) (q : ℕ) : Prop :=
  ∀ (Ω : Type) [Field Ω] (io : FractionRing R →+* Ω)
    (w : Over.mk (spMap (io.comp (algebraMap R (FractionRing R))) ≫ x) ⟶ t.G), w ^ q = 1 →
      ∃ w₀ : Sp (FractionRing R) ⟶ t.G.left, spMap io ≫ w₀ = w.left

def Thru {R B : Type} [CommRing R] [CommRing B] [Algebra R B] (u : Sp B ⟶ t.G.left) {S : Type} [CommRing S]
    (φ : R →+* S) (w : Sp S ⟶ t.G.left) : Prop :=
  ∃ β : B →+* S, β.comp (algebraMap R B) = φ ∧ spMap β ≫ u = w

structure IsFinPart {R : Type} [CommRing R] (x : Sp R ⟶ X) (q : ℕ) {B : Type} [CommRing B] [Algebra R B]
    (u : Over.mk (spMap (algebraMap R B) ≫ x) ⟶ t.G) : Prop where
  finite : Module.Finite R B
  free : Module.Free R B
  tors : u ^ q = 1
  mono : ∀ (S : Type) [CommRing S] (β β' : B →+* S), β.comp (algebraMap R B) = β'.comp (algebraMap R B) →
    spMap β ≫ u.left = spMap β' ≫ u.left → β = β'
  isOpen : ∀ (S : Type) [CommRing S] (φ : R →+* S) (w : Over.mk (spMap φ ≫ x) ⟶ t.G), w ^ q = 1 →
    (∀ 𝔪 : Ideal S, 𝔪.IsMaximal →
      Thru t u.left ((Ideal.Quotient.mk 𝔪).comp φ) (spMap (Ideal.Quotient.mk 𝔪) ≫ w.left)) → Thru t u.left φ w.left
  one : ∀ (S : Type) [CommRing S] (φ : R →+* S), Thru t u.left φ (1 : Over.mk (spMap φ ≫ x) ⟶ t.G).left
  mul : ∀ (S : Type) [CommRing S] (φ : R →+* S) (w w' : Over.mk (spMap φ ≫ x) ⟶ t.G),
    Thru t u.left φ w.left → Thru t u.left φ w'.left → Thru t u.left φ (w * w').left
  sect : ∀ (k : Type) [Field k] (β : B →+* k), ∃ σ : B →ₐ[R] R, β = (β.comp (algebraMap R B)).comp σ.toRingHom
  inj : ∀ b : B, (∀ σ : B →ₐ[R] R, σ b = 0) → b = 0

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

open Classical in

def stepLog (ρ : Y.X ⟶ X) {m : ℕ}
    (f : ∀ y : Y.X, Fin m → (Sp (DualNumber (Y.X.presheaf.stalk y)) ⟶ t.G.left)) (q : ℕ) (i : Fin m) : PtFn Y :=
  fun v ε y =>
    if hp : (resP v).Prime then
      haveI := Fact.mk hp
      let ψ : Y.X.presheaf.stalk (below y.1) →+* ℂ_[resP v] := (ioOf (resP v) ε).comp (Scheme.stalkClosedPointTo y.1).hom
      (-Real.log (ε.w (resP v)) / Real.log (resP v)) *
        Real.log (grNorm t (spMap ψ ≫ stalkPt Y (below y.1) ≫ ρ)
          (lat t (resP v) (spMap ψ ≫ stalkPt Y (below y.1) ≫ ρ) (decide (resP v = q)))
          (fun l => spMap (dualMap ψ) ≫ f (below y.1) l) i)
    else 0

structure IsFlagFrame (ρ : Y.X ⟶ X) {m : ℕ} (u₀ : Fin m → (Sp (DualNumber Y.Fn) ⟶ t.G.left))
    (f : ∀ y : Y.X, Fin m → (Sp (DualNumber (Y.X.presheaf.stalk y)) ⟶ t.G.left)) (d : Y.X → Fin m → Y.Fnˣ) : Prop where
  tan : ∀ y l, IsTanAtG t (stalkPt Y y ≫ ρ) (f y l)
  tri : ∀ y i, ∃ cf : Fin m → Y.Fn, cf i = d y i ∧ (∀ k, i < k → cf k = 0) ∧
    IsCombAtG t (genericPt Y ≫ ρ)
      (fun k => spMap (dualMap (algebraMap (Y.X.presheaf.stalk y) Y.X.functionField)) ≫ f y k) cf (u₀ i)
  indep : ∀ y (k : Type) [Field k] (ψ : Y.X.presheaf.stalk y →+* k),
    IsIndep t (spMap ψ ≫ stalkPt Y y ≫ ρ) (fun l => spMap (dualMap ψ) ≫ f y l)

end Tangent

end GlobalTheory.LineNorm
