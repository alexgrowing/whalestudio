import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitKOfIsAlgClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducesPl

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag GlobalTheory.LineNorm
open Formalism.MainNotions.DIV.Cons (intO)
open scoped TensorProduct Matrix
open MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RootFrameB

def colMinor {K : Type} [CommRing K] {n r : ℕ} (X : Matrix (Fin n) (Fin r) K) (k : ℕ) (hk : k ≤ r) (σ : Fin k → Fin n) : K :=
  (Matrix.of fun a l : Fin k => X (σ a) (Fin.castLE hk l)).det

def lo {r s N : ℕ} (h : r + s = N) (i : Fin r) : Fin N := ⟨i, by omega⟩

def hi {r s N : ℕ} (h : r + s = N) (l : Fin s) : Fin N := ⟨N - 1 - l, by omega⟩

section Cover

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

def Tst (V : Cover Y) (W : Y.X.Opens) (p : ℕ) (v : HeightOneSpectrum (𝓞 F)) (e : TrueGeo.Ext v) (y : AlgPt Y)
    (z : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp e.O ⟶ V.X) : Prop :=
  resP v = p ∧ below y.1 ∈ W ∧ z ≫ V.π = y.1 ∧ spMap e.O.subtype ≫ yt = z ≫ V.j

def vals (V : Cover Y) {n r : ℕ} (X : Matrix (Fin n) (Fin r) V.G.functionField) (T : Y.X → Matrix (Fin r) (Fin r) Y.Fn)
    (z : Sp (AlgebraicClosure F) ⟶ V.G) (x : Y.X) : Matrix (Fin n) (Fin r) (AlgebraicClosure F) :=
  (X * ((T x).map V.φ)⁻¹).map (TrueGeo.valAt z)

def PowRead (V : Cover Y) (p : ℕ) (f : Y.X → Y.Fn) (l : PtFn Y) : Prop :=
  ∃ m : ℕ, 0 < m ∧ ∀ x : V.X, ¬ IsUnit (p : V.X.presheaf.stalk x) → ∃ (U : V.X.Opens) (r : V.G.functionField), x ∈ U ∧
    (∀ z : V.G, V.j z ∈ U → UnitAt z (V.φ (f (V.π z)) ^ m * r)) ∧
    ∀ v e y z yt, Tst V ⊤ p v e y z yt → ⊤ ≤ yt ⁻¹ᵁ U →
      m * l v e y = Real.log (e.w (TrueGeo.valAt z (V.φ (f (below y.1)) ^ m * r)))

def SideData (V : Cover Y) (W : Y.X.Opens) (p : ℕ) {J : Type} (U : J → V.X.Opens) {n r : ℕ}
    (X : J → Matrix (Fin n) (Fin r) V.G.functionField) (T : Y.X → Matrix (Fin r) (Fin r) Y.Fn)
    (f : Fin r → Y.X → Y.Fn) (l : Fin r → PtFn Y) : Prop :=
  (∀ x, (T x).BlockTriangular id ∧ ∀ i, UnitAt x (f i x * T x i i)) ∧
  (∀ a (z : V.G), V.j z ∈ U a → ∀ k i, RegAt z ((X a * ((T (V.π z)).map V.φ)⁻¹) k i)) ∧
  ∀ v e y z yt, Tst V W p v e y z yt → ∃ ν : ℕ → ℝ, (∀ k, k ≤ r → 0 < ν k) ∧
    (∀ i : Fin r, l i v e y = Real.log (e.w (TrueGeo.valAt y.1 (f i (below y.1) * T (below y.1) i i))) +
      Real.log (ν ((i : ℕ) + 1)) - Real.log (ν (i : ℕ))) ∧
    ∀ a, ⊤ ≤ yt ⁻¹ᵁ U a →
      (∀ k (hk : k ≤ r) σ, e.w (colMinor (vals V (X a) T z (below y.1)) k hk σ) ≤ ν k) ∧
      (∀ k (hk : k ≤ r), ∃ σ, e.w (colMinor (vals V (X a) T z (below y.1)) k hk σ) = ν k) ∧
      ∀ b, ⊤ ≤ yt ⁻¹ᵁ U b → ∀ u : Fin r → AlgebraicClosure F, (∀ k, e.w ((vals V (X a) T z (below y.1) *ᵥ u) k) ≤ 1) →
        ∀ k, e.w ((vals V (X b) T z (below y.1) *ᵥ u) k - (vals V (X a) T z (below y.1) *ᵥ u) k) < 1

def Orth (V : Cover Y) (W : Y.X.Opens) (p : ℕ) {J : Type} (U : J → V.X.Opens) {n r s : ℕ}
    (X : J → Matrix (Fin n) (Fin r) V.G.functionField) (T : Y.X → Matrix (Fin r) (Fin r) Y.Fn)
    (X' : J → Matrix (Fin n) (Fin s) V.G.functionField) (T' : Y.X → Matrix (Fin s) (Fin s) Y.Fn) : Prop :=
  ∀ v e y z yt, Tst V W p v e y z yt → ∀ a, ⊤ ≤ yt ⁻¹ᵁ U a →
    ∀ (u : Fin r → AlgebraicClosure F) (u' : Fin s → AlgebraicClosure F),
      (∀ k, e.w ((vals V (X a) T z (below y.1) *ᵥ u) k) ≤ 1) → (∀ k, e.w ((vals V (X' a) T' z (below y.1) *ᵥ u') k) ≤ 1) →
      e.w ((vals V (X a) T z (below y.1) *ᵥ u) ⬝ᵥ (vals V (X' a) T' z (below y.1) *ᵥ u')) < 1

def FrameOn (V : Cover Y) (W : Y.X.Opens) (p : ℕ) (U : V.X.Opens) {n r : ℕ}
    (X : Matrix (Fin n) (Fin r) V.G.functionField) (T : Y.X → Matrix (Fin r) (Fin r) Y.Fn)
    (f : Fin r → Y.X → Y.Fn) (l : Fin r → PtFn Y) (M : Matrix (Fin n) (Fin r) V.X.functionField)
    (c : Fin r → V.G.functionFieldˣ) (σ : Fin r → Fin n) : Prop :=
  (∀ x ∈ U, ¬ IsUnit (p : V.X.presheaf.stalk x) → ∀ k i, RegAt x (M k i)) ∧ (M.submatrix σ id).det = 1 ∧
  (∀ i (z : V.G), V.j z ∈ U → UnitAt z (V.φ (f i (V.π z)) * c i)) ∧
  ∀ v e y z yt, Tst V W p v e y z yt → ⊤ ≤ yt ⁻¹ᵁ U →
    (∀ i, l i v e y = Real.log (e.w (TrueGeo.valAt z (V.φ (f i (below y.1)) * (c i : V.G.functionField))))) ∧
    ∃ β : Matrix (Fin r) (Fin r) (AlgebraicClosure F), β.BlockTriangular id ∧
      M.map (TrueGeo.valAt (z ≫ V.j)) = vals V X T z (below y.1) * β ∧
      ∀ i, β i i * TrueGeo.valAt z (V.φ (f i (below y.1)) * (c i : V.G.functionField)) =
        TrueGeo.valAt y.1 (f i (below y.1) * T (below y.1) i i)

def PairData {C : CxSt F} {N : ℕ} (A : Fin N → Adl C Y) (p : ℕ) : Prop :=
  ∃ (V : Cover Y) (W : Y.X.Opens) (J : Type) (U : J → V.X.Opens) (r s : ℕ) (h : r + s = N)
    (X : J → Matrix (Fin N) (Fin r) V.G.functionField) (T : Y.X → Matrix (Fin r) (Fin r) Y.Fn)
    (X' : J → Matrix (Fin N) (Fin s) V.G.functionField) (T' : Y.X → Matrix (Fin s) (Fin s) Y.Fn),
    genericPoint Y.X ∈ W ∧ (∀ x : V.X, ¬ IsUnit (p : V.X.presheaf.stalk x) → ∃ a, x ∈ U a) ∧
    (∀ i, PowRead V p (genAt (A i).D) (A i).lg) ∧
    SideData V W p U X T (fun i => genAt (A (lo h i)).D) (fun i => (A (lo h i)).lg) ∧
    SideData V W p U X' T' (fun i x => (genAt (A (hi h i)).D x)⁻¹) (fun i v e y => -(A (hi h i)).lg v e y) ∧
    Orth V W p U X T X' T'

end Cover

section Chars

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

def IsLabel (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) {R : Type} [CommRing R] (y : Sp R ⟶ Xo.XF c) (q : ℕ)
    (lb : Dw.La → (Over.mk y ⟶ Z.oF.t.G)) (ζ : Rˣ) : Prop :=
  IsPrimitiveRoot ζ q ∧ (∀ a b, lb (a + b) = lb a * lb b) ∧ (∀ (o : 𝓞 E) a, lb (o • a) = lb a ≫ Z.oF.t.act.act o) ∧
    (∀ a, lb a ^ q = 1) ∧ ∀ a b, Out.WeilIs Z.oF.t.G Z.oF.t.PP.L (q : ℤ) (lb a) (lb b) (unitOn (ζ ^ Dw.EF a b))

def WeilLab (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) {p : ℕ} [Fact p.Prime] (x : Sp ↥(intO ℂ_[p]) ⟶ Z.X)
    (y : Sp ℂ_[p] ⟶ Xo.XF c) (q : ℕ) (ch : Dw.La → TorsChar Z.t x q) : Prop :=
  ∃ (lb : Dw.La → (Over.mk y ⟶ Z.oF.t.G)) (ζ : ℂ_[p]ˣ), IsLabel Z y q lb ζ ∧
    ∀ a (w : Over.mk (spMap (algebraMap ↥(intO ℂ_[p]) ↥(intO ℂ_[p])) ≫ x) ⟶ Z.t.G) (σ : Over.mk y ⟶ Z.oF.t.G),
      w ^ q = 1 → σ.left ≫ Z.m.φ = spMap (intO ℂ_[p]).subtype ≫ w.left →
      Out.WeilIs Z.oF.t.G Z.oF.t.PP.L (q : ℤ) (lb a) σ
        (unitOn (Units.map (intO ℂ_[p]).subtype.toMonoidHom ((ch a).χ ↥(intO ℂ_[p]) w)))

def LabFam (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) {S : Scheme.{0}} (ρ : S ⟶ Z.X) (p : ℕ) [Fact p.Prime] (n : ℕ) : Prop :=
  ∃ ch : Dw.La → ∀ x : Sp ↥(intO ℂ_[p]) ⟶ S, TorsChar Z.t (x ≫ ρ) (p ^ n),
    (∀ x (y : Sp ℂ_[p] ⟶ Xo.XF c), spMap (intO ℂ_[p]).subtype ≫ x ≫ ρ = y ≫ Z.j →
      WeilLab Z (x ≫ ρ) y (p ^ n) fun a => ch a x) ∧
    ∀ (U : S.Opens) (hU : IsAffineOpen U) (g : ℕ) (e : Fin g → (Sp (DualNumber Γ(S, U)) ⟶ Z.t.G.left)),
      IsTanBasis Z.t (R := Γ(S, U)) (hU.fromSpec ≫ ρ) e → ∃ h : Dw.La → Fin g → Γ(S, U),
        ∀ (φ : Γ(S, U) →+* ↥(intO ℂ_[p])) (x : Sp ↥(intO ℂ_[p]) ⟶ S), spMap φ ≫ hU.fromSpec = x →
          ∀ a, DlogIs Z.t p n (ch a x) (fun i => spMap (dualMap φ) ≫ e i) (fun i => φ (h a i))

variable (Dw) in

def pr {K : Type} [CommRing K] (y : K ⊗[ℤ] Dw.La) (a : Dw.La) : K := Dw.EF.baseChange K y (1 ⊗ₜ a)

variable (Dw) in

def IsEigL {K : Type} [CommRing K] (σ : 𝓞 E →+* K) (y : K ⊗[ℤ] Dw.La) : Prop :=
  ∀ o : 𝓞 E, ((LinearMap.lsmul (𝓞 E) Dw.La o).restrictScalars ℤ).baseChange K y = σ o • y

variable (Dw) in

def HTLin {X : Scheme.{0}} (t : SAB H X) (p : ℕ) [Fact p.Prime] (n : ℕ) (x : Sp ↥(intO ℂ_[p]) ⟶ X)
    (ch : Dw.La → TorsChar t x (p ^ n)) {g : ℕ} (e : Fin g → (Sp (DualNumber ↥(intO ℂ_[p])) ⟶ t.G.left))
    (b : (Fin g → ℂ_[p]) →ₗ[ℂ_[p]] ℂ_[p] ⊗[ℤ] Dw.La) : Prop :=
  (∀ a (h : Fin g → ↥(intO ℂ_[p])), DlogIs t p n (ch a) e h →
    ∀ i, ‖(h i : ℂ_[p]) - pr Dw (b (Pi.single i 1)) a‖ ≤ (p : ℝ)⁻¹ ^ n) ∧
  (∀ cf w, IsCombAtG t (spMap (intO ℂ_[p]).subtype ≫ x) (fun i => spMap (dualMap (intO ℂ_[p]).subtype) ≫ e i) cf w →
    (w ∈ latHT t p (spMap (intO ℂ_[p]).subtype ≫ x) ↔ ∀ a, ‖pr Dw (b cf) a‖ ≤ 1) ∧
    ∀ σ : 𝓞 E →+* ℂ_[p], GlobalTheory.FlatModel.IsEigG t σ w → IsEigL Dw σ (b cf)) ∧
  ∀ cf cf', (∀ a, ‖pr Dw (b cf) a‖ ≤ 1) → (∀ a, ‖pr Dw (b cf') a‖ ≤ 1) →
    ‖Dw.EF.baseChange ℂ_[p] (b cf) (b cf')‖ ≤ (p : ℝ)⁻¹ ^ n

variable (Dw) in

def CutL {K : Type} [NormedField K] (σ : 𝓞 E →+* K) {M N : ℕ} (a : Fin M → Dw.La) (T : Fin N → Fin M → K) (δ : K) : Prop :=
  (∀ j m, ‖T j m‖ ≤ 1) ∧ ∀ y, IsEigL Dw σ y → ((∀ j, ‖∑ m, T j m * pr Dw y (a m)‖ ≤ 1) ↔ ∀ b, ‖δ * pr Dw y b‖ ≤ 1)

variable (Dw) in

def DualL {K : Type} [CommRing K] (σ σ' : 𝓞 E →+* K) {M N : ℕ} (a : Fin M → Dw.La) (T S : Fin N → Fin M → K) : Prop :=
  ∀ y y', IsEigL Dw σ y → IsEigL Dw σ' y' →
    ∑ j, (∑ m, T j m * pr Dw y (a m)) * (∑ m, S j m * pr Dw y' (a m)) = -Dw.EF.baseChange K y y'

end Chars

section Cut

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  (t : SAB H X)

def CutBy {C : Type} [NormedField C] (x : Sp C ⟶ X) (Λ : Set (Sp (DualNumber C) ⟶ t.G.left)) {n r : ℕ}
    (u : Fin r → (Sp (DualNumber C) ⟶ t.G.left)) (P : Matrix (Fin n) (Fin r) C) (δ : C) : Prop :=
  (∀ cf, P *ᵥ cf = 0 → cf = 0) ∧ ∀ cf w, IsCombAtG t x u cf w → (w ∈ Λ ↔ ∀ k, ‖(P *ᵥ cf) k‖ ≤ ‖δ‖)

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

def CutAt (V : Cover Y) (W : Y.X.Opens) (p : ℕ) (ρ : Y.X ⟶ X) {J : Type} (U : J → V.X.Opens) {n r : ℕ}
    (f : ∀ y : Y.X, Fin r → (Sp (DualNumber (Y.X.presheaf.stalk y)) ⟶ t.G.left))
    (P : J → Matrix (Fin n) (Fin r) V.G.functionField) (T : Y.X → Matrix (Fin r) (Fin r) Y.Fn) (κ : ℝ) : Prop :=
  ∀ v e y z yt, Tst V W p v e y z yt → ∀ [Fact (resP v).Prime], ∃ δ : ℂ_[resP v], δ ≠ 0 ∧
    Real.log ‖δ‖ = -(κ * Real.log (resP v)) ∧ ∀ a, ⊤ ≤ yt ⁻¹ᵁ U a →
      CutBy t (spMap ((ioOf (resP v) e).comp (Scheme.stalkClosedPointTo y.1).hom) ≫ stalkPt Y (below y.1) ≫ ρ)
        (latHT t (resP v)
          (spMap ((ioOf (resP v) e).comp (Scheme.stalkClosedPointTo y.1).hom) ≫ stalkPt Y (below y.1) ≫ ρ))
        (fun i => spMap (dualMap ((ioOf (resP v) e).comp (Scheme.stalkClosedPointTo y.1).hom)) ≫ f (below y.1) i)
        ((vals V (P a) T z (below y.1)).map (ioOf (resP v) e)) δ ∧
      ∀ b, ⊤ ≤ yt ⁻¹ᵁ U b → ∀ u : Fin r → ℂ_[resP v],
        (∀ k, ‖((vals V (P a) T z (below y.1)).map (ioOf (resP v) e) *ᵥ u) k‖ ≤ 1) →
        ∀ k, ‖((vals V (P b) T z (below y.1)).map (ioOf (resP v) e) *ᵥ u) k -
          ((vals V (P a) T z (below y.1)).map (ioOf (resP v) e) *ᵥ u) k‖ < 1

end Cut

def covMat {K : Type} [CommRing K] {M N g r : ℕ} (T : Fin N → Fin M → K) (h : Fin M → Fin g → K) (A : Fin r → Fin g → K) :
    Matrix (Fin N) (Fin r) K :=
  Matrix.of fun j i => ∑ m, T j m * ∑ k, h m k * A i k

end GlobalTheory.RootFrameB

end
