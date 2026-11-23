import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitKOfIsAlgClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag GlobalTheory.LineNorm
open Formalism.MainNotions.DIV.Cons (intO)
open scoped TensorProduct Matrix
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RootFrame

def colMinor {K : Type} [CommRing K] {n r : ℕ} (X : Matrix (Fin n) (Fin r) K) (k : ℕ) (hk : k ≤ r) (σ : Fin k → Fin n) : K :=
  (Matrix.of fun a l : Fin k => X (σ a) (Fin.castLE hk l)).det

def lead {K : Type} [CommRing K] {n r : ℕ} (X : Matrix (Fin n) (Fin r) K) (σ : Fin r → Fin n) (k : ℕ) (hk : k ≤ r) : K :=
  colMinor X k hk fun a => σ (Fin.castLE hk a)

def cram {K : Type} [Field K] {n r : ℕ} (X : Matrix (Fin n) (Fin r) K) (σ : Fin r → Fin n) : Matrix (Fin n) (Fin r) K :=
  Matrix.of fun ρ k => colMinor X (k + 1) k.2 (fun a => if (a : ℕ) < k then σ (Fin.castLE k.2 a) else ρ) /
    lead X σ (k + 1) k.2

def lo {r s N : ℕ} (h : r + s = N) (i : Fin r) : Fin N := ⟨i, by omega⟩

def hi {r s N : ℕ} (h : r + s = N) (l : Fin s) : Fin N := ⟨N - 1 - l, by omega⟩

def joinM {K : Type} {r s N : ℕ} (h : r + s = N) (M : Matrix (Fin N) (Fin r) K) (L : Matrix (Fin N) (Fin s) K) :
    Matrix (Fin N) (Fin N) K :=
  Matrix.of fun k i => if hi : (i : ℕ) < r then M k ⟨i, hi⟩ else L k ⟨N - 1 - i, by omega⟩

def covMat {K : Type} [CommRing K] {M N g r : ℕ} (T : Fin N → Fin M → K) (h : Fin M → Fin g → K) (A : Fin r → Fin g → K) :
    Matrix (Fin N) (Fin r) K :=
  Matrix.of fun j i => ∑ m, T j m * ∑ k, h m k * A i k

section Cover

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

def Tst (V : Cover Y) (W : Y.X.Opens) (p : ℕ) (v : HeightOneSpectrum (𝓞 F)) (e : TrueGeo.Ext v) (y : AlgPt Y)
    (z : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp e.O ⟶ V.X) : Prop :=
  resP v = p ∧ below y.1 ∈ W ∧ z ≫ V.π = y.1 ∧ spMap e.O.subtype ≫ yt = z ≫ V.j

def locM (V : Cover Y) {n r : ℕ} (X : Matrix (Fin n) (Fin r) V.G.functionField) (T : Y.X → Matrix (Fin r) (Fin r) Y.Fn)
    (x : Y.X) : Matrix (Fin n) (Fin r) V.G.functionField :=
  X * ((T x).map V.φ)⁻¹

def vals (V : Cover Y) {n r : ℕ} (X : Matrix (Fin n) (Fin r) V.G.functionField) (T : Y.X → Matrix (Fin r) (Fin r) Y.Fn)
    (z : Sp (AlgebraicClosure F) ⟶ V.G) (x : Y.X) : Matrix (Fin n) (Fin r) (AlgebraicClosure F) :=
  (locM V X T x).map (TrueGeo.valAt z)

def PowRead (V : Cover Y) (p : ℕ) (f : Y.X → Y.Fn) (l : PtFn Y) : Prop :=
  ∃ m : ℕ, 0 < m ∧ ∀ x : V.X, ¬ IsUnit (p : V.X.presheaf.stalk x) → ∃ (U : V.X.Opens) (r : V.G.functionField), x ∈ U ∧
    (∀ z : V.G, V.j z ∈ U → UnitAt z (V.φ (f (V.π z)) ^ m * r)) ∧
    ∀ v e y z yt, Tst V ⊤ p v e y z yt → ⊤ ≤ yt ⁻¹ᵁ U →
      m * l v e y = Real.log (e.w (TrueGeo.valAt z (V.φ (f (below y.1)) ^ m * r)))

def SideData (V : Cover Y) (W : Y.X.Opens) (p : ℕ) {J : Type} (U : J → V.X.Opens) {n r : ℕ}
    (X : J → Matrix (Fin n) (Fin r) V.G.functionField) (T : Y.X → Matrix (Fin r) (Fin r) Y.Fn)
    (f : Fin r → Y.X → Y.Fn) (l : Fin r → PtFn Y) : Prop :=
  (∀ x, (T x).BlockTriangular id ∧ ∀ i, UnitAt x (f i x * T x i i)) ∧
  (∀ a (z : V.G), V.j z ∈ U a → ∀ k i, RegAt z (locM V (X a) T (V.π z) k i)) ∧
  ∀ v e y z yt, Tst V W p v e y z yt → ∀ a, ⊤ ≤ yt ⁻¹ᵁ U a →
    (∃ ν : ℕ → ℝ, (∀ k, k ≤ r → 0 < ν k) ∧
      (∀ i : Fin r, l i v e y = Real.log (e.w (TrueGeo.valAt y.1 (f i (below y.1) * T (below y.1) i i))) +
        Real.log (ν ((i : ℕ) + 1)) - Real.log (ν (i : ℕ))) ∧
      (∀ k (hk : k ≤ r) σ, e.w (colMinor (vals V (X a) T z (below y.1)) k hk σ) ≤ ν k) ∧
      ∀ k (hk : k ≤ r), ∃ σ, e.w (colMinor (vals V (X a) T z (below y.1)) k hk σ) = ν k) ∧
    ∀ b, ⊤ ≤ yt ⁻¹ᵁ U b → ∀ u : Fin r → AlgebraicClosure F, (∀ k, e.w ((vals V (X a) T z (below y.1) *ᵥ u) k) ≤ 1) →
      ∀ k, e.w ((vals V (X b) T z (below y.1) *ᵥ u) k - (vals V (X a) T z (below y.1) *ᵥ u) k) < 1

def Orth (V : Cover Y) (W : Y.X.Opens) (p : ℕ) {J : Type} (U : J → V.X.Opens) {n r s : ℕ}
    (X : J → Matrix (Fin n) (Fin r) V.G.functionField) (T : Y.X → Matrix (Fin r) (Fin r) Y.Fn)
    (X' : J → Matrix (Fin n) (Fin s) V.G.functionField) (T' : Y.X → Matrix (Fin s) (Fin s) Y.Fn) : Prop :=
  ∀ v e y z yt, Tst V W p v e y z yt → ∀ a, ⊤ ≤ yt ⁻¹ᵁ U a →
    ∀ (u : Fin r → AlgebraicClosure F) (u' : Fin s → AlgebraicClosure F),
      (∀ k, e.w ((vals V (X a) T z (below y.1) *ᵥ u) k) ≤ 1) → (∀ k, e.w ((vals V (X' a) T' z (below y.1) *ᵥ u') k) ≤ 1) →
      e.w ((vals V (X a) T z (below y.1) *ᵥ u) ⬝ᵥ (vals V (X' a) T' z (below y.1) *ᵥ u')) < 1

def GoodOn (V : Cover Y) (W : Y.X.Opens) (p : ℕ) (U : V.X.Opens) {n r : ℕ}
    (X : Matrix (Fin n) (Fin r) V.G.functionField) (T : Y.X → Matrix (Fin r) (Fin r) Y.Fn) (σ : Fin r → Fin n) : Prop :=
  (∀ z : V.G, V.j z ∈ U → ∀ k (hk : k ≤ r), UnitAt z (lead (locM V X T (V.π z)) σ k hk)) ∧
  ∀ v e y z yt, Tst V W p v e y z yt → ⊤ ≤ yt ⁻¹ᵁ U → ∀ k (hk : k ≤ r) σ',
    e.w (colMinor (vals V X T z (below y.1)) k hk σ') ≤ e.w (lead (vals V X T z (below y.1)) σ k hk)

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

abbrev psi (p : ℕ) [Fact p.Prime] {v : HeightOneSpectrum (𝓞 F)} (e : TrueGeo.Ext v) (y : AlgPt Y) :
    Y.X.presheaf.stalk (below y.1) →+* ℂ_[p] :=
  (ioOf p e).comp (Scheme.stalkClosedPointTo y.1).hom

def constM (V : Cover Y) {n m : ℕ} (T : Fin n → Fin m → F) : Matrix (Fin n) (Fin m) V.G.functionField :=
  Matrix.of fun j k => V.φ (algebraMap F Y.Fn (T j k))

end Cover

section Chars

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

def IsLabel (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) {K : Type} [Field K] (y : Sp K ⟶ Xo.XF c) (q : ℕ)
    (lb : Dw.La → (Over.mk y ⟶ Z.oF.t.G)) (ζ : Kˣ) : Prop :=
  IsPrimitiveRoot ζ q ∧ (∀ a b, lb (a + b) = lb a * lb b) ∧ (∀ (o : 𝓞 E) a, lb (o • a) = lb a ≫ Z.oF.t.act.act o) ∧
    (∀ σ : Over.mk y ⟶ Z.oF.t.G, σ ^ q = 1 ↔ ∃ a, lb a = σ) ∧
    ∀ a b, Out.WeilIs Z.oF.t.G Z.oF.t.PP.L (q : ℤ) (lb a) (lb b) (unitOn (ζ ^ Dw.EF a b))

def WeilLab (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) {R K : Type} [CommRing R] [Field K] (io : R →+* K) (x : Sp R ⟶ Z.X)
    (y : Sp K ⟶ Xo.XF c) (q : ℕ) (ch : Dw.La → TorsChar Z.t x q) : Prop :=
  ∃ (lb : Dw.La → (Over.mk y ⟶ Z.oF.t.G)) (ζ : Kˣ), IsLabel Z y q lb ζ ∧
    ∀ a b (w : Over.mk (spMap (algebraMap R R) ≫ x) ⟶ Z.t.G),
      w ^ q = 1 → (lb b).left ≫ Z.m.φ = spMap io ≫ w.left → io ((ch a).χ R w : Rˣ) = (ζ ^ Dw.EF a b : Kˣ)

def LabFam (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) {S : Scheme.{0}} (ρ : S ⟶ Z.X) (p : ℕ) [Fact p.Prime] (n : ℕ) : Prop :=
  ∃ ch : Dw.La → ∀ x : Sp ↥(intO ℂ_[p]) ⟶ S, TorsChar Z.t (x ≫ ρ) (p ^ n),
    (∀ x (y : Sp ℂ_[p] ⟶ Xo.XF c), spMap (intO ℂ_[p]).subtype ≫ x ≫ ρ = y ≫ Z.j →
      WeilLab Z (intO ℂ_[p]).subtype (x ≫ ρ) y (p ^ n) fun a => ch a x) ∧
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

def Isot (p : ℕ) [Fact p.Prime] (n : ℕ) {U : Type} (b : U → ℂ_[p] ⊗[ℤ] Dw.La) : Prop :=
  ∀ u u', (∀ a, ‖pr Dw (b u) a‖ ≤ 1) → (∀ a, ‖pr Dw (b u') a‖ ≤ 1) →
    ‖Dw.EF.baseChange ℂ_[p] (b u) (b u')‖ ≤ (p : ℝ)⁻¹ ^ n

variable (Dw) in

def EigTo {X : Scheme.{0}} (t : SAB H X) {K : Type} [CommRing K] (x : Sp K ⟶ X) {g : ℕ}
    (e : Fin g → (Sp (DualNumber K) ⟶ t.G.left)) (b : (Fin g → K) → K ⊗[ℤ] Dw.La) : Prop :=
  ∀ cf w, IsCombAtG t x e cf w → ∀ σ : 𝓞 E →+* K, GlobalTheory.FlatModel.IsEigG t σ w → IsEigL Dw σ (b cf)

variable (Dw) in

def HTLin {X : Scheme.{0}} (t : SAB H X) (p : ℕ) [Fact p.Prime] (n : ℕ) {R : Type} [CommRing R] (io : R →+* ℂ_[p])
    (x : Sp R ⟶ X) (ch : Dw.La → TorsChar t x (p ^ n)) {g : ℕ} (e : Fin g → (Sp (DualNumber R) ⟶ t.G.left))
    (b : (Fin g → ℂ_[p]) →ₗ[ℂ_[p]] ℂ_[p] ⊗[ℤ] Dw.La) : Prop :=
  (∀ a (h : Fin g → R), DlogIs t p n (ch a) e h → ∀ i, ‖io (h i) - pr Dw (b (Pi.single i 1)) a‖ ≤ (p : ℝ)⁻¹ ^ n) ∧
  EigTo Dw t (spMap io ≫ x) (fun i => spMap (dualMap io) ≫ e i) b ∧ Isot Dw p n b

variable (Dw) in

def PtData (p : ℕ) [Fact p.Prime] (n : ℕ) {g : ℕ} (h : Dw.La → Fin g → ℂ_[p])
    (b : (Fin g → ℂ_[p]) →ₗ[ℂ_[p]] ℂ_[p] ⊗[ℤ] Dw.La) (Λ : Set (Fin g → ℂ_[p])) : Prop :=
  (∀ a i, ‖h a i - pr Dw (b (Pi.single i 1)) a‖ ≤ (p : ℝ)⁻¹ ^ n) ∧ (∀ cf, cf ∈ Λ ↔ ∀ a, ‖pr Dw (b cf) a‖ ≤ 1) ∧
    (∀ cf ∈ Λ, ∀ i, ‖(p : ℂ_[p]) * cf i‖ ≤ 1) ∧ Isot Dw p n b

variable (Dw) in

def CutL {K : Type} [NormedField K] (σ : 𝓞 E →+* K) {M N : ℕ} (a : Fin M → Dw.La) (T : Fin N → Fin M → K) (δ : K) : Prop :=
  (∀ j m, ‖T j m‖ ≤ 1) ∧ ∀ y, IsEigL Dw σ y → ((∀ j, ‖∑ m, T j m * pr Dw y (a m)‖ ≤ 1) ↔ ∀ b, ‖δ * pr Dw y b‖ ≤ 1)

variable (Dw) in

def DualL {K : Type} [CommRing K] (σ' : 𝓞 E →+* K) {M N : ℕ} (a : Fin M → Dw.La) (T S : Fin N → Fin M → K) : Prop :=
  ∀ y y', IsEigL Dw σ' y' →
    ∑ j, (∑ m, T j m * pr Dw y (a m)) * (∑ m, S j m * pr Dw y' (a m)) = -Dw.EF.baseChange K y y'

variable (Dw) in

def CutAll (p : ℕ) [Fact p.Prime] {F : Type} [Field F] (σ : 𝓞 E →+* F) {M N : ℕ} (a : Fin M → Dw.La)
    (T : Fin N → Fin M → F) (κ : ℝ) : Prop :=
  ∀ k : F →+* ℂ_[p], ∃ δ : ℂ_[p], δ ≠ 0 ∧ Real.log ‖δ‖ = -(κ * Real.log p) ∧ CutL Dw (k.comp σ) a (fun j m => k (T j m)) δ

def AlgDef {X : Scheme.{0}} {K : Type} [Field K] (x : Sp K ⟶ X) : Prop :=
  ∃ (L : Type) (_ : Field L) (k : L →+* K) (z : Sp L ⟶ X), (∀ a : L, IsAlgebraic ℤ a) ∧ x = spMap k ≫ z

def PtOnG (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) {p : ℕ} [Fact p.Prime] [StarRing (𝓞 E)] (yb : Sp 𝓞_ℂ_[p] ⟶ Z.X)
    (yy : Sp ℂ_[p] ⟶ Xo.XF c) (P : GlobalTheory.FlatModel.PtP E p) (π : P.G.left ⟶ Z.t.G.left) (ψ : P.A.A.left ⟶ Z.oF.t.G.left) :
    Prop :=
  spMap (algebraMap 𝓞_ℂ_[p] ℂ_[p]) ≫ yb = yy ≫ Z.j ∧ IsGrpPullback P.G Z.t.G yb π ∧
    (∀ a, (P.oG.act a).left ≫ π = π ≫ (Z.t.act.act a).left) ∧ IsGrpPullback P.A.A Z.oF.t.G yy ψ ∧
    ψ ≫ Z.m.φ = P.gen ≫ π ∧ LBIso P.A.L (Z.oF.t.PP.L.pull ψ)

end Chars

section Cut

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  (t : SAB H X)

def latCo (p : ℕ) [Fact p.Prime] (x : Sp ℂ_[p] ⟶ X) {g : ℕ} (e : Fin g → (Sp (DualNumber ℂ_[p]) ⟶ t.G.left)) :
    Set (Fin g → ℂ_[p]) :=
  {cf | ∃ w ∈ latHT t p x, IsCombAtG t x e cf w}

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

def TriOf (ρ : Y.X ⟶ X) {m : ℕ} (u₀ : Fin m → (Sp (DualNumber Y.Fn) ⟶ t.G.left))
    (f : ∀ y : Y.X, Fin m → (Sp (DualNumber (Y.X.presheaf.stalk y)) ⟶ t.G.left)) (d : Y.X → Fin m → Y.Fnˣ)
    (T : Y.X → Matrix (Fin m) (Fin m) Y.Fn) : Prop :=
  ∀ y, (T y).BlockTriangular id ∧ ∀ i, T y i i = d y i ∧ IsCombAtG t (genericPt Y ≫ ρ)
    (fun k => spMap (dualMap (algebraMap (Y.X.presheaf.stalk y) Y.X.functionField)) ≫ f y k) (fun k => T y k i) (u₀ i)

def ChartCo (V : Cover Y) (ρ' : V.X ⟶ X) {U : V.X.Opens} (hU : IsAffineOpen U) {g : ℕ}
    (e : Fin g → (Sp (DualNumber Γ(V.X, U)) ⟶ t.G.left)) {n m : ℕ} (h : Fin n → Fin g → Γ(V.X, U))
    (f : ∀ y : Y.X, Fin m → (Sp (DualNumber (Y.X.presheaf.stalk y)) ⟶ t.G.left))
    (T : Y.X → Matrix (Fin m) (Fin m) Y.Fn) (P : Matrix (Fin n) (Fin m) V.G.functionField) : Prop :=
  ∀ z : V.G, V.j z ∈ U → ∃ (α : Γ(V.X, U) →+* V.G.presheaf.stalk z) (a : Fin m → Fin g → V.G.presheaf.stalk z),
    spMap α ≫ hU.fromSpec = V.G.fromSpecStalk z ≫ V.j ∧
    (∀ i, IsCombAtG t (spMap α ≫ hU.fromSpec ≫ ρ') (fun k => spMap (dualMap α) ≫ e k) (a i)
      (spMap (dualMap (V.π.stalkMap z).hom) ≫ f (V.π z) i)) ∧
    ∀ j i, locM V P T (V.π z) j i = algebraMap (V.G.presheaf.stalk z) V.G.functionField (∑ k, α (h j k) * a i k)

def CutAt (V : Cover Y) (W : Y.X.Opens) (p : ℕ) [Fact p.Prime] (ρ : Y.X ⟶ X) {J : Type} (U : J → V.X.Opens) {n r : ℕ}
    (f : ∀ y : Y.X, Fin r → (Sp (DualNumber (Y.X.presheaf.stalk y)) ⟶ t.G.left))
    (P : J → Matrix (Fin n) (Fin r) V.G.functionField) (T : Y.X → Matrix (Fin r) (Fin r) Y.Fn) (κ : ℝ) : Prop :=
  ∀ v e y z yt, Tst V W p v e y z yt → ∀ a, ⊤ ≤ yt ⁻¹ᵁ U a →
    (∃ δ : ℂ_[p], δ ≠ 0 ∧ Real.log ‖δ‖ = -(κ * Real.log p) ∧
      (∀ cf, (vals V (P a) T z (below y.1)).map (ioOf p e) *ᵥ cf = 0 → cf = 0) ∧
      ∀ cf, cf ∈ latCo t p (spMap (psi p e y) ≫ stalkPt Y (below y.1) ≫ ρ)
          (fun i => spMap (dualMap (psi p e y)) ≫ f (below y.1) i) ↔
        ∀ k, ‖((vals V (P a) T z (below y.1)).map (ioOf p e) *ᵥ cf) k‖ ≤ ‖δ‖) ∧
    ∀ b, ⊤ ≤ yt ⁻¹ᵁ U b → ∀ u : Fin r → ℂ_[p],
      (∀ k, ‖((vals V (P a) T z (below y.1)).map (ioOf p e) *ᵥ u) k‖ ≤ 1) →
      ∀ k, ‖((vals V (P b) T z (below y.1)).map (ioOf p e) *ᵥ u) k -
        ((vals V (P a) T z (below y.1)).map (ioOf p e) *ᵥ u) k‖ < 1

def EigFr (p : ℕ) [Fact p.Prime] (ρ : Y.X ⟶ X) {r : ℕ}
    (f : ∀ y : Y.X, Fin r → (Sp (DualNumber (Y.X.presheaf.stalk y)) ⟶ t.G.left)) (σ : 𝓞 E →+* F) : Prop :=
  ∀ (v : HeightOneSpectrum (𝓞 F)) (e : TrueGeo.Ext v) (y : AlgPt Y),
    IsIndep t (spMap (psi p e y) ≫ stalkPt Y (below y.1) ≫ ρ) (fun i => spMap (dualMap (psi p e y)) ≫ f (below y.1) i) ∧
    ∀ i, IsTanAtG t (spMap (psi p e y) ≫ stalkPt Y (below y.1) ≫ ρ) (spMap (dualMap (psi p e y)) ≫ f (below y.1) i) ∧
      GlobalTheory.FlatModel.IsEigG t (((ioOf p e).comp (algebraMap F (AlgebraicClosure F))).comp σ)
        (spMap (dualMap (psi p e y)) ≫ f (below y.1) i)

end Cut

section Fam

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {X : Scheme.{0}} {F : Type} [Field F] [NumberField F] {Y : Var F}

variable (Dw) in

structure Charts (t : SAB H X) (V : Cover Y) (ρ' : V.X ⟶ X) (J : Type) : Type 1 where
  U : J → V.X.Opens
  aff : ∀ a, IsAffineOpen (U a)
  g : J → ℕ
  e : ∀ a, Fin (g a) → (Sp (DualNumber Γ(V.X, U a)) ⟶ t.G.left)
  basis : ∀ a, IsTanBasis t (R := Γ(V.X, U a)) ((aff a).fromSpec ≫ ρ') (e a)
  h : ∀ a, Dw.La → Fin (g a) → Γ(V.X, U a)

def Charts.HTAt {t : SAB H X} {V : Cover Y} {ρ' : V.X ⟶ X} {J : Type} (K : Charts Dw t V ρ' J) (ρ : Y.X ⟶ X) (W : Y.X.Opens)
    (p : ℕ) [Fact p.Prime] (n : ℕ) : Prop :=
  ∀ v e y z yt, Tst V W p v e y z yt → ∃ (x : Sp ↥(intO ℂ_[p]) ⟶ X) (ch : Dw.La → TorsChar t x (p ^ n)),
    spMap (intO ℂ_[p]).subtype ≫ x = spMap (psi p e y) ≫ stalkPt Y (below y.1) ≫ ρ ∧
    ∀ a, ⊤ ≤ yt ⁻¹ᵁ K.U a → ∃ (ex : Fin (K.g a) → (Sp (DualNumber ↥(intO ℂ_[p])) ⟶ t.G.left))
      (hx : Dw.La → Fin (K.g a) → ↥(intO ℂ_[p])) (b : (Fin (K.g a) → ℂ_[p]) →ₗ[ℂ_[p]] ℂ_[p] ⊗[ℤ] Dw.La),
      IsTanBasis t x ex ∧ (∀ o, DlogIs t p n (ch o) ex (hx o)) ∧
      PtData Dw p n (fun o i => (hx o i : ℂ_[p])) b (latCo t p (spMap (intO ℂ_[p]).subtype ≫ x)
        fun i => spMap (dualMap (intO ℂ_[p]).subtype) ≫ ex i) ∧
      EigTo Dw t (spMap (intO ℂ_[p]).subtype ≫ x) (fun i => spMap (dualMap (intO ℂ_[p]).subtype) ≫ ex i) b ∧
      ∀ (M m : ℕ) (o : Fin M → Dw.La) (f : ∀ y : Y.X, Fin m → (Sp (DualNumber (Y.X.presheaf.stalk y)) ⟶ t.G.left))
        (T : Y.X → Matrix (Fin m) (Fin m) Y.Fn) (P : Matrix (Fin M) (Fin m) V.G.functionField),
        ChartCo t V ρ' (K.aff a) (K.e a) (fun j => K.h a (o j)) f T P → ∃ A : Fin m → Fin (K.g a) → ℂ_[p],
          (∀ i, IsCombAtG t (spMap (intO ℂ_[p]).subtype ≫ x) (fun k => spMap (dualMap (intO ℂ_[p]).subtype) ≫ ex k) (A i)
            (spMap (dualMap (psi p e y)) ≫ f (below y.1) i)) ∧
          ∀ (N : ℕ) (S : Fin N → Fin M → F), (vals V (constM V S * P) T z (below y.1)).map (ioOf p e) =
            covMat (fun j k => ioOf p e (algebraMap F (AlgebraicClosure F) (S j k))) (fun j k => (hx (o j) k : ℂ_[p])) A

end Fam

theorem lo_or_hi {r s N : ℕ} (h : r + s = N) (i : Fin N) : (∃ k, lo h k = i) ∨ ∃ l, hi h l = i := by
  by_cases hi' : (i : ℕ) < r
  · exact .inl ⟨⟨i, hi'⟩, rfl⟩
  · have := i.2
    exact .inr ⟨⟨N - 1 - i, by omega⟩, Fin.ext (by simp only [hi]; omega)⟩

end GlobalTheory.RootFrame

end
