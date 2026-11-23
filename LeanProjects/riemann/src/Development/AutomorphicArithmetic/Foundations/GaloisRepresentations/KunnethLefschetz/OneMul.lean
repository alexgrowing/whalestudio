import Development.EtaleCohomology.EtaleTrace.LadicH0LocallyConstant
import Development.EtaleCohomology.CohomologicalPurity.LeafIndExc
import Development.EtaleCohomology.KummerTheory.InjSlice
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.WtDegConst

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace
open scoped TensorProduct DirectSum

namespace UpperTheory.Gal.KunnethLefschetz

structure In : Prop where
  a1 : A1
  a2 : A2
  a3 : A3
  a4 : A4
  a5 : A5
  a6nat : DivisorNaturality
  a6ring : DivisorRingCompatibility
  a6supp : DivisorSupportCondition
  a6add : DivisorAdditivity
  a7 : A7
  a8 : A8
  a9 : A9
  a10 : A10
  a11 : A11
  b1 : B1
  b2 : B2
  b3 : B3
  c4 : C4
  d1 : D1
  e2 : E2
  e3 : E3
  e4 : E4
  gys : ∀ d, LateralTheory.CohomologicalPurity.Gysin d
  kun : LateralTheory.KummerTheory.GOAL

section Defs
variable {k : Type} [Field k]

structure IsPair (d e : ℕ) {Z X : Scheme.{0}} (p : X ⟶ S k) (ι : Z ⟶ X) : Prop where
  cl : IsClosedImmersion ι
  big : SmoothOfRelativeDimension (e + d) p
  small : SmoothOfRelativeDimension e (ι ≫ p)

def Off {Z X : Scheme.{0}} (ι : Z ⟶ X) (U : X.Opens) : Prop := (U : Set X) = (Set.range ι)ᶜ

def cup0 (q : ℕ) {X : Scheme.{0}} {n m r : ℤ} (h : n + m = r) (a : Ht q (sch.obj X) n 0) (b : Ht q (sch.obj X) m 0) :
    Ht q (sch.obj X) r 0 := (cup q a b).cast h (add_zero 0)

variable (k) in

structure Gys0 (l : ℕ) where
  g : ∀ (j : ℕ) {d e : ℕ} {Z X : Scheme.{0}} {p : X ⟶ S k} {ι : Z ⟶ X}, IsPair d e p ι → ∀ {n m : ℤ}, n + 2 * d = m →
    Ht (l ^ j) (sch.obj Z) n 0 →+ Ht (l ^ j) (sch.obj X) m 0
  exact : ∀ (j : ℕ) {d e : ℕ} {Z X : Scheme.{0}} {p : X ⟶ S k} {ι : Z ⟶ X} (h : IsPair d e p ι) {n m : ℤ} (hn : n + 2 * d = m)
    (U : X.Opens), Off ι U → Function.Exact (g j h hn) (pull _ (sch.map U.ι) (tw (l ^ j) 0) m)
  inj : ∀ (j : ℕ) {d e : ℕ} {Z X : Scheme.{0}} {p : X ⟶ S k} {ι : Z ⟶ X} (h : IsPair d e p ι) {n m : ℤ} (hn : n + 2 * d = m)
    (U : X.Opens), Off ι U → Subsingleton (Ht (l ^ j) (sch.obj U) (m - 1) 0) → Function.Injective (g j h hn)
  nat : ∀ (j : ℕ) {d e' e : ℕ} {Z' X' Z X : Scheme.{0}} {p' : X' ⟶ S k} {ι' : Z' ⟶ X'} {p : X ⟶ S k} {ι : Z ⟶ X}
    (h' : IsPair d e' p' ι') (h : IsPair d e p ι) (f : X' ⟶ X) (u : Z' ⟶ Z), f ≫ p = p' → IsPullback ι' u f ι →
    ∀ {n m : ℤ} (hn : n + 2 * d = m) (a : Ht (l ^ j) (sch.obj Z) n 0),
      pull _ (sch.map f) _ m (g j h hn a) = g j h' hn (pull _ (sch.map u) _ n a)
  proj : ∀ (j : ℕ) {d e : ℕ} {Z X : Scheme.{0}} {p : X ⟶ S k} {ι : Z ⟶ X} (h : IsPair d e p ι) {n m r s t : ℤ}
    (h1 : n + m = r) (h2 : r + 2 * d = t) (h3 : m + 2 * d = s) (h4 : n + s = t) (a : Ht (l ^ j) (sch.obj X) n 0)
    (b : Ht (l ^ j) (sch.obj Z) m 0),
    g j h h2 (cup0 _ h1 (pull _ (sch.map ι) _ n a) b) = cup0 _ h4 a (g j h h3 b)
  red : ∀ (j : ℕ) {d e : ℕ} {Z X : Scheme.{0}} {p : X ⟶ S k} {ι : Z ⟶ X} (h : IsPair d e p ι) {n m : ℤ} (hn : n + 2 * d = m)
    (a : Ht (l ^ (j + 1)) (sch.obj Z) n 0),
    red (l ^ (j + 1)) (l ^ j) _ m 0 (g (j + 1) h hn a) = g j h hn (red (l ^ (j + 1)) (l ^ j) _ n 0 a)

variable {l : ℕ} [Fact l.Prime]

def Gys0.hl (G : Gys0 k l) {d e : ℕ} {Z X : Scheme.{0}} {p : X ⟶ S k} {ι : Z ⟶ X} (h : IsPair d e p ι) {n m : ℤ}
    (hn : n + 2 * d = m) : Hl l (sch.obj Z) n 0 →ₗ[ℤ_[l]] Hl l (sch.obj X) m 0 where
  toFun x := ⟨fun j => G.g j h hn (x.1 j), fun j => (G.red j h hn _).trans (congrArg _ (x.2 j))⟩
  map_add' x y := Subtype.ext (funext fun j => map_add (G.g j h hn) (x.1 j) (y.1 j))
  map_smul' r x := Subtype.ext (funext fun j => by
    change G.g j h hn (show Ht (l ^ j) _ n 0 from r • x.1 j) =
      r • (show HtL l j (sch.obj X) m 0 from G.g j h hn (x.1 j))
    rw [HtL.smul_eq l j j le_rfl, HtL.smul_eq l j j le_rfl]
    exact map_nsmul (G.g j h hn) _ _)

def Gys0.q (G : Gys0 k l) {d e : ℕ} {Z X : Scheme.{0}} {p : X ⟶ S k} {ι : Z ⟶ X} (h : IsPair d e p ι) {n m : ℤ}
    (hn : n + 2 * d = m) : V l Z n →ₗ[ℚ_[l]] V l X m := (G.hl h hn).baseChange ℚ_[l]

variable (k l) in

structure GysQ where
  g : ∀ {d e : ℕ} {Z X : Scheme.{0}} {p : X ⟶ S k} {ι : Z ⟶ X}, IsPair d e p ι → ∀ {n m : ℤ}, n + 2 * d = m →
    V l Z n →ₗ[ℚ_[l]] V l X m
  off : ∀ {d e : ℕ} {Z X : Scheme.{0}} {p : X ⟶ S k} {ι : Z ⟶ X} (h : IsPair d e p ι) {n m : ℤ} (hn : n + 2 * d = m)
    (U : X.Opens), Off ι U → ∀ a, pb l U.ι m (g h hn a) = 0
  onto : ∀ {d e : ℕ} {Z X : Scheme.{0}} {p : X ⟶ S k} {ι : Z ⟶ X} (h : IsPair d e p ι) {n m : ℤ} (hn : n + 2 * d = m)
    (U : X.Opens), Off ι U → IsProper (ι ≫ p) → ∀ z, pb l U.ι m z = 0 → ∃ a, g h hn a = z
  inj : ∀ {d e : ℕ} {Z X : Scheme.{0}} {p : X ⟶ S k} {ι : Z ⟶ X} (h : IsPair d e p ι) {n m : ℤ} (hn : n + 2 * d = m)
    (U : X.Opens), Off ι U → (∀ j, Subsingleton (Ht (l ^ j) (sch.obj U) (m - 1) 0)) → Function.Injective (g h hn)
  nat : ∀ {d e' e : ℕ} {Z' X' Z X : Scheme.{0}} {p' : X' ⟶ S k} {ι' : Z' ⟶ X'} {p : X ⟶ S k} {ι : Z ⟶ X}
    (h' : IsPair d e' p' ι') (h : IsPair d e p ι) (f : X' ⟶ X) (u : Z' ⟶ Z), f ≫ p = p' → IsPullback ι' u f ι →
    ∀ {n m : ℤ} (hn : n + 2 * d = m) (a : V l Z n), pb l f m (g h hn a) = g h' hn (pb l u n a)
  proj : ∀ {d e : ℕ} {Z X : Scheme.{0}} {p : X ⟶ S k} {ι : Z ⟶ X} (h : IsPair d e p ι) {n m r s t : ℤ}
    (h1 : n + m = r) (h2 : r + 2 * d = t) (h3 : m + 2 * d = s) (h4 : n + s = t) (a : V l X n) (b : V l Z m),
    g h h2 (cupV l Z h1 (pb l ι n a) b) = cupV l X h4 a (g h h3 b)

open Classical in

def GysQ.cls (G : GysQ k l) (d e : ℕ) {Z X : Scheme.{0}} (p : X ⟶ S k) (ι : Z ⟶ X) : V l X (2 * d) :=
  if h : IsPair d e p ι then G.g h (zero_add _) (oneV l Z) else 0

abbrev GysQ.pt (G : GysQ k l) (d : ℕ) {X : Scheme.{0}} {p : X ⟶ S k} (y : Pt p) : V l X (2 * d) := G.cls d 0 p y.1

abbrev GysQ.diag (G : GysQ k l) (d : ℕ) {X : Scheme.{0}} (p : X ⟶ S k) : V l (pullback p p) (2 * d) :=
  G.cls d d (pullback.fst p p ≫ p) (pullback.diagonal p)

variable (l) in

abbrev ext2 {X : Scheme.{0}} (p : X ⟶ S k) {a b n : ℤ} (h : a + b = n) (u : V l X a) (v : V l X b) : V l (pullback p p) n :=
  cupV l (pullback p p) h (pb l (pullback.fst p p) a u) (pb l (pullback.snd p p) b v)

variable (l) in

def IsInt {d : ℕ} {X : Scheme.{0}} (p : X ⟶ S k) (lam : V l X (2 * d) →ₗ[ℚ_[l]] ℚ_[l]) {m n : ℤ} (h : 2 * d + m = n)
    (Λ : V l (pullback p p) n →ₗ[ℚ_[l]] V l X m) : Prop :=
  (∀ u v, Λ (ext2 l p h u v) = lam u • v) ∧ ∀ (a b : ℤ) (h' : a + b = n), b ≠ m → ∀ u v, Λ (ext2 l p h' u v) = 0

variable (l) in

def powV {X : Scheme.{0}} (x : V l X 2) : ∀ j : ℕ, V l X (2 * j)
  | 0 => oneV l X
  | j + 1 => cupV l X (by push_cast; ring) (powV x j) x

variable (l) in

structure PBQ {E Z : Scheme.{0}} (r : E ⟶ Z) (ξ : V l E 2) : Prop where
  span : ∀ n : ℤ, Submodule.span ℚ_[l] {z : V l E n | ∃ (j : ℕ) (a : ℤ) (h : a + 2 * j = n) (u : V l Z a),
    z = cupV l E h (pb l r a u) (powV l ξ j)} = ⊤
  zero : ∀ z : V l E 0, ∃ u, z = pb l r 0 u
  two : ∀ z : V l E 2, ∃ u v, z = pb l r 2 u + cupV l E (zero_add 2) (pb l r 0 v) ξ
  indep : ∀ u v, pb l r 2 u + cupV l E (zero_add 2) (pb l r 0 v) ξ = 0 → v = 0

def PBT (q N : ℕ) {E Z : Scheme.{0}} (r : E ⟶ Z) (x : Ht q (sch.obj E) 2 1) : Prop :=
  ∀ n i : ℤ, Function.Bijective fun a : ∀ j : Fin N, Ht q (sch.obj Z) (n - 2 * (j : ℕ)) (i - (j : ℕ)) =>
    ∑ j : Fin N, ((cup q (pull _ (sch.map r) _ _ (a j)) (cpow q x j)).cast (by ring) (by ring) : Ht q _ n i)

end Defs

section Facts
variable (l : ℕ) [Fact l.Prime] (k : Type) [Field k]

structure Ring : Prop where
  isCup : ∀ (X : Scheme.{0}) (n m r : ℤ) (h : n + m = r), IsCup l X h (cupV l X h)
  nat : ∀ {Y X : Scheme.{0}} (f : Y ⟶ X) (n m r : ℤ) (h : n + m = r) (u : V l X n) (v : V l X m),
    pb l f r (cupV l X h u v) = cupV l Y h (pb l f n u) (pb l f m v)
  one_def : ∀ X : Scheme.{0}, IsUnit (l : Γ(X, ⊤)) →
    ∃ z : Hl l (sch.obj X) 0 0, (∀ j, z.1 j = one (l ^ j) (sch.obj X)) ∧ oneV l X = 1 ⊗ₜ z
  one_mul : ∀ X : Scheme.{0}, IsUnit (l : Γ(X, ⊤)) → ∀ (n : ℤ) (u : V l X n), cupV l X (zero_add n) (oneV l X) u = u
  mul_one : ∀ X : Scheme.{0}, IsUnit (l : Γ(X, ⊤)) → ∀ (n : ℤ) (u : V l X n), cupV l X (add_zero n) u (oneV l X) = u
  one_nat : ∀ {Y X : Scheme.{0}} (f : Y ⟶ X), IsUnit (l : Γ(X, ⊤)) → pb l f 0 (oneV l X) = oneV l Y
  assoc : ∀ (X : Scheme.{0}) (n m r s t w : ℤ) (h1 : n + m = s) (h2 : s + r = w) (h3 : m + r = t) (h4 : n + t = w)
    (u : V l X n) (v : V l X m) (z : V l X r), cupV l X h2 (cupV l X h1 u v) z = cupV l X h4 u (cupV l X h3 v z)
  comm : ∀ (X : Scheme.{0}) (n m r : ℤ) (h : n + m = r) (h' : m + n = r) (u : V l X n) (v : V l X m),
    cupV l X h u v = (n * m).negOnePow • cupV l X h' v u

structure Low : Prop where
  neg : ∀ (X : Scheme.{0}) (n : ℤ), n < 0 → Subsingleton (V l X n)
  pos : ∀ n : ℤ, 0 < n → Subsingleton (V l (S k) n)
  line : ∀ z : V l (S k) 0, ∃! r : ℚ_[l], z = r • oneV l (S k)
  pts : ∀ {X : Scheme.{0}} (p : X ⟶ S k), IsProper p → ∀ z : V l X 0, (∀ y : Pt p, pb l y.1 0 z = 0) → z = 0
  conn : ∀ {X : Scheme.{0}} (p : X ⟶ S k), IsProper p → ConnectedSpace X → ∀ (z : V l X 0) (y y' : Pt p),
    pb l y.1 0 z = pb l y'.1 0 z

def Tower : Prop := ∀ i : ℤ, ∃ (u : Hl l (sch.obj (S k)) 0 i) (v : Hl l (sch.obj (S k)) 0 (-i)), ∀ j,
  (cup (l ^ j) (show Ht (l ^ j) _ 0 i from u.1 j) (show Ht (l ^ j) _ 0 (-i) from v.1 j)).cast (add_zero 0) (add_neg_cancel i) =
    one (l ^ j) (sch.obj (S k))

structure Kun (d : ℕ) {X : Scheme.{0}} (p : X ⟶ S k) : Prop where
  span : ∀ n : ℤ, Submodule.span ℚ_[l] {w : V l (pullback p p) n | ∃ (a b : ℤ) (h : a + b = n) (u : V l X a) (v : V l X b),
    w = ext2 l p h u v} = ⊤
  int : ∀ lam : V l X (2 * d) →ₗ[ℚ_[l]] ℚ_[l], ∀ (m n : ℤ) (h : 2 * d + m = n),
    ∃ Λ : V l (pullback p p) n →ₗ[ℚ_[l]] V l X m, IsInt l p lam h Λ

def Dual (d : ℕ) (X : Scheme.{0}) : Prop :=
  (∀ n, FiniteDimensional ℚ_[l] (V l X n)) ∧ (∀ n : ℤ, 2 * d < n → Subsingleton (V l X n)) ∧
  ∃ tr : V l X (2 * d) ≃ₗ[ℚ_[l]] ℚ_[l], ∀ (n m : ℤ) (h : n + m = 2 * d),
    Function.Bijective ((cupV l X h).compr₂ tr.toLinearMap).flip

end Facts

def TrIn : Prop := TranscendenceTraces.WtNormal ∧ TranscendenceTraces.NmlLoc ∧ TranscendenceTraces.NwtDeg ∧ TranscendenceTraces.TrDegQ

def QDual : Prop := ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [IsAlgClosed k], (l : k) ≠ 0 →
  ∀ (d : ℕ) {X : Scheme.{0}} (p : X ⟶ S k), SP d p → IsProj p → IsIntegral X → Dual l d X

def QDiag : Prop := ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [IsAlgClosed k], (l : k) ≠ 0 →
  ∀ (d : ℕ) {X : Scheme.{0}} (p : X ⟶ S k), SP (d + 1) p → IsProj p →
  ∀ {W E : Scheme.{0}} (π : W ⟶ pullback p p) (i : E ⟶ W) (r : E ⟶ X) (c : ℕ), IsPullback i r π (pullback.diagonal p) →
    IsPair 1 c (π ≫ pullback.fst p p ≫ p) i → IsProper r → ∀ (U : W.Opens), Off i U → ∀ e : V l W 2, pb l U.ι 2 e = 0 →
    PBQ l r (pb l i 2 e) →
  ∃ (δ : V l (pullback p p) (2 + 2 * d)) (m : V l W (2 * d)) (s : ℕ) (a : Fin s → V l X (2 + 2 * d)) (b : Fin s → V l X 0),
    pb l π _ δ = cupV l W rfl e m ∧ LinearIndependent ℚ_[l] a ∧ ∑ t, b t = oneV l X ∧
    δ - ∑ t, ext2 l p (add_zero _) (a t) (b t) ∈ Submodule.span ℚ_[l] {w : V l (pullback p p) (2 + 2 * d) |
      ∃ (n n' : ℤ) (h : n + n' = 2 + 2 * d) (u : V l X n) (v : V l X n'), 0 ≤ n ∧ 0 < n' ∧ w = ext2 l p h u v}

end UpperTheory.Gal.KunnethLefschetz
