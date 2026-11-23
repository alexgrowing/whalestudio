import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.OneMul

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace
open scoped TensorProduct DirectSum

namespace UpperTheory.Gal.KunnethLefschetz

section Defs
variable {k : Type} [Field k]

variable (k) in

structure GysT where
  g : ∀ (q : ℕ) {d e : ℕ} {Z X : Scheme.{0}} {p : X ⟶ S k} {ι : Z ⟶ X}, IsPair d e p ι → ∀ {n m i j : ℤ}, n + 2 * d = m → i + d = j →
    Ht q (sch.obj Z) n i →+ Ht q (sch.obj X) m j
  exact : ∀ (q : ℕ) [NeZero q], IsUnit (q : k) → ∀ {d e : ℕ} {Z X : Scheme.{0}} {p : X ⟶ S k} {ι : Z ⟶ X} (h : IsPair d e p ι) {n m i j : ℤ} (hn : n + 2 * d = m) (hi : i + d = j)
    (U : X.Opens), Off ι U → Function.Exact (g q h hn hi) (pull _ (sch.map U.ι) (tw q j) m)
  inj : ∀ (q : ℕ) [NeZero q], IsUnit (q : k) → ∀ {d e : ℕ} {Z X : Scheme.{0}} {p : X ⟶ S k} {ι : Z ⟶ X} (h : IsPair d e p ι) {n m i j : ℤ} (hn : n + 2 * d = m) (hi : i + d = j)
    (U : X.Opens), Off ι U → Subsingleton (Ht q (sch.obj U) (m - 1) j) → Function.Injective (g q h hn hi)
  nat : ∀ (q : ℕ) [NeZero q], IsUnit (q : k) → ∀ {d e' e : ℕ} {Z' X' Z X : Scheme.{0}} {p' : X' ⟶ S k} {ι' : Z' ⟶ X'} {p : X ⟶ S k}
    {ι : Z ⟶ X} (h' : IsPair d e' p' ι') (h : IsPair d e p ι) (f : X' ⟶ X) (u : Z' ⟶ Z), IsPullback ι' u f ι →
    ∀ {n m i j : ℤ} (hn : n + 2 * d = m) (hi : i + d = j) (a : Ht q (sch.obj Z) n i),
      pull _ (sch.map f) _ m (g q h hn hi a) = g q h' hn hi (pull _ (sch.map u) _ n a)
  proj : ∀ (q : ℕ) [NeZero q], IsUnit (q : k) → ∀ {d e : ℕ} {Z X : Scheme.{0}} {p : X ⟶ S k} {ι : Z ⟶ X} (h : IsPair d e p ι) {n m r s t i j i' j' w : ℤ}
    (h1 : n + m = r) (h2 : r + 2 * d = t) (h3 : m + 2 * d = s) (h4 : n + s = t)
    (k1 : i + j = i') (k2 : i' + d = w) (k3 : j + d = j') (k4 : i + j' = w) (a : Ht q (sch.obj X) n i) (b : Ht q (sch.obj Z) m j),
    g q h h2 k2 ((cup q (pull _ (sch.map ι) _ n a) b).cast h1 k1) = (cup q a (g q h h3 k3 b)).cast h4 k4
  red : ∀ (q r : ℕ) [NeZero q], IsUnit (q : k) → r ∣ q → ∀ {d e : ℕ} {Z X : Scheme.{0}} {p : X ⟶ S k} {ι : Z ⟶ X} (h : IsPair d e p ι) {n m i j : ℤ} (hn : n + 2 * d = m) (hi : i + d = j)
    (a : Ht q (sch.obj Z) n i), red q r _ m j (g q h hn hi a) = g r h hn hi (red q r _ n i a)

def twMul (q : ℕ) {X : Scheme.{0}} (p : X ⟶ S k) {i j w : ℤ} (hw : i + j = w) (v : Ht q (sch.obj (S k)) 0 i) (n : ℤ)
    (a : Ht q (sch.obj X) n j) : Ht q (sch.obj X) n w := (cup q (pull _ (sch.map p) _ 0 v) a).cast (zero_add n) hw

abbrev slice {X : Scheme.{0}} {p : X ⟶ S k} (y : Pt p) : X ⟶ pullback p p :=
  pullback.lift (𝟙 X) (p ≫ y.1) (by rw [Category.id_comp, Category.assoc, y.2, Category.comp_id])

def OffPts {X : Scheme.{0}} {p : X ⟶ S k} (s : Finset (Pt p)) (U : X.Opens) : Prop :=
  (U : Set X) = (⋃ y ∈ s, Set.range y.1)ᶜ

variable (k) in

def LowT (q : ℕ) : Prop :=
  ((∀ z : Ht q (sch.obj (S k)) 0 0, ∃ a : ℕ, z = a • one q (sch.obj (S k))) ∧ ∀ a : ℕ, a • one q (sch.obj (S k)) = 0 → q ∣ a) ∧
  ∀ {X : Scheme.{0}} (p : X ⟶ S k), IsProper p → ∀ z : Ht q (sch.obj X) 0 0,
    ((∀ y : Pt p, pull (ZMod q) (sch.map y.1) (tw q 0) 0 z = 0) → z = 0) ∧
    (ConnectedSpace X → ∀ y y' : Pt p, pull (ZMod q) (sch.map y.1) (tw q 0) 0 z = pull (ZMod q) (sch.map y'.1) (tw q 0) 0 z)

variable (l : ℕ) [Fact l.Prime]

def Detect (d : ℕ) (X : Scheme.{0}) (lam : V l X (2 * d) →ₗ[ℚ_[l]] ℚ_[l]) : Prop :=
  ∃ (s : ℕ) (c : Fin s → ℤ) (a : ∀ t, V l X (c t)), ∀ (n : ℤ) (x : V l X n),
    (∀ (t : Fin s) (h : n + c t = 2 * d), lam (cupV l X h x (a t)) = 0) → x = 0

end Defs

def OffEx : Prop := (∀ {Z X : Scheme.{0}} (ι : Z ⟶ X), IsClosedImmersion ι → ∃ U : X.Opens, Off ι U) ∧
  ∀ {Z' X' Z X : Scheme.{0}} (ι' : Z' ⟶ X') (ι : Z ⟶ X) (f : X' ⟶ X) (u : Z' ⟶ Z), IsPullback ι' u f ι →
    ∀ U : X.Opens, Off ι U → Off ι' (f ⁻¹ᵁ U)

def Pairs : Prop := ∀ (k : Type) [Field k] (d : ℕ) {X : Scheme.{0}} (p : X ⟶ S k), IsSeparated p → SmoothOfRelativeDimension d p →
  IsPair d d (pullback.fst p p ≫ p) (pullback.diagonal p) ∧ ∀ y : Pt p, IsPair d 0 p y.1 ∧
    IsPullback y.1 y.1 (slice y) (pullback.diagonal p)

def PnFacts : Prop := ∀ (k : Type) [Field k] (d : ℕ), SP d (PNto k d) ∧ IsIntegral (PN k d) ∧ TranscendenceTraces.LocNml (PN k d) ∧
  IsIso (PNto k 0)

def HypEmb : Prop := ∀ (k : Type) [Field k] (d : ℕ), ∃ (ι : PN k d ⟶ PN k (d + 1)) (U : (PN k (d + 1)).Opens),
  IsClosedImmersion ι ∧ ι ≫ PNto k (d + 1) = PNto k d ∧ Off ι U ∧
  Nonempty ((U : Scheme.{0}) ≅ Spec (CommRingCat.of (MvPolynomial (Fin (d + 1)) k)))

def FinCov : Prop := ∀ (k : Type) [Field k] [IsAlgClosed k] (d : ℕ) {X : Scheme.{0}} (p : X ⟶ S k), SP d p → IsProj p →
  IsIntegral X → ∃ π : X ⟶ PN k d, π ≫ PNto k d = p ∧ IsFinite π ∧ Surjective π

def FinFib : Prop := ∀ (k : Type) [Field k] [IsAlgClosed k] {X Y : Scheme.{0}} (p : X ⟶ S k) (r : Y ⟶ S k) (π : X ⟶ Y), π ≫ r = p →
  IsFinite π → ∀ (t : Pt r) (U : Y.Opens), Off t.1 U → ∃ s : Finset (Pt p), OffPts s (π ⁻¹ᵁ U)

def Comps : Prop := ∀ (k : Type) [Field k] [IsAlgClosed k] (d : ℕ) {X : Scheme.{0}} (p : X ⟶ S k), SP d p → IsProj p →
  ∃ (m : ℕ) (U : Fin m → X.Opens), (∀ j, SP d ((U j).ι ≫ p) ∧ IsProj ((U j).ι ≫ p) ∧ IsIntegral (U j : Scheme.{0})) ∧
    (∀ x : X, ∃ j, x ∈ U j) ∧ ∀ j j', j ≠ j' → Disjoint (U j) (U j')

def RingL : Prop := In → ∀ (l : ℕ) [Fact l.Prime], Ring l

def LowTL : Prop := In → ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [IsAlgClosed k], (l : k) ≠ 0 → ∀ j : ℕ, LowT k (l ^ j)

def PtVanT : Prop := In → ∀ (k : Type) [Field k] [IsAlgClosed k] (q : ℕ) (n i : ℤ), 0 < n → Subsingleton (Ht q (sch.obj (S k)) n i)

def LowL : Prop := In → PtVanT → ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [IsAlgClosed k], (l : k) ≠ 0 → Ring l → (∀ j : ℕ, LowT k (l ^ j)) → Low l k

def TowerL : Prop := In → ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [IsAlgClosed k], (l : k) ≠ 0 → Tower l k

def AffVan : Prop := In → PtVanT → ∀ (k : Type) [Field k] [IsAlgClosed k] (q : ℕ) [NeZero q], IsUnit (q : k) → ∀ (d : ℕ) (n i : ℤ), 0 < n →
  Subsingleton (Ht q (sch.obj (Spec (CommRingCat.of (MvPolynomial (Fin d) k)))) n i)

def TwBij : Prop := In → ∀ (k : Type) [Field k] (q : ℕ) [NeZero q], IsUnit (q : k) → ∀ (i : ℤ) (u : Ht q (sch.obj (S k)) 0 i)
  (v : Ht q (sch.obj (S k)) 0 (-i)), (cup q u v).cast (add_zero 0) (add_neg_cancel i) = one q (sch.obj (S k)) →
  ∀ {X : Scheme.{0}} (p : X ⟶ S k) (n j w : ℤ), (∀ hw : -i + j = w, Function.Bijective (twMul q p hw v n)) ∧
    ∀ hw : i + j = w, Function.Bijective (twMul q p hw u n)

def GysTL : Prop := In → OffEx → ∀ (k : Type) [Field k], Nonempty (GysT k)

def GysinCondition : Prop := In → TwBij → ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [IsAlgClosed k], (l : k) ≠ 0 → Tower l k → Nonempty (GysT k) → Nonempty (Gys0 k l)

def QEasy : Prop := ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] (G : Gys0 k l),
  (∀ {d e : ℕ} {Z X : Scheme.{0}} {p : X ⟶ S k} {ι : Z ⟶ X} (h : IsPair d e p ι) {n m : ℤ} (hn : n + 2 * d = m) (U : X.Opens), Off ι U → ∀ a, pb l U.ι m (G.q h hn a) = 0) ∧
  (∀ {d e : ℕ} {Z X : Scheme.{0}} {p : X ⟶ S k} {ι : Z ⟶ X} (h : IsPair d e p ι) {n m : ℤ} (hn : n + 2 * d = m) (U : X.Opens), Off ι U →
    (∀ j, Subsingleton (Ht (l ^ j) (sch.obj U) (m - 1) 0)) → Function.Injective (G.q h hn)) ∧
  ∀ {d e' e : ℕ} {Z' X' Z X : Scheme.{0}} {p' : X' ⟶ S k} {ι' : Z' ⟶ X'} {p : X ⟶ S k} {ι : Z ⟶ X}
    (h' : IsPair d e' p' ι') (h : IsPair d e p ι) (f : X' ⟶ X) (u : Z' ⟶ Z), f ≫ p = p' → IsPullback ι' u f ι →
    ∀ {n m : ℤ} (hn : n + 2 * d = m) (a : V l Z n), pb l f m (G.q h hn a) = G.q h' hn (pb l u n a)

def LimOnto : Prop := ∀ (A B : ℕ → Type 1) [∀ j, Finite (A j)] (ra : ∀ j, A (j + 1) → A j) (rb : ∀ j, B (j + 1) → B j)
  (f : ∀ j, A j → B j), (∀ j a, rb j (f (j + 1) a) = f j (ra j a)) → ∀ z : ∀ j, B j, (∀ j, rb j (z (j + 1)) = z j) →
  (∀ j, ∃ a, f j a = z j) → ∃ a : ∀ j, A j, (∀ j, ra j (a (j + 1)) = a j) ∧ ∀ j, f j (a j) = z j

def QOnto : Prop := In → LimOnto → ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [IsAlgClosed k], (l : k) ≠ 0 → ∀ (G : Gys0 k l)
  {d e : ℕ} {Z X : Scheme.{0}} {p : X ⟶ S k} {ι : Z ⟶ X} (h : IsPair d e p ι) {n m : ℤ} (hn : n + 2 * d = m) (U : X.Opens), Off ι U → IsProper (ι ≫ p) →
  ∀ z, pb l U.ι m z = 0 → ∃ a, G.q h hn a = z

def QProj : Prop := In → ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] (G : Gys0 k l)
  {d e : ℕ} {Z X : Scheme.{0}} {p : X ⟶ S k} {ι : Z ⟶ X} (h : IsPair d e p ι) {n m r s t : ℤ}
    (h1 : n + m = r) (h2 : r + 2 * d = t) (h3 : m + 2 * d = s) (h4 : n + s = t) (a : V l X n) (b : V l Z m),
    G.q h h2 (cupV l Z h1 (pb l ι n a) b) = cupV l X h4 a (G.q h h3 b)

def KunBij : Prop := In → ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [IsAlgClosed k], (l : k) ≠ 0 → Ring l →
  ∀ (d : ℕ) {X : Scheme.{0}} (p : X ⟶ S k), SP d p → ∀ n, Function.Bijective (kun l p p n)

def KunL : Prop := ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] (d : ℕ) {X : Scheme.{0}} (p : X ⟶ S k),
  (∀ n, Function.Bijective (kun l p p n)) → Kun l k d p

def Swap : Prop := Pairs → ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [IsAlgClosed k], (l : k) ≠ 0 →
  ∀ (d : ℕ) {X : Scheme.{0}} (p : X ⟶ S k), SP d p → Ring l → ∀ (G : GysQ k l) (n w : ℤ) (h : n + 2 * d = w) (h' : 2 * d + n = w) (x : V l X n),
  cupV l _ h (pb l (pullback.fst p p) n x) (G.diag d p) = cupV l _ h' (G.diag d p) (pb l (pullback.snd p p) n x)

def Slice : Prop := Pairs → ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [IsAlgClosed k], (l : k) ≠ 0 →
  ∀ (d : ℕ) {X : Scheme.{0}} (p : X ⟶ S k), SP d p → Ring l → ∀ (G : GysQ k l) (y : Pt p), pb l (slice y) _ (G.diag d p) = G.pt d y

def PtInt : Prop := ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [IsAlgClosed k], (l : k) ≠ 0 →
  ∀ (d : ℕ) {X : Scheme.{0}} (p : X ⟶ S k), SP d p → Ring l → Low l k → Kun l k d p → ∀ (lam : V l X (2 * d) →ₗ[ℚ_[l]] ℚ_[l])
  (Λ : V l (pullback p p) (2 * d) →ₗ[ℚ_[l]] V l X 0), IsInt l p lam (add_zero _) Λ → ∀ (y : Pt p) (w : V l (pullback p p) (2 * d)),
  pb l y.1 0 (Λ w) = lam (pb l (slice y) _ w) • oneV l (S k)

def DetectL : Prop := ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [IsAlgClosed k], (l : k) ≠ 0 →
  ∀ (d : ℕ) {X : Scheme.{0}} (p : X ⟶ S k), SP d p → Ring l → Kun l k d p → ∀ (lam : V l X (2 * d) →ₗ[ℚ_[l]] ℚ_[l]) (δ : V l (pullback p p) (2 * d)),
  (∀ (n w : ℤ) (h : n + 2 * d = w) (h' : 2 * d + n = w) (x : V l X n),
    cupV l _ h (pb l (pullback.fst p p) n x) δ = cupV l _ h' δ (pb l (pullback.snd p p) n x)) →
  (∀ Λ : V l (pullback p p) (2 * d) →ₗ[ℚ_[l]] V l X 0, IsInt l p lam (add_zero _) Λ → Λ δ = oneV l X) → Detect l d X lam

def DualL : Prop := ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [IsAlgClosed k], (l : k) ≠ 0 →
  ∀ (d : ℕ) {X : Scheme.{0}} (p : X ⟶ S k), SP d p → IsIntegral X → Ring l → Low l k → ∀ lam : V l X (2 * d) →ₗ[ℚ_[l]] ℚ_[l], Detect l d X lam →
  lam ≠ 0 → Dual l d X

def FinSupp : Prop := OffEx → Pairs → ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [IsAlgClosed k], (l : k) ≠ 0 → Ring l → Low l k → ∀ (G : GysQ k l)
  (d : ℕ) {X : Scheme.{0}} (p : X ⟶ S k), IsSeparated p → SmoothOfRelativeDimension d p → ∀ (s : Finset (Pt p)) (U : X.Opens),
  OffPts s U → ∀ z : V l X (2 * d), pb l U.ι _ z = 0 → z ∈ Submodule.span ℚ_[l] (Set.range fun y : Pt p => G.pt d y)

def PnCls : Prop := In → PnFacts → HypEmb → OffEx → ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [IsAlgClosed k], (l : k) ≠ 0 → Ring l → Low l k →
  (∀ (j d : ℕ) (n : ℤ), 0 < n → Subsingleton (Ht (l ^ j) (sch.obj (Spec (CommRingCat.of (MvPolynomial (Fin d) k)))) n 0)) →
  Nonempty (GysQ k l) → ∀ d : ℕ, ∃ (t : Pt (PNto k d)) (U : (PN k d).Opens) (z : V l (PN k d) (2 * d)),
    Off t.1 U ∧ z ≠ 0 ∧ pb l U.ι _ z = 0

def InjL : Prop := TrIn → ∀ (l : ℕ) [Fact l.Prime] {X Y : Scheme.{0}} (π : X ⟶ Y), IsFinite π → Surjective π → IsIntegral Y →
  TranscendenceTraces.LocNml Y → IsUnit (l : Γ(Y, ⊤)) → ∀ n, Function.Injective (pb l π n)

def TrComp : Prop := Comps → OffEx → Pairs → ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [IsAlgClosed k], (l : k) ≠ 0 → Ring l → ∀ (G : GysQ k l) (d : ℕ),
  (∀ {X : Scheme.{0}} (p : X ⟶ S k), SP d p → IsProj p → IsIntegral X →
    ∃ lam : V l X (2 * d) →ₗ[ℚ_[l]] ℚ_[l], ∀ y : Pt p, lam (G.pt d y) = 1) →
  ∀ {X : Scheme.{0}} (p : X ⟶ S k), SP d p → IsProj p → ∃ lam : V l X (2 * d) →ₗ[ℚ_[l]] ℚ_[l], ∀ y : Pt p, lam (G.pt d y) = 1

def DivL : Prop := ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [IsAlgClosed k], (l : k) ≠ 0 → Ring l → ∀ (G : GysQ k l) {W E X : Scheme.{0}} (px : X ⟶ S k) (i : E ⟶ W) (s : W ⟶ X) (c : ℕ),
  IsPair 1 c (s ≫ px) i → IsProper (i ≫ s ≫ px) → ∀ U : W.Opens, Off i U → ∀ e : V l W 2, pb l U.ι 2 e = 0 → PBQ l (i ≫ s) (pb l i 2 e) →
  ∀ (n w : ℤ) (h : 2 + n = w) (z : V l W w), pb l U.ι w z = 0 → ∃ m : V l W n, z = cupV l W h e m

def BasisOne : Prop := ∀ (F : Type) (M : Type 1) [Field F] [AddCommGroup M] [Module F M] [FiniteDimensional F M] (lam : M →ₗ[F] F),
  (lam = 0 → Subsingleton M) → ∃ (s : ℕ) (b : Module.Basis (Fin s) F M), ∀ t, lam (b t) = 1

def TopPart : Prop := ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [IsAlgClosed k], (l : k) ≠ 0 →
  ∀ (d : ℕ) {X : Scheme.{0}} (p : X ⟶ S k), SP d p → Ring l → Low l k → Kun l k d p → ∀ (lam : V l X (2 * d) →ₗ[ℚ_[l]] ℚ_[l]) (s : ℕ)
  (a : Module.Basis (Fin s) ℚ_[l] (V l X (2 * d))), (∀ t, lam (a t) = 1) →
  ∀ (Λ : V l (pullback p p) (2 * d) →ₗ[ℚ_[l]] V l X 0), IsInt l p lam (add_zero _) Λ → ∀ δ : V l (pullback p p) (2 * d),
  ∃ b : Fin s → V l X 0, ∑ t, b t = Λ δ ∧
    δ - ∑ t, ext2 l p (add_zero _) (a t) (b t) ∈ Submodule.span ℚ_[l] {w : V l (pullback p p) (2 * d) |
      ∃ (n n' : ℤ) (h : n + n' = 2 * d) (u : V l X n) (v : V l X n'), 0 ≤ n ∧ 0 < n' ∧ w = ext2 l p h u v}

end UpperTheory.Gal.KunnethLefschetz
