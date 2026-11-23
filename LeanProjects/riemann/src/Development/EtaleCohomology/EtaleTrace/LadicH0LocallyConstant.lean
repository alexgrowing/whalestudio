import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC
open scoped TensorProduct DirectSum
attribute [local instance] MvPolynomial.gradedAlgebra

namespace LateralTheory.EtaleTrace

def Base : Prop := (A1 ∧ A2 ∧ A3 ∧ A4 ∧ A5 ∧ DivisorNaturality ∧ DivisorRingCompatibility ∧ DivisorSupportCondition ∧ DivisorAdditivity ∧ A7 ∧ A8 ∧ A9 ∧ A10 ∧ A11) ∧
  (B1 ∧ B2 ∧ B3 ∧ B4 ∧ B5) ∧ (C4 ∧ C5 ∧ D1) ∧ (E1 ∧ E2 ∧ E3 ∧ E4 ∧ E6 ∧ E8)

abbrev S (k : Type) [Field k] : Scheme.{0} := Spec (CommRingCat.of k)

section Defs
variable (l : ℕ) [Fact l.Prime]

abbrev V (X : Scheme.{0}) (n : ℤ) : Type 1 := HQ l (sch.obj X) n 0

abbrev pb {Y X : Scheme.{0}} (f : Y ⟶ X) (n : ℤ) : V l X n →ₗ[ℚ_[l]] V l Y n := pullHQ l (sch.map f) n 0

def IsCup (X : Scheme.{0}) {n m r : ℤ} (h : n + m = r) (c : V l X n →ₗ[ℚ_[l]] V l X m →ₗ[ℚ_[l]] V l X r) : Prop :=
  ∀ (x : Hl l (sch.obj X) n 0) (y : Hl l (sch.obj X) m 0) (z : Hl l (sch.obj X) r 0),
    (∀ j, z.1 j = Ht.cast h (add_zero 0) (cup (l ^ j) (show Ht (l ^ j) (sch.obj X) n 0 from x.1 j)
      (show Ht (l ^ j) (sch.obj X) m 0 from y.1 j))) →
    c (1 ⊗ₜ x) (1 ⊗ₜ y) = 1 ⊗ₜ z

def cupV (X : Scheme.{0}) {n m r : ℤ} (h : n + m = r) : V l X n →ₗ[ℚ_[l]] V l X m →ₗ[ℚ_[l]] V l X r := pick (IsCup l X h)

def oneV (X : Scheme.{0}) : V l X 0 :=
  pick fun c => ∀ z : Hl l (sch.obj X) 0 0, (∀ j, z.1 j = one (l ^ j) (sch.obj X)) → c = 1 ⊗ₜ z

def IsPush {Y X : Scheme.{0}} (a : Y ⟶ X) (n : ℤ) (T : V l Y n →ₗ[ℚ_[l]] V l X n) : Prop :=
  ∀ (W : Scheme.{0}) (x : W ⟶ X) (m : ℕ) (s : Fin m → (W ⟶ Y)) (hs : ∀ j, s j ≫ a = x),
    IsIso (Sigma.desc (fun j => pullback.lift (s j) (𝟙 W) (by rw [hs j, Category.id_comp])) :
      ∐ (fun _ : Fin m => W) ⟶ pullback a x) →
    ∀ z, pb l x n (T z) = ∑ j, pb l (s j) n z

def push {Y X : Scheme.{0}} (a : Y ⟶ X) (n : ℤ) : V l Y n →ₗ[ℚ_[l]] V l X n := pick (IsPush l a n)

def altTr (X : Scheme.{0}) (d : ℕ) (T : ∀ n : ℤ, V l X n →ₗ[ℚ_[l]] V l X n) : ℚ_[l] :=
  ∑ n ∈ Finset.range (2 * d + 1), (-1) ^ n * LinearMap.trace ℚ_[l] _ (T n)

variable {k : Type} [Field k]

def Pt {X : Scheme.{0}} (p : X ⟶ S k) : Type := {y : S k ⟶ X // y ≫ p = 𝟙 _}

def Pt.map {Y X : Scheme.{0}} {q : Y ⟶ S k} {p : X ⟶ S k} (a : Y ⟶ X) (ha : a ≫ p = q) (y : Pt q) : Pt p :=
  ⟨y.1 ≫ a, by rw [Category.assoc, ha, y.2]⟩

variable (k) in

abbrev PN (N : ℕ) : Scheme.{0} := Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k)

variable (k) in

def PNto (N : ℕ) : PN k N ⟶ S k :=
  Proj.toSpecZero _ ≫ Spec.map (CommRingCat.ofHom (algebraMap k (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k 0)))

def IsProj {X : Scheme.{0}} (p : X ⟶ S k) : Prop := ∃ (N : ℕ) (ι : X ⟶ PN k N), IsClosedImmersion ι ∧ ι ≫ PNto k N = p

def SP (d : ℕ) {X : Scheme.{0}} (p : X ⟶ S k) : Prop := IsProper p ∧ SmoothOfRelativeDimension d p

variable (k) in

abbrev Fam : Type 1 := ∀ (d : ℕ) {X : Scheme.{0}} (p : X ⟶ S k), V l (pullback p p) (2 * d)

variable {l}

def Fam.corr (δ : Fam l k) (d : ℕ) {Y X : Scheme.{0}} {q : Y ⟶ S k} {p : X ⟶ S k} (c a : Y ⟶ X) (hc : c ≫ p = q)
    (ha : a ≫ p = q) : V l Y (2 * d) := pb l (pullback.lift c a (hc.trans ha.symm)) _ (δ d p)

def Fam.cl (δ : Fam l k) (d : ℕ) {X : Scheme.{0}} {p : X ⟶ S k} (y : Pt p) : V l X (2 * d) :=
  δ.corr d (q := p) (𝟙 X) (p ≫ y.1) (Category.id_comp _) (by rw [Category.assoc, y.2, Category.comp_id])

structure IsDiag (δ : Fam l k) : Prop where
  swap : ∀ (d : ℕ) {X : Scheme.{0}} (p : X ⟶ S k), SP d p → ∀ (m : ℤ) (β : V l X m),
    cupV l _ rfl (δ d p) (pb l (pullback.fst p p) m β) = cupV l _ rfl (δ d p) (pb l (pullback.snd p p) m β)
  trans : ∀ (d : ℕ) {Y X : Scheme.{0}} (q : Y ⟶ S k) (p : X ⟶ S k), SP d q → SP d p → ∀ (c a : Y ⟶ X) (hc : c ≫ p = q)
    (ha : a ≫ p = q), Etale (equalizer.ι c a ≫ q) → ∀ s : Finset (Pt q), (∀ y, y ∈ s ↔ y.1 ≫ c = y.1 ≫ a) →
    δ.corr d c a hc ha = ∑ y ∈ s, δ.cl d y
  span : ∀ (d : ℕ) {X : Scheme.{0}} (p : X ⟶ S k), SP d p → ∀ (y : Pt p) (U : X.Opens), (U : Set X) = (Set.range y.1)ᶜ →
    ∀ z : V l X (2 * d), pb l U.ι _ z = 0 → ∃ r : ℚ_[l], z = r • δ.cl d y

variable (l) in

def kun {X Y : Scheme.{0}} (p : X ⟶ S k) (q : Y ⟶ S k) (n : ℤ) :
    (⨁ i : ℤ, V l X i ⊗[ℚ_[l]] V l Y (n - i)) →ₗ[ℚ_[l]] V l (pullback p q) n :=
  DirectSum.toModule _ _ _ fun i => TensorProduct.lift
    ((cupV l (pullback p q) (by omega : i + (n - i) = n)).compl₁₂ (pb l (pullback.fst p q) i) (pb l (pullback.snd p q) (n - i)))

def IsFrob (Q : ℕ) {X : Scheme.{0}} (F : X ⟶ X) : Prop :=
  ∀ (A : Type) [CommRing A] (x : Spec (CommRingCat.of A) ⟶ X) (φ : A →+* A), (∀ t, φ t = t ^ Q) →
    x ≫ F = Spec.map (CommRingCat.ofHom φ) ≫ x

end Defs

def Lefschetz : Prop := ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [IsAlgClosed k], (l : k) ≠ 0 →
  ∀ (d : ℕ) {Y X : Scheme.{0}} (q : Y ⟶ S k) (p : X ⟶ S k), SP d q → SP d p → IsProj p →
  ∀ (c a : Y ⟶ X), c ≫ p = q → a ≫ p = q → IsFinite a → Etale a → Etale (equalizer.ι c a ≫ q) →
  altTr l X d (fun n => push l a n ∘ₗ pb l c n) = (Nat.card {y : Pt q // y.1 ≫ c = y.1 ≫ a} : ℚ_[l])

def Fix {κ : Type} [Field κ] (Ω : Type) [Field Ω] [Algebra κ Ω] {Y X : Scheme.{0}} (q : Y ⟶ S κ) (a b : Y ⟶ X)
    (σ : Ω ≃ₐ[κ] Ω) : Type :=
  {y : S Ω ⟶ Y // y ≫ q = Spec.map (CommRingCat.ofHom (algebraMap κ Ω)) ∧
    y ≫ a = Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫ y ≫ b}

def FrobTrace : Prop := ∀ (l : ℕ) [Fact l.Prime] (κ Ω : Type) [Field κ] [Finite κ] [Field Ω] [Algebra κ Ω] [IsAlgClosure κ Ω],
  (l : κ) ≠ 0 → ∀ (d : ℕ) {Y X : Scheme.{0}} (q : Y ⟶ S κ) (p : X ⟶ S κ), SP d q → SP d p → IsProj p →
  ∀ (a b : Y ⟶ X) (ha : a ≫ p = q) (hb : b ≫ p = q), IsFinite a → Etale a →
  ∀ (r : ℕ), 0 < r → ∀ σ : Ω ≃ₐ[κ] Ω, (∀ t, σ t = t ^ Nat.card κ ^ r) →
  altTr l (GlobalTheory.Et.geom Ω p) d (fun n => push l (GlobalTheory.Et.geomMap Ω q a ha) n ∘ₗ pb l (GlobalTheory.Et.geomMap Ω q b hb) n ∘ₗ
    galHQ l Ω p n 0 σ⁻¹) = (Nat.card (Fix Ω q a b σ) : ℚ_[l])

def Finiteness : Prop := ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [IsAlgClosed k], (l : k) ≠ 0 →
  ∀ (d : ℕ) {X : Scheme.{0}} (p : X ⟶ S k), SP d p → ∀ n : ℤ,
  FiniteDimensional ℚ_[l] (V l X n) ∧ (n < 0 ∨ 2 * (d : ℤ) < n → Subsingleton (V l X n))

def Transfer : Prop := ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k], (l : k) ≠ 0 →
  ∀ {Y X : Scheme.{0}} (p : X ⟶ S k), IsProper p → ∀ a : Y ⟶ X, IsFinite a → Etale a →
  (∀ n, IsPush l a n (push l a n)) ∧
  (∀ (n m r : ℤ) (h : n + m = r) (u : V l Y n) (v : V l X m),
    push l a r (cupV l Y h u (pb l a m v)) = cupV l X h (push l a n u) v) ∧
  (Surjective a → ∀ n, Function.Injective (pb l a n))

def Goal : Prop := Base → Finiteness ∧ Transfer ∧ Lefschetz ∧ FrobTrace

def LFin : Prop := Base → Finiteness

def LRing : Prop := Base → ∀ (l : ℕ) [Fact l.Prime],
  (∀ (X : Scheme.{0}) (n m r : ℤ) (h : n + m = r), IsCup l X h (cupV l X h)) ∧
  (∀ {Y X : Scheme.{0}} (f : Y ⟶ X) (n m r : ℤ) (h : n + m = r) (u : V l X n) (v : V l X m),
    pb l f r (cupV l X h u v) = cupV l Y h (pb l f n u) (pb l f m v)) ∧
  (∀ (X : Scheme.{0}), IsUnit (l : Γ(X, ⊤)) →
    (∃ z : Hl l (sch.obj X) 0 0, (∀ j, z.1 j = one (l ^ j) (sch.obj X)) ∧ oneV l X = 1 ⊗ₜ z) ∧
    (∀ (n : ℤ) (u : V l X n), cupV l X (zero_add n) (oneV l X) u = u) ∧
    ∀ {Y : Scheme.{0}} (f : Y ⟶ X), pb l f 0 (oneV l X) = oneV l Y) ∧
  (∀ (X : Scheme.{0}) (n m r s t w : ℤ) (h1 : n + m = s) (h2 : s + r = w) (h3 : m + r = t) (h4 : n + t = w)
    (u : V l X n) (v : V l X m) (z : V l X r), cupV l X h2 (cupV l X h1 u v) z = cupV l X h4 u (cupV l X h3 v z)) ∧
  ∀ (X : Scheme.{0}) (n m r : ℤ) (h : n + m = r) (h' : m + n = r) (u : V l X n) (v : V l X m),
    cupV l X h u v = (n * m).negOnePow • cupV l X h' v u

def LTransfer : Prop := Base → Transfer

def LadicH0LocallyConstant : Prop := Base → ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [IsAlgClosed k], (l : k) ≠ 0 →
  (∀ z : V l (S k) 0, ∃! r : ℚ_[l], z = r • oneV l (S k)) ∧
  ∀ {X : Scheme.{0}} (p : X ⟶ S k), IsProper p → ∀ z : V l X 0,
    ((∀ y : Pt p, pb l y.1 0 z = 0) → z = 0) ∧
    (ConnectedSpace X → ∀ y y' : Pt p, pb l y.1 0 z = pb l y'.1 0 z)

def LKunneth : Prop := Base → ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [IsAlgClosed k], (l : k) ≠ 0 →
  ∀ (d e : ℕ) {X Y : Scheme.{0}} (p : X ⟶ S k) (q : Y ⟶ S k), SP d p → SP e q → ∀ n, Function.Bijective (kun l p q n)

def LCycle : Prop := Base → ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [IsAlgClosed k], (l : k) ≠ 0 →
  ∃ δ : Fam l k, IsDiag δ

def LPd : Prop := Base → ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [IsAlgClosed k], (l : k) ≠ 0 → ∀ d : ℕ,
  SP d (PNto k d) ∧ IsIntegral (PN k d) ∧ ∀ (t : Pt (PNto k d)) (U : (PN k d).Opens), (U : Set (PN k d)) = (Set.range t.1)ᶜ →
    ∃ z : V l (PN k d) (2 * d), z ≠ 0 ∧ pb l U.ι _ z = 0

def LCover : Prop := ∀ (k : Type) [Field k] [IsAlgClosed k] (d : ℕ) {X : Scheme.{0}} (p : X ⟶ S k), SP d p → IsProj p →
  IsIntegral X → ∃ (π : X ⟶ PN k d) (t : Pt (PNto k d)), π ≫ PNto k d = p ∧ IsFinite π ∧ Surjective π ∧
    Etale (equalizer.ι π (p ≫ t.1) ≫ p)

def LInj : Prop := Base → ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [IsAlgClosed k], (l : k) ≠ 0 →
  ∀ (d : ℕ) {X P : Scheme.{0}} (p : X ⟶ S k) (r : P ⟶ S k), SP d p → SP d r → IsIntegral X → IsIntegral P →
  ∀ π : X ⟶ P, π ≫ r = p → IsFinite π → Surjective π → ∀ n, Function.Injective (pb l π n)

def LConst : Prop := Base → ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [IsAlgClosed k], (l : k) ≠ 0 →
  ∀ (δ : Fam l k) (d : ℕ) {X : Scheme.{0}} (p : X ⟶ S k), SP d p → ConnectedSpace X → ∀ y y' : Pt p, δ.cl d y = δ.cl d y'

def LFix : Prop := ∀ (k : Type) [Field k] {Y X : Scheme.{0}} (q : Y ⟶ S k) (p : X ⟶ S k), IsProper q → IsProper p →
  ∀ (c a : Y ⟶ X), c ≫ p = q → a ≫ p = q → Etale (equalizer.ι c a ≫ q) → Finite {y : Pt q // y.1 ≫ c = y.1 ≫ a}

def LTr : Prop := Base → ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [IsAlgClosed k], (l : k) ≠ 0 →
  ∀ δ : Fam l k, IsDiag δ → ∀ (d : ℕ) {X : Scheme.{0}} (p : X ⟶ S k), SP d p → IsProj p →
  ∃ tr : V l X (2 * d) →ₗ[ℚ_[l]] ℚ_[l], ∀ y : Pt p, tr (δ.cl d y) = 1

def LPushPt : Prop := Base → ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [IsAlgClosed k], (l : k) ≠ 0 →
  ∀ δ : Fam l k, IsDiag δ → ∀ (d : ℕ) {Y X : Scheme.{0}} (q : Y ⟶ S k) (p : X ⟶ S k), SP d q → SP d p →
  ∀ (a : Y ⟶ X) (ha : a ≫ p = q), IsFinite a → Etale a → ∀ y : Pt q, push l a _ (δ.cl d y) = δ.cl d (y.map a ha)

def LAlg : Prop := Base → ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [IsAlgClosed k], (l : k) ≠ 0 →
  ∀ δ : Fam l k, IsDiag δ → ∀ (d : ℕ) {Y X : Scheme.{0}} (q : Y ⟶ S k) (p : X ⟶ S k), SP d p →
  ∀ tr : V l X (2 * d) →ₗ[ℚ_[l]] ℚ_[l], (∀ y : Pt p, tr (δ.cl d y) = 1) →
  ∀ (c a : Y ⟶ X) (hc : c ≫ p = q) (ha : a ≫ p = q) (τ : V l Y (2 * d) →ₗ[ℚ_[l]] ℚ_[l])
    (T : ∀ n : ℤ, V l X n →ₗ[ℚ_[l]] V l X n),
    (∀ (n m : ℤ) (h : n + m = 2 * d) (u : V l X n) (v : V l X m),
      τ (cupV l Y h (pb l c n u) (pb l a m v)) = tr (cupV l X h (T n u) v)) →
    τ (δ.corr d c a hc ha) = altTr l X d T

def LFrobId : Prop := Base → ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] (p₀ : ℕ) [Fact p₀.Prime] [CharP k p₀], (l : k) ≠ 0 →
  ∀ {X : Scheme.{0}} (_ : X ⟶ S k) (s : ℕ) (F : X ⟶ X), IsFrob (p₀ ^ s) F → ∀ n, pb l F n = LinearMap.id

def LFrobGeom : Prop := ∀ (κ Ω : Type) [Field κ] [Finite κ] [Field Ω] [Algebra κ Ω] [IsAlgClosure κ Ω]
  (d : ℕ) {Y X : Scheme.{0}} (q : Y ⟶ S κ) (p : X ⟶ S κ), SP d q → SP d p → IsProj p →
  ∀ (a b : Y ⟶ X) (ha : a ≫ p = q) (hb : b ≫ p = q), IsFinite a → Etale a →
  ∀ (r : ℕ), 0 < r → ∀ σ : Ω ≃ₐ[κ] Ω, (∀ t, σ t = t ^ Nat.card κ ^ r) →
  ∀ (q' : GlobalTheory.Et.geom Ω q ⟶ S Ω) (p' : GlobalTheory.Et.geom Ω p ⟶ S Ω), q' = pullback.snd _ _ → p' = pullback.snd _ _ →
  SP d q' ∧ SP d p' ∧ IsProj p' ∧ GlobalTheory.Et.geomMap Ω q a ha ≫ p' = q' ∧
  IsFinite (GlobalTheory.Et.geomMap Ω q a ha) ∧ Etale (GlobalTheory.Et.geomMap Ω q a ha) ∧
  ∃ (c : GlobalTheory.Et.geom Ω q ⟶ GlobalTheory.Et.geom Ω p) (F : GlobalTheory.Et.geom Ω p ⟶ GlobalTheory.Et.geom Ω p), c ≫ p' = q' ∧
    IsFrob (Nat.card κ ^ r) F ∧ c ≫ GlobalTheory.Et.galMap Ω p σ = GlobalTheory.Et.geomMap Ω q b hb ≫ F ∧
    Etale (equalizer.ι c (GlobalTheory.Et.geomMap Ω q a ha) ≫ q') ∧
    Nat.card {y : Pt q' // y.1 ≫ c = y.1 ≫ GlobalTheory.Et.geomMap Ω q a ha} = Nat.card (Fix Ω q a b σ)

end LateralTheory.EtaleTrace

end
