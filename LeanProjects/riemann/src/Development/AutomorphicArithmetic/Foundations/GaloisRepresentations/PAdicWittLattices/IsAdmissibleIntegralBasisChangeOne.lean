import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.BcMapFst
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsWtZero
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct

universe u v

namespace UpperTheory.Gal.G3

def Th.ext {B : Scheme.{0}} {R : Type} [Field R] (T : Th.{u} B R) (L : Type) [Field L] [Algebra R L] : Th.{u} B L where
  H p := ModuleCat.of L (L ⊗[R] T.H p)
  pull f h := (T.pull f h).baseChange L
  pull_id p h x := by
    have e : T.pull (𝟙 _) h = LinearMap.id := LinearMap.ext (T.pull_id p h)
    rw [e, LinearMap.baseChange_id]; rfl
  pull_comp g f hg hf h x := by
    have e : T.pull (g ≫ f) h = T.pull g hg ∘ₗ T.pull f hf := LinearMap.ext (T.pull_comp g f hg hf h)
    rw [e, LinearMap.baseChange_comp]; rfl

def lev {G : Type} [Group G] (K : Subgroup G) (h : G) : Subgroup G := K ⊓ K.comap (MulAut.conj h).toMonoidHom

namespace Tower

variable {B : Scheme.{0}} {G : Type} [Group G] (X : Tower B G) {R : Type} [Field R] (T : Th.{u} B R)

theorem admitted.mul {X : Tower B G} {i j m : X.ι} {h h' : G} (a : X.admitted i j h) (a' : X.admitted j m h') : X.admitted i m (h' * h) :=
  ⟨X.Δ.mul_mem a'.1 a.1, fun u hu => by simpa [mul_assoc] using a'.2 _ (a.2 u hu)⟩

theorem isAdmissibleIntegralBasisChange_one {i j : X.ι} (h : X.K i ≤ X.K j) : X.admitted i j 1 := ⟨X.Δ.one_mem, fun u hu => by simpa using h hu⟩

theorem tower_admissible_self {j : X.ι} {k : G} (hk : k ∈ X.K j) : X.admitted j j k :=
  ⟨X.K_le j k hk, fun _ hu => (X.K j).mul_mem ((X.K j).mul_mem hk hu) ((X.K j).inv_mem hk)⟩

theorem pl_eq {i j : X.ι} {h : G} (a : X.admitted i j h) : X.pl T i j h = T.pull (X.tr i j h a.1 a.2) (X.tr_q ..) := dif_pos a

theorem pl_pl {i j m : X.ι} {h h' : G} (a : X.admitted i j h) (a' : X.admitted j m h') (x : T.H (X.q m)) :
    X.pl T i j h (X.pl T j m h' x) = X.pl T i m (h' * h) x := by
  rw [X.pl_eq T a, X.pl_eq T a', X.pl_eq T (a.mul a'), ← T.pull_comp _ _ _ _ (by rw [Category.assoc, X.tr_q, X.tr_q])]
  simp only [X.tr_mul i j m h h' a.1 a.2 a'.1 a'.2 (a.mul a').1 (a.mul a').2]

theorem pl_self {j : X.ι} {k : G} (hk : k ∈ X.K j) (x : T.H (X.q j)) : X.pl T j j k x = x := by
  rw [pl_eq X T (tower_admissible_self X hk)]
  have e := X.tr_self j k (tower_admissible_self X hk).1 (tower_admissible_self X hk).2 hk
  simp only [e, T.pull_id]

theorem pl_left {i j : X.ι} {h k : G} (a : X.admitted i j h) (hk : k ∈ X.K j) (x : T.H (X.q j)) :
    X.pl T i j (k * h) x = X.pl T i j h x := by
  rw [← X.pl_pl T a (X.tower_admissible_self hk), X.pl_self T hk]

end Tower

def SplitsPts : Prop := ∀ {Z Y W : Scheme.{0}} (s : Y ⟶ Z) [IsFinite s] [Etale s] (c : W ⟶ Z) (J : Type) [Finite J]
  (σ : J → (W ⟶ Y)), (∀ j, σ j ≫ s = c) →
  (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : sp Ω ⟶ W) (y : sp Ω ⟶ Y), y ≫ s = x ≫ c → ∃! j, x ≫ σ j = y) → Splits s c σ

def PtsOfSplits : Prop := ∀ {Z Y W : Scheme.{0}} (s : Y ⟶ Z) (c : W ⟶ Z) (J : Type) (σ : J → (W ⟶ Y)), Splits s c σ →
  ∀ (Ω : Type) [Field Ω] (x : sp Ω ⟶ W) (y : sp Ω ⟶ Y), y ≫ s = x ≫ c → ∃! j, x ≫ σ j = y

def IsoPts : Prop := ∀ {Y Z : Scheme.{0}} (f : Y ⟶ Z) [Etale f],
  (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (z : sp Ω ⟶ Z), ∃! y : sp Ω ⟶ Y, y ≫ f = z) → IsIso f

def ExtPts : Prop := ∀ {W Z B : Scheme.{0}} [IsReduced W] (p : Z ⟶ B) [IsSeparated p] (f g : W ⟶ Z), f ≫ p = g ≫ p →
  (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : sp Ω ⟶ W), x ≫ f = x ≫ g) → f = g

def GalOfZM : Prop := ∀ {W Z : Scheme.{0}} (c : W ⟶ Z) (G : Type) [Group G] (ρ : G → (W ⟶ W)),
  GlobalTheory.ZM.IsGaloisCover G ρ c → Finite G ∧ IsGalois c G ρ

def BcSplits : Prop := ∀ {B B' Z Y W : Scheme.{0}} (g : B ⟶ B') (p : Z ⟶ B') (q : Y ⟶ B') (r : W ⟶ B') (s : Y ⟶ Z)
  (hs : s ≫ p = q) (c : W ⟶ Z) (hc : c ≫ p = r) (J : Type) [Finite J] (σ : J → (W ⟶ Y)) (hσ : ∀ j, σ j ≫ q = r)
  [IsFinite s] [Etale s], IsFinite (bcMap g s hs) ∧ Etale (bcMap g s hs) ∧
    (Splits s c σ → Splits (bcMap g s hs) (bcMap g c hc) fun j => bcMap g (σ j) (hσ j))

def BcGal : Prop := ∀ {B B' Z W : Scheme.{0}} (g : B ⟶ B') (p : Z ⟶ B') (r : W ⟶ B') (c : W ⟶ Z) (hc : c ≫ p = r)
  (G : Type) [Group G] [Finite G] (a : G → (W ⟶ W)) (ha : ∀ x, a x ≫ r = r), IsGalois c G a →
    IsGalois (bcMap g c hc) G fun x => bcMap g (a x) (ha x)

def GalClos : Prop := ∀ {Z Y : Scheme.{0}} (s : Y ⟶ Z) [IsFinite s] [Etale s] (d : ℕ),
  (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (z : sp Ω ⟶ Z), Nat.card {y : sp Ω ⟶ Y // y ≫ s = z} = d) → GalSplit s

def EtnGood : Prop := ∀ (l : ℕ) [Fact l.Prime] (B : Scheme.{0}), IsUnit (l : Γ(B, ⊤)) → ∀ n i, (etn l B n i).Good
def EtGood : Prop := ∀ (l : ℕ) [Fact l.Prime] (B : Scheme.{0}), IsUnit (l : Γ(B, ⊤)) → (et l B).Good
def HodgeGood : Prop := ∀ (k : Type) [Field k] [CharZero k] (a b : ℕ), (hodge k a b).Good
def BcGood : Prop := ∀ {B B' : Scheme.{0}} {R : Type} [Field R] (T : Th.{u} B R) (g : B ⟶ B'), T.Good → (T.bc g).Good
def ExtGood : Prop := ∀ {B : Scheme.{0}} {R : Type} [Field R] (T : Th.{u} B R) (L : Type) [Field L] [Algebra R L],
  T.Good → (T.ext L).Good

def HodgeTr : Prop := ∀ (k : Type) [Field k] (a b : ℕ) {Z Y : Scheme.{0}} (p : Z ⟶ sp k) (q : Y ⟶ sp k) (s : Y ⟶ Z)
  [IsFinite s] [Etale s] (hs : s ≫ p = q), (hodge k a b).IsTr p q s (hodgeTrace hs a b)

def HodgeInj : Prop := ∀ (k : Type) [Field k] [CharZero k] (a b : ℕ) {Z W : Scheme.{0}} (p : Z ⟶ sp k) (r : W ⟶ sp k)
  (c : W ⟶ Z) [IsFinite c] [Etale c] [Surjective c] (hc : c ≫ p = r), Function.Injective (hodgePull hc a b)

def EtTr : Prop := ∀ (l : ℕ) [Fact l.Prime] (B : Scheme.{0}), IsUnit (l : Γ(B, ⊤)) → ∀ (n i : ℤ) {Z Y : Scheme.{0}} (p : Z ⟶ B)
  (q : Y ⟶ B) (s : Y ⟶ Z) [IsFinite s] [Etale s], (etn l B n i).IsTr p q s (TranscendenceTraces.trHQ l s (TranscendenceTraces.Wt.const Y 1) n i)

def EtInjFlat : Prop := ∀ (l : ℕ) [Fact l.Prime] (n i : ℤ) {W Z : Scheme.{0}} [CompactSpace Z] (c : W ⟶ Z) [IsFinite c] [Flat c]
  [LocallyOfFinitePresentation c] [Surjective c], IsUnit (l : Γ(Z, ⊤)) → Function.Injective (pullHQ l (sch.map c) n i)

def OpTr : Prop := ∀ {B : Scheme.{0}} {R : Type} [Field R] (T : Th.{u} B R), T.Good → ∀ {Z Y Z' : Scheme.{0}} (p : Z ⟶ B)
  (q : Y ⟶ B) (p' : Z' ⟶ B) (s : Y ⟶ Z) (t : Y ⟶ Z') (_ : s ≫ p = q) (ht : t ≫ p' = q) (tr : T.H q →ₗ[R] T.H p),
  T.IsTr p q s tr → ∀ A, (T.IsOp p p' s t A → A = tr ∘ₗ T.pull t ht) ∧ (GalSplit s → A = tr ∘ₗ T.pull t ht → T.IsOp p p' s t A)

def OpEx : Prop := ∀ {B : Scheme.{0}} {R : Type} [Field R] (T : Th.{u} B R), T.Good → ∀ {Z Y Z' : Scheme.{0}} (p : Z ⟶ B)
  (p' : Z' ⟶ B) (s : Y ⟶ Z) [IsFinite s] [Etale s] (t : Y ⟶ Z'), t ≫ p' = s ≫ p →
  (GalSplit s → ∃! A, T.IsOp p p' s t A) ∧
  ∀ A, T.IsOp p p' s t A → ∀ (W : Scheme.{0}) (r : W ⟶ B) (c : W ⟶ Z) (hc : c ≫ p = r) (J : Type) [Fintype J]
    (σ : J → (W ⟶ Y)) (h : ∀ j, (σ j ≫ t) ≫ p' = r), Splits s c σ → ∀ x, T.pull c hc (A x) = ∑ j, T.pull (σ j ≫ t) (h j) x

def GalInv : Prop := ∀ {B : Scheme.{0}} {R : Type} [Field R] [CharZero R] (T : Th.{u} B R), T.Good →
  ∀ {Z W : Scheme.{0}} (p : Z ⟶ B) (r : W ⟶ B) (c : W ⟶ Z) (hc : c ≫ p = r) (G : Type) [Group G] [Finite G]
    (a : G → (W ⟶ W)) (ha : ∀ g, a g ≫ r = r), IsGalois c G a →
    ∀ y, (∃ x, T.pull c hc x = y) ↔ ∀ g, T.pull (a g) (ha g) y = y

def OpEt : Prop := ∀ (l : ℕ) [Fact l.Prime] {B Z Y Z' : Scheme.{0}} (p : Z ⟶ B) (p' : Z' ⟶ B) (s : Y ⟶ Z) (t : Y ⟶ Z'),
  t ≫ p' = s ≫ p → ∀ A : Htot l (sch.obj Z') →ₗ[ℚ_[l]] Htot l (sch.obj Z), (et l B).IsOp p p' s t A ↔ IsCorrOp l s t A

def OpBc : Prop := ∀ {B B' : Scheme.{0}} {R : Type} [Field R] (T : Th.{u} B R) (g : B ⟶ B') {Z Y Z' : Scheme.{0}}
  (p : Z ⟶ B') (q : Y ⟶ B') (p' : Z' ⟶ B') (s : Y ⟶ Z) [IsFinite s] [Etale s] (t : Y ⟶ Z') (hs : s ≫ p = q) (ht : t ≫ p' = q) (A),
  (T.bc g).IsOp p p' s t A → T.IsOp (pullback.snd p g) (pullback.snd p' g) (bcMap g s hs) (bcMap g t ht) A

def OpNat : Prop := ∀ {B : Scheme.{0}} {R : Type} [Field R] (T : Th.{u} B R) (T' : Th.{v} B R) {Z Z' W : Scheme.{0}} (p : Z ⟶ B)
  (p' : Z' ⟶ B) (r : W ⟶ B) (c : W ⟶ Z) (hc : c ≫ p = r) (J : Type) [Fintype J] (t : J → (W ⟶ Z')) (ht : ∀ j, t j ≫ p' = r)
  (Φ : T'.H p →ₗ[R] T.H p) (Φ' : T'.H p' →ₗ[R] T.H p') (Ψ : T'.H r →ₗ[R] T.H r) (A : T.H p' →ₗ[R] T.H p) (A' : T'.H p' →ₗ[R] T'.H p),
  Function.Injective (T.pull c hc) → Ψ ∘ₗ T'.pull c hc = T.pull c hc ∘ₗ Φ →
  (∀ j, Ψ ∘ₗ T'.pull (t j) (ht j) = T.pull (t j) (ht j) ∘ₗ Φ') →
  (∀ x, T.pull c hc (A x) = ∑ j, T.pull (t j) (ht j) x) → (∀ x, T'.pull c hc (A' x) = ∑ j, T'.pull (t j) (ht j) x) →
  Φ ∘ₗ A' = A ∘ₗ Φ'

def TwSplit : Prop := ∀ {B : Scheme.{0}} {G : Type} [Group G] (X : Tower B G) (m i j : X.ι) (a : X.admitted i j 1) (b : X.admitted m j 1),
  X.K m ≤ X.K i → (∀ k ∈ X.K j, ∀ u ∈ X.K m, k * u * k⁻¹ ∈ X.K m) → ∀ (J : Type) [Finite J] (r : J → G)
  (c : ∀ x, X.admitted m i (r x)), (∀ x, r x ∈ X.K j) → (∀ k ∈ X.K j, ∃! x, k * (r x)⁻¹ ∈ X.K i) →
  Splits (X.tr i j 1 a.1 a.2) (X.tr m j 1 b.1 b.2) fun x => X.tr m i (r x) (c x).1 (c x).2

def TwGal : Prop := ∀ {B : Scheme.{0}} {G : Type} [Group G] (X : Tower B G) (m j : X.ι) (b : X.admitted m j 1),
  (∀ k ∈ X.K j, ∀ u ∈ X.K m, k * u * k⁻¹ ∈ X.K m) → ∃ (Γ : Type) (_ : Group Γ) (_ : Finite Γ) (r : Γ → G)
    (c : ∀ x, X.admitted m m (r x)), (∀ x, r x ∈ X.K j) ∧ (∀ k ∈ X.K j, ∃! x, k * (r x)⁻¹ ∈ X.K m) ∧
    IsGalois (X.tr m j 1 b.1 b.2) Γ fun x => X.tr m m (r x) (c x).1 (c x).2

def PlInv : Prop := ∀ {B : Scheme.{0}} {G : Type} [Group G] (X : Tower B G) {R : Type} [Field R] [CharZero R] (T : Th.{u} B R),
  T.Good → ∀ (m j : X.ι), X.K m ≤ X.K j → Function.Injective (X.pl T m j 1) ∧
    ((∀ k ∈ X.K j, ∀ u ∈ X.K m, k * u * k⁻¹ ∈ X.K m) → ∀ y, (∀ k ∈ X.K j, X.pl T m m k y = y) → ∃ x, X.pl T m j 1 x = y)

def HopDeep : Prop := ∀ {B : Scheme.{0}} {G : Type} [Group G] (X : Tower B G) {R : Type} [Field R] [CharZero R] (T : Th.{u} B R),
  T.Good → ∀ (j : X.ι) (f : G → R), X.IsFn j f → (∃ m, X.K m ≤ X.K j ∧ ∀ g, f g ≠ 0 → X.admitted m j g⁻¹) ∧
  ∀ (A : Module.End R (T.H (X.q j))) (m : X.ι), X.K m ≤ X.K j → (∀ g, f g ≠ 0 → X.admitted m j g⁻¹) →
    (∀ x, X.pl T m j 1 (A x) = ∑ᶠ y : G ⧸ X.K j, f y.out • X.pl T m j y.out⁻¹ x) → X.IsHop T j f A

def HopEx : Prop := ∀ {B : Scheme.{0}} {G : Type} [Group G] (X : Tower B G) {R : Type} [Field R] [CharZero R] (T : Th.{u} B R),
  T.Good → ∀ (j : X.ι) (f : G → R), X.IsFn j f → X.IsHop T j f (X.hecke T j f) ∧ ∀ A, X.IsHop T j f A → A = X.hecke T j f

def FnRing : Prop := ∀ {B : Scheme.{0}} {G : Type} [Group G] (X : Tower B G) (R : Type) [Field R] (j : X.ι),
  (∀ h ∈ X.Δ, X.IsFn j (ind R (X.K j) h⁻¹)) ∧ X.IsFn j (0 : G → R) ∧
  (∀ f f' : G → R, X.IsFn j f → X.IsFn j f' → X.IsFn j (f + f') ∧ X.IsFn j (conv (X.K j) f f')) ∧
  ∀ (c : R) (f : G → R), X.IsFn j f → X.IsFn j (c • f)

def HopLin : Prop := ∀ {B : Scheme.{0}} {G : Type} [Group G] (X : Tower B G) {R : Type} [Field R] [CharZero R] (T : Th.{u} B R),
  T.Good → ∀ (j : X.ι) (f f' : G → R) (c : R), X.IsFn j f → X.IsFn j f' →
    X.hecke T j (f + f') = X.hecke T j f + X.hecke T j f' ∧ X.hecke T j (c • f) = c • X.hecke T j f

def HopMul : Prop := ∀ {B : Scheme.{0}} {G : Type} [Group G] (X : Tower B G) {R : Type} [Field R] [CharZero R] (T : Th.{u} B R),
  T.Good → ∀ (j : X.ι) (f f' : G → R), X.IsFn j f → X.IsFn j f' →
    X.hecke T j (conv (X.K j) f f') = X.hecke T j f * X.hecke T j f'

def HopNorm : Prop := ∀ {B : Scheme.{0}} {G : Type} [Group G] (X : Tower B G) {R : Type} [Field R] [CharZero R] (T : Th.{u} B R),
  T.Good → ∀ (j : X.ι) (h : G), h ∈ X.Δ → (∀ u, h * u * h⁻¹ ∈ X.K j ↔ u ∈ X.K j) →
    X.hecke T j (ind R (X.K j) h⁻¹) = X.pl T j j h

def HopOp : Prop := ∀ {B : Scheme.{0}} {G : Type} [Group G] (X : Tower B G) {R : Type} [Field R] [CharZero R] (T : Th.{u} B R),
  T.Good → ∀ (i j : X.ι) (h : G) (a : X.admitted i j 1) (b : X.admitted i j h),
    (X.K i).relIndex (lev (X.K j) h) ≠ 0 ∧
    T.IsOpIdx (X.q j) (X.q j) (X.tr i j 1 a.1 a.2) (X.tr i j h b.1 b.2) ((X.K i).relIndex (lev (X.K j) h))
      (X.hecke T j (ind R (X.K j) h⁻¹))

def HopNat : Prop := ∀ {B : Scheme.{0}} {G : Type} [Group G] (X : Tower B G) {R : Type} [Field R] [CharZero R]
  (T : Th.{u} B R) (T' : Th.{v} B R), T.Good → T'.Good → ∀ (Φ : ∀ i, T'.H (X.q i) →ₗ[R] T.H (X.q i)),
  (∀ i j h, X.admitted i j h → Φ i ∘ₗ X.pl T' i j h = X.pl T i j h ∘ₗ Φ j) →
  ∀ (j : X.ι) (f : G → R), X.IsFn j f → Φ j ∘ₗ X.hecke T' j f = X.hecke T j f ∘ₗ Φ j

def HopExt : Prop := ∀ {B : Scheme.{0}} {G : Type} [Group G] (X : Tower B G) {R : Type} [Field R] [CharZero R] (T : Th.{u} B R),
  T.Good → ∀ (L : Type) [Field L] [Algebra R L] (j : X.ι) (f : G → R), X.IsFn j f →
    X.IsFn j (fun g => algebraMap R L (f g)) ∧
    X.hecke (T.ext L) j (fun g => algebraMap R L (f g)) = (X.hecke T j f).baseChange L

def HopLevel : Prop := ∀ {B : Scheme.{0}} {G : Type} [Group G] (X : Tower B G) {R : Type} [Field R] [CharZero R]
  (T : Th.{u} B R), T.Good → ∀ (i j : X.ι), X.K i ≤ X.K j → ∀ f : G → R,
    (X.IsFn j f → X.IsFn i f ∧
      X.hecke T i f ∘ₗ X.pl T i j 1 = (((X.K i).relIndex (X.K j) : ℕ) : R) • (X.pl T i j 1 ∘ₗ X.hecke T j f)) ∧
    (X.IsFn i f → (∀ k ∈ X.K j, ∀ g, f (k * g) = f g) → LinearMap.range (X.hecke T i f) ≤ LinearMap.range (X.pl T i j 1))

def ConvMap : Prop := ∀ {G : Type} [Group G] (K : Subgroup G) {R L : Type} [Field R] [Field L] (φ : R →+* L),
  (∀ f f' : G → R, conv K (φ ∘ f) (φ ∘ f') = φ ∘ conv K f f') ∧ ∀ g, ind L K g = φ ∘ ind R K g

end UpperTheory.Gal.G3

end
