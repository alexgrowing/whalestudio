import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IdTower
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.OmegaPullOmegaTraceOfSecTraceOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.OmegaPullId
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HodgePullHodgePull

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh

universe u v

namespace UpperTheory.Gal.G3

abbrev sp (k : Type) [CommRing k] : Scheme.{0} := Spec (CommRingCat.of k)

structure Th (B : Scheme.{0}) (R : Type) [Field R] where
  H : ∀ {X : Scheme.{0}}, (X ⟶ B) → ModuleCat.{u} R
  pull : ∀ {X Y : Scheme.{0}} {p : X ⟶ B} {q : Y ⟶ B} (f : Y ⟶ X), f ≫ p = q → (H p →ₗ[R] H q)
  pull_id : ∀ {X : Scheme.{0}} (p : X ⟶ B) (h : 𝟙 X ≫ p = p) (x : H p), pull (𝟙 X) h x = x
  pull_comp : ∀ {X Y Z : Scheme.{0}} {p : X ⟶ B} {q : Y ⟶ B} {r : Z ⟶ B} (g : Z ⟶ Y) (f : Y ⟶ X) (hg : g ≫ q = r)
    (hf : f ≫ p = q) (h : (g ≫ f) ≫ p = r) (x : H p), pull (g ≫ f) h x = pull g hg (pull f hf x)

def et (l : ℕ) [Fact l.Prime] (B : Scheme.{0}) : Th.{1} B ℚ_[l] where
  H {X} _ := ModuleCat.of ℚ_[l] (Htot l (sch.obj X))
  pull f _ := pullTot l (sch.map f)
  pull_id p _ x := by
    rw [CategoryTheory.Functor.map_id, pullTot_id]; rfl
  pull_comp g f _ _ _ x := by
    rw [Functor.map_comp, pullTot_comp]; rfl

def etn (l : ℕ) [Fact l.Prime] (B : Scheme.{0}) (n i : ℤ) : Th.{1} B ℚ_[l] where
  H {X} _ := ModuleCat.of ℚ_[l] (HQ l (sch.obj X) n i)
  pull f _ := pullHQ l (sch.map f) n i
  pull_id p _ x := by
    rw [CategoryTheory.Functor.map_id]; unfold pullHQ; rw [pullHl_id, LinearMap.baseChange_id]; rfl
  pull_comp g f _ _ _ x := by
    rw [Functor.map_comp]; unfold pullHQ; rw [pullHl_comp, LinearMap.baseChange_comp]; rfl

def hodge (k : Type) [Field k] (a b : ℕ) : Th.{0} (sp k) k where
  H p := ModuleCat.of k (hodgeH p a b)
  pull _ h := hodgePull h a b
  pull_id p _ x := hodgePull_id p a b x
  pull_comp _ _ hg hf h x := (hodgePull_comp hf hg h a b x).symm

def bcMap {B B' X Y : Scheme.{0}} (g : B ⟶ B') {p : X ⟶ B'} {q : Y ⟶ B'} (f : Y ⟶ X) (h : f ≫ p = q) :
    pullback q g ⟶ pullback p g :=
  pullback.lift (pullback.fst q g ≫ f) (pullback.snd q g) (by rw [Category.assoc, h, pullback.condition])

theorem bcMap_fst {B B' X Y : Scheme.{0}} (g : B ⟶ B') {p : X ⟶ B'} {q : Y ⟶ B'} (f : Y ⟶ X) (h : f ≫ p = q) :
    bcMap g f h ≫ pullback.fst p g = pullback.fst q g ≫ f := pullback.lift_fst _ _ _

theorem bcMap_snd {B B' X Y : Scheme.{0}} (g : B ⟶ B') {p : X ⟶ B'} {q : Y ⟶ B'} (f : Y ⟶ X) (h : f ≫ p = q) :
    bcMap g f h ≫ pullback.snd p g = pullback.snd q g := pullback.lift_snd _ _ _

namespace Th

variable {B : Scheme.{0}} {R : Type} [Field R] (T : Th.{u} B R)

def bc {B' : Scheme.{0}} (g : B ⟶ B') : Th.{u} B' R where
  H p := T.H (pullback.snd p g)
  pull f h := T.pull (bcMap g f h) (bcMap_snd g f h)
  pull_id p h x := by
    have e : bcMap g (𝟙 _) h = 𝟙 _ := by
      apply pullback.hom_ext
      · rw [bcMap_fst, Category.comp_id, Category.id_comp]
      · rw [bcMap_snd, Category.id_comp]
    simp only [e]
    exact T.pull_id _ _ x
  pull_comp {_ _ _ p q r} g' f hg hf h x := by
    have e : bcMap g (g' ≫ f) h = bcMap g g' hg ≫ bcMap g f hf := by
      apply pullback.hom_ext
      · rw [bcMap_fst, Category.assoc, bcMap_fst, ← Category.assoc (bcMap g g' hg), bcMap_fst, Category.assoc]
      · rw [bcMap_snd, Category.assoc, bcMap_snd, bcMap_snd]
    simp only [e]
    exact T.pull_comp _ _ _ _ _ x

def IsTr {Z Y : Scheme.{0}} (p : Z ⟶ B) (q : Y ⟶ B) (s : Y ⟶ Z) (tr : T.H q →ₗ[R] T.H p) : Prop :=
  ∀ (W : Scheme.{0}) (r : W ⟶ B) (c : W ⟶ Z) (hc : c ≫ p = r) (J : Type) [Fintype J] (σ : J → (W ⟶ Y))
    (hσ : ∀ j, σ j ≫ q = r), Splits s c σ → ∀ x, T.pull c hc (tr x) = ∑ j, T.pull (σ j) (hσ j) x

structure Good : Prop where
  inj : ∀ {Z W : Scheme.{0}} (p : Z ⟶ B) (r : W ⟶ B) (c : W ⟶ Z) (hc : c ≫ p = r) (G : Type) [Group G] [Finite G]
    (a : G → (W ⟶ W)), IsGalois c G a → Function.Injective (T.pull c hc)
  tr : ∀ {Z Y : Scheme.{0}} (p : Z ⟶ B) (q : Y ⟶ B) (s : Y ⟶ Z) [IsFinite s] [Etale s], s ≫ p = q →
    ∃ tr, T.IsTr p q s tr

def IsOp {Z Y Z' : Scheme.{0}} (p : Z ⟶ B) (p' : Z' ⟶ B) (s : Y ⟶ Z) (t : Y ⟶ Z') (A : T.H p' →ₗ[R] T.H p) : Prop :=
  ∃ (W : Scheme.{0}) (c : W ⟶ Z) (G : Type) (_ : Group G) (_ : Finite G) (a : G → (W ⟶ W)) (J : Type) (_ : Fintype J)
    (σ : J → (W ⟶ Y)) (h : ∀ j, (σ j ≫ t) ≫ p' = c ≫ p), IsGalois c G a ∧ Splits s c σ ∧
    ∀ x, T.pull c rfl (A x) = ∑ j, T.pull (σ j ≫ t) (h j) x

def IsOpIdx {Z Y Z' : Scheme.{0}} (p : Z ⟶ B) (p' : Z' ⟶ B) (s : Y ⟶ Z) (t : Y ⟶ Z') (n : ℕ)
    (A : T.H p' →ₗ[R] T.H p) : Prop := T.IsOp p p' s t ((n : R) • A)

end Th

def GalSplit {Z Y : Scheme.{0}} (s : Y ⟶ Z) : Prop :=
  ∃ (W : Scheme.{0}) (c : W ⟶ Z) (G : Type) (_ : Group G) (_ : Finite G) (a : G → (W ⟶ W)) (J : Type) (_ : Fintype J)
    (σ : J → (W ⟶ Y)), IsGalois c G a ∧ Splits s c σ

structure Tower (B : Scheme.{0}) (G : Type) [Group G] where
  ι : Type
  K : ι → Subgroup G
  Δ : Submonoid G
  K_le : ∀ i, ∀ k ∈ K i, k ∈ Δ
  deep : ∀ (j : ι) (S : Finset (ι × G)), ∃ m, K m ≤ K j ∧ (∀ k ∈ K j, ∀ u ∈ K m, k * u * k⁻¹ ∈ K m) ∧
    ∀ x ∈ S, ∀ u ∈ K m, x.2 * u * x.2⁻¹ ∈ K x.1
  idx : ∀ i j, (K i).relIndex (K j) ≠ 0
  Z : ι → Scheme.{0}
  q : ∀ i, Z i ⟶ B
  tr : ∀ (i j : ι) (h : G), h ∈ Δ → (∀ u ∈ K i, h * u * h⁻¹ ∈ K j) → (Z i ⟶ Z j)
  tr_q : ∀ i j h a b, tr i j h a b ≫ q j = q i
  tr_self : ∀ i k a b, k ∈ K i → tr i i k a b = 𝟙 _
  tr_mul : ∀ i j m h h' a b a' b' a'' b'', tr i j h a b ≫ tr j m h' a' b' = tr i m (h' * h) a'' b''
  fin : ∀ i j a b, IsFinite (tr i j 1 a b)
  etale : ∀ i j a b, Etale (tr i j 1 a b)
  onto : ∀ i j a b, Surjective (tr i j 1 a b)
  trans : ∀ i j a b, (∀ k ∈ K j, ∀ u ∈ K i, k * u * k⁻¹ ∈ K i) → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x y : sp Ω ⟶ Z i),
    x ≫ tr i j 1 a b = y ≫ tr i j 1 a b → ∃ k ∈ K j, ∃ a' b', y = x ≫ tr i i k a' b'
  free : ∀ i j, K i ≤ K j → ∀ k ∈ K j, ∀ a b (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : sp Ω ⟶ Z i),
    x ≫ tr i i k a b = x → k ∈ K i

def Tower.triv {B X : Scheme.{0}} (p : X ⟶ B) : Tower B Unit where
  ι := Unit
  K _ := ⊤
  Δ := ⊤
  K_le _ _ _ := trivial
  deep _ _ := ⟨(), le_rfl, fun _ _ _ _ => trivial, fun _ _ _ _ => trivial⟩
  idx _ _ := by simp
  Z _ := X
  q _ := p
  tr _ _ _ _ _ := 𝟙 X
  tr_q _ _ _ _ _ := Category.id_comp _
  tr_self _ _ _ _ _ := rfl
  tr_mul _ _ _ _ _ _ _ _ _ _ _ := Category.id_comp _
  fin _ _ _ _ := inferInstance
  etale _ _ _ _ := inferInstance
  onto _ _ _ _ := inferInstance
  trans _ _ _ _ _ _ _ _ x y h := ⟨(), trivial, trivial, fun _ _ => trivial, by simpa using h.symm⟩
  free _ _ _ _ _ _ _ _ _ _ _ _ := trivial

def conv {G R : Type} [Group G] [Field R] (K : Subgroup G) (f f' : G → R) (x : G) : R :=
  ∑ᶠ y : G ⧸ K, f y.out * f' (y.out⁻¹ * x)

def ind {G : Type} [Group G] (R : Type) [Field R] (K : Subgroup G) (g : G) : G → R :=
  Set.indicator (DoubleCoset.doubleCoset g (K : Set G) K) 1

namespace Tower

variable {B : Scheme.{0}} {G : Type} [Group G] (X : Tower B G) {R : Type} [Field R] (T : Th.{u} B R)

def admitted (i j : X.ι) (h : G) : Prop := h ∈ X.Δ ∧ ∀ u ∈ X.K i, h * u * h⁻¹ ∈ X.K j

open Classical in

def pl (i j : X.ι) (h : G) : T.H (X.q j) →ₗ[R] T.H (X.q i) :=
  if a : X.admitted i j h then T.pull (X.tr i j h a.1 a.2) (X.tr_q ..) else 0

def IsFn (j : X.ι) (f : G → R) : Prop :=
  (∀ k ∈ X.K j, ∀ g, f (k * g) = f g ∧ f (g * k) = f g) ∧ (∀ g, f g ≠ 0 → g⁻¹ ∈ X.Δ) ∧
    {y : G ⧸ X.K j | f y.out ≠ 0}.Finite

def IsHop (j : X.ι) (f : G → R) (A : Module.End R (T.H (X.q j))) : Prop :=
  ∀ m, X.K m ≤ X.K j → (∀ g, f g ≠ 0 → X.admitted m j g⁻¹) →
    ∀ x, X.pl T m j 1 (A x) = ∑ᶠ y : G ⧸ X.K j, f y.out • X.pl T m j y.out⁻¹ x

open Classical in

def hecke (j : X.ι) (f : G → R) : Module.End R (T.H (X.q j)) :=
  if h : ∃ A, X.IsHop T j f A then h.choose else 0

structure Endo where
  e : ∀ i, X.Z i ⟶ X.Z i
  e_q : ∀ i, e i ≫ X.q i = X.q i
  comm : ∀ i j h a b, e i ≫ X.tr i j h a b = X.tr i j h a b ≫ e j

def Endo.id : X.Endo := ⟨fun _ => 𝟙 _, fun _ => Category.id_comp _, fun _ _ _ _ _ => by simp⟩

end Tower

end UpperTheory.Gal.G3

end
