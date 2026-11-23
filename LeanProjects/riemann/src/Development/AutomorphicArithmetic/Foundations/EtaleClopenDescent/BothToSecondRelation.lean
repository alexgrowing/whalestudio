import Mathlib
import Development.EtaleCohomology.EtaleSheaves.LeafChartRing

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace UpperTheory.Aff

structure RF where
  obj : ∀ (A : Type) [CommRing A], Type
  map : ∀ {A B : Type} [CommRing A] [CommRing B], (A →+* B) → obj A → obj B
  map_id : ∀ {A : Type} [CommRing A] (x : obj A), map (RingHom.id A) x = x
  map_comp : ∀ {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) (x : obj A),
    map (g.comp f) x = map g (map f x)
  rel : ∀ {A : Type} [CommRing A], obj A → obj A → Prop
  map_rel : ∀ {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {x y : obj A}, rel x y → rel (map f x) (map f y)

structure RF.Hom (X Y : RF) where
  app : ∀ (A : Type) [CommRing A], X.obj A → Y.obj A
  nat : ∀ {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (x : X.obj A), app B (X.map f x) = Y.map f (app A x)

def RF.Hom.Rel {X Y : RF} (h : X.Hom Y) : Prop :=
  ∀ {A : Type} [CommRing A] {x y : X.obj A}, X.rel x y → Y.rel (h.app A x) (h.app A y)

def RF.Hom.Const {X Y : RF} (h : X.Hom Y) : Prop :=
  ∀ {A : Type} [CommRing A] {x y : X.obj A}, X.rel x y → h.app A x = h.app A y

def RF.psh (X : RF) : PSh where
  obj U := X.obj Γ(U.unop, ⊤)
  map f := TypeCat.ofHom (X.map f.unop.appTop.hom)
  map_id U := by
    ext x
    exact X.map_id x
  map_comp f g := by
    ext x
    exact X.map_comp f.unop.appTop.hom g.unop.appTop.hom x

def RF.Hom.psh {X Y : RF} (h : X.Hom Y) : X.psh ⟶ Y.psh where
  app U := TypeCat.ofHom (h.app Γ(U.unop, ⊤))
  naturality U V f := by
    ext x
    exact h.nat f.unop.appTop.hom x

def CN (X : RF) : Spc where
  obj n :=
    { obj := fun U => {x : Fin (n.unop.len + 1) → X.obj Γ(U.unop, ⊤) // ∀ i j, X.rel (x i) (x j)}
      map := fun f => TypeCat.ofHom fun x =>
        ⟨fun i => X.map f.unop.appTop.hom (x.1 i), fun i j => X.map_rel _ (x.2 i j)⟩
      map_id := fun U => by
        ext x i
        exact X.map_id (x.1 i)
      map_comp := fun f g => by
        ext x i
        exact X.map_comp f.unop.appTop.hom g.unop.appTop.hom (x.1 i) }
  map θ :=
    { app := fun U => TypeCat.ofHom fun x => ⟨fun i => x.1 (θ.unop.toOrderHom i), fun i j => x.2 _ _⟩
      naturality := fun U V f => rfl }
  map_id n := rfl
  map_comp θ θ' := rfl

def CN.map {X Y : RF} (h : X.Hom Y) (hr : h.Rel) : CN X ⟶ CN Y where
  app n :=
    { app := fun U => TypeCat.ofHom fun x => ⟨fun i => h.app _ (x.1 i), fun i j => hr (x.2 i j)⟩
      naturality := fun U V f => by
        refine ConcreteCategory.hom_ext _ _ fun x => Subtype.ext (funext fun i => ?_)
        exact h.nat f.unop.appTop.hom (x.1 i) }
  naturality n m θ := rfl

def CN.proj {X M : RF} (ρ : X.Hom M) (hc : ρ.Const) : CN X ⟶ disc.obj M.psh where
  app n :=
    { app := fun U => TypeCat.ofHom fun x => ρ.app _ (x.1 0)
      naturality := fun U V f => by
        ext x
        exact ρ.nat f.unop.appTop.hom (x.1 0) }
  naturality n m θ := by
    ext U x
    exact hc (x.2 _ _)

def RF.sub (X : RF) (P : ∀ {A : Type} [CommRing A], X.obj A → Prop)
    (hP : ∀ {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {x : X.obj A}, P x → P (X.map f x)) : RF where
  obj A _ := {x : X.obj A // P x}
  map f x := ⟨X.map f x.1, hP f x.2⟩
  map_id x := Subtype.ext (X.map_id x.1)
  map_comp f g x := Subtype.ext (X.map_comp f g x.1)
  rel x y := X.rel x.1 y.1
  map_rel f _ _ h := X.map_rel f h

def RF.subι (X : RF) (P : ∀ {A : Type} [CommRing A], X.obj A → Prop)
    (hP : ∀ {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {x : X.obj A}, P x → P (X.map f x)) :
    (X.sub P hP).Hom X where
  app _ _ x := x.1
  nat _ _ := rfl

theorem RF.subι_rel (X : RF) (P : ∀ {A : Type} [CommRing A], X.obj A → Prop)
    (hP : ∀ {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {x : X.obj A}, P x → P (X.map f x)) :
    (X.subι P hP).Rel := fun h => h

variable (D : Type) [CommRing D]

def Aff (N : ℕ) : RF where
  obj A _ := (D →+* A) × (Fin N → A)
  map f x := (f.comp x.1, f ∘ x.2)
  map_id _ := rfl
  map_comp _ _ _ := rfl
  rel x y := x = y
  map_rel _ _ _ h := by rw [h]

def Vec (N : ℕ) : RF where
  obj A _ := {x : (D →+* A) × (Fin N → A) // Ideal.span (Set.range x.2) = ⊤}
  map f x := ⟨(f.comp x.1.1, f ∘ x.1.2), by rw [Set.range_comp, ← Ideal.map_span, x.2, Ideal.map_top]⟩
  map_id _ := rfl
  map_comp _ _ _ := rfl
  rel {A} _ x y := x.1.1 = y.1.1 ∧ ∃ u : Aˣ, x.1.2 = fun j => (u : A) * y.1.2 j
  map_rel {A B} _ _ f x y h := by
    obtain ⟨h1, u, h2⟩ := h
    refine ⟨congrArg f.comp h1, Units.map (f : A →* B) u, funext fun j => ?_⟩
    simp [h2]

variable {D}

def Vec.toAff (N : ℕ) : (Vec D N).Hom (Aff D N) where
  app _ _ x := x.1
  nat _ _ := rfl

def P2 {d : ℕ} {A : Type} [CommRing A] (x : (Vec D (d + 1)).obj A) : Prop :=
  Ideal.span (Set.range fun j : Fin d => x.1.2 j.castSucc) = ⊤

def P1 {d : ℕ} {A : Type} [CommRing A] (x : (Vec D (d + 1)).obj A) : Prop := IsUnit (x.1.2 (Fin.last d))

theorem second_property_map {d : ℕ} {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {x : (Vec D (d + 1)).obj A} (h : P2 x) :
    P2 ((Vec D (d + 1)).map f x) := by
  have : (Set.range fun j : Fin d => ((Vec D (d + 1)).map f x).1.2 j.castSucc) =
      f '' (Set.range fun j : Fin d => x.1.2 j.castSucc) := by
    rw [← Set.range_comp]; rfl
  rw [P2, this, ← Ideal.map_span, h, Ideal.map_top]

theorem first_property_map {d : ℕ} {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {x : (Vec D (d + 1)).obj A} (h : P1 x) :
    P1 ((Vec D (d + 1)).map f x) := h.map f

variable (D)

abbrev L2 (d : ℕ) : RF := (Vec D (d + 1)).sub P2 second_property_map

abbrev L1 (d : ℕ) : RF := (Vec D (d + 1)).sub P1 first_property_map

abbrev lift_levelP_alt₂ (d : ℕ) : RF := (Vec D (d + 1)).sub (fun x => P2 x ∧ P1 x) fun f _ h => ⟨second_property_map f h.1, first_property_map f h.2⟩

theorem span_snoc {A : Type} [CommRing A] {N : ℕ} (v : Fin N → A) (w : A) (h : Ideal.span (Set.range v) = ⊤) :
    Ideal.span (Set.range (Fin.snoc (α := fun _ => A) v w)) = ⊤ := by
  rw [eq_top_iff, ← h]
  refine Ideal.span_mono ?_
  rintro _ ⟨j, rfl⟩
  exact ⟨j.castSucc, by simp⟩

theorem comp_snoc' {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {N : ℕ} (v : Fin N → A) (w : A) :
    f ∘ (Fin.snoc (α := fun _ => A) v w) = Fin.snoc (α := fun _ => B) (f ∘ v) (f w) := by
  funext j
  refine Fin.lastCases ?_ (fun j => ?_) j <;> simp

def incl (d : ℕ) : (Vec D d).Hom (Vec D (d + 1)) where
  app _ _ x := ⟨(x.1.1, Fin.snoc (α := fun _ => _) x.1.2 0), span_snoc _ _ x.2⟩
  nat f x := Subtype.ext (Prod.ext rfl (by
    change Fin.snoc (α := fun _ => _) (f ∘ x.1.2) 0 = f ∘ Fin.snoc (α := fun _ => _) x.1.2 0
    rw [comp_snoc', map_zero]))

def incl2 (d : ℕ) : (Vec D d).Hom (L2 D d) where
  app _ _ x := ⟨(incl D d).app _ x, by
    change Ideal.span (Set.range fun j : Fin d => Fin.snoc (α := fun _ => _) x.1.2 0 j.castSucc) = ⊤
    simpa using x.2⟩
  nat f x := Subtype.ext ((incl D d).nat f x)

def fstV (d : ℕ) : (L2 D d).Hom (Vec D d) where
  app _ _ x := ⟨(x.1.1.1, fun j => x.1.1.2 j.castSucc), x.2⟩
  nat _ _ := rfl

def lastInv {d : ℕ} {A : Type} [CommRing A] (x : (Vec D (d + 1)).obj A) : A := Ring.inverse (x.1.2 (Fin.last d))

theorem map_inverse {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {a : A} (h : IsUnit a) :
    f (Ring.inverse a) = Ring.inverse (f a) := by
  obtain ⟨u, rfl⟩ := h
  have h1 : f (u : A) = ((Units.map (f : A →* B) u : Bˣ) : B) := rfl
  rw [Ring.inverse_unit, h1, Ring.inverse_unit]
  rfl

theorem lastInv_map {d : ℕ} {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {x : (Vec D (d + 1)).obj A} (h : P1 x) :
    lastInv D ((Vec D (d + 1)).map f x) = f (lastInv D x) :=
  (map_inverse f h).symm

def ratio1 (d : ℕ) : (L1 D d).Hom (Aff D d) where
  app _ _ x := (x.1.1.1, fun j => x.1.1.2 j.castSucc * lastInv D x.1)
  nat f x := Prod.ext rfl (funext fun j => by
    change f (x.1.1.2 j.castSucc) * lastInv D ((Vec D (d + 1)).map f x.1) = f (x.1.1.2 j.castSucc * lastInv D x.1)
    rw [lastInv_map D f x.2, map_mul])

theorem span_mul_unit {A : Type} [CommRing A] {N : ℕ} (v : Fin N → A) {c : A} (hc : IsUnit c)
    (h : Ideal.span (Set.range v) = ⊤) : Ideal.span (Set.range fun j => v j * c) = ⊤ := by
  rw [eq_top_iff, ← h]
  refine Ideal.span_le.2 ?_
  rintro _ ⟨j, rfl⟩
  obtain ⟨u, rfl⟩ := hc
  have h1 : v j = ((u⁻¹ : Aˣ) : A) * (v j * u) := by
    rw [mul_comm (v j), ← mul_assoc, Units.inv_mul, one_mul]
  rw [h1]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)

theorem isUnit_lastInv {d : ℕ} {A : Type} [CommRing A] {x : (Vec D (d + 1)).obj A} (h : P1 x) :
    IsUnit (lastInv D x) := by
  obtain ⟨u, hu⟩ := h
  rw [lastInv, ← hu, Ring.inverse_unit]
  exact (u⁻¹).isUnit

def ratioBoth (d : ℕ) : (lift_levelP_alt₂ D d).Hom (Vec D d) where
  app _ _ x := ⟨(x.1.1.1, fun j => x.1.1.2 j.castSucc * lastInv D x.1), span_mul_unit _ (isUnit_lastInv D x.2.2) x.2.1⟩
  nat f x := Subtype.ext (Prod.ext rfl (funext fun j => by
    change f (x.1.1.2 j.castSucc) * lastInv D ((Vec D (d + 1)).map f x.1) = f (x.1.1.2 j.castSucc * lastInv D x.1)
    rw [lastInv_map D f x.2.2, map_mul]))

def bothToFirst (d : ℕ) : (lift_levelP_alt₂ D d).Hom (L1 D d) where
  app _ _ x := ⟨x.1, x.2.2⟩
  nat _ _ := rfl

def bothToSecond (d : ℕ) : (lift_levelP_alt₂ D d).Hom (L2 D d) where
  app _ _ x := ⟨x.1, x.2.1⟩
  nat _ _ := rfl

theorem incl_rel (d : ℕ) : (incl D d).Rel := by
  intro A _ x y h
  obtain ⟨h1, u, h2⟩ := h
  refine ⟨h1, u, funext fun j => ?_⟩
  change Fin.snoc (α := fun _ => A) x.1.2 0 j = (u : A) * Fin.snoc (α := fun _ => A) y.1.2 0 j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · simp
  · simp [h2]

theorem inclusion_two_relation (d : ℕ) : (incl2 D d).Rel := fun h => incl_rel D d h

theorem fstV_rel (d : ℕ) : (fstV D d).Rel := by
  intro A _ x y h
  obtain ⟨h1, u, h2⟩ := h
  exact ⟨h1, u, funext fun j => congrFun h2 j.castSucc⟩

theorem both_to_first_relation (d : ℕ) : (bothToFirst D d).Rel := fun h => h

theorem both_to_second_relation (d : ℕ) : (bothToSecond D d).Rel := fun h => h

theorem ratio1_const (d : ℕ) : (ratio1 D d).Const := by
  intro A _ x y h
  obtain ⟨h1, u, h2⟩ := h
  have hy : IsUnit (y.1.1.2 (Fin.last d)) := y.2
  have hx : x.1.1.2 (Fin.last d) = (u : A) * y.1.1.2 (Fin.last d) := congrFun h2 _
  obtain ⟨w, hw⟩ := hy
  refine Prod.ext h1 (funext fun j => ?_)
  change x.1.1.2 j.castSucc * Ring.inverse (x.1.1.2 (Fin.last d)) =
    y.1.1.2 j.castSucc * Ring.inverse (y.1.1.2 (Fin.last d))
  rw [hx, congrFun h2 j.castSucc, ← hw, ← Units.val_mul, Ring.inverse_unit, Ring.inverse_unit, mul_inv, Units.val_mul,
    mul_comm ((u⁻¹ : Aˣ) : A)]
  simp only [Units.val_mul, mul_assoc]
  linear_combination ((y.1.1.2 j.castSucc) * ((w⁻¹ : Aˣ) : A)) * Units.mul_inv u

theorem ratio_both_constant (d : ℕ) : (ratioBoth D d).Const := by
  intro A _ x y h
  exact Subtype.ext (ratio1_const D d (x := bothToFirst D d |>.app A x) (y := bothToFirst D d |>.app A y) h)

def sec1 (d : ℕ) : (Aff D d).Hom (L1 D d) where
  app _ _ x := ⟨⟨(x.1, Fin.snoc (α := fun _ => _) x.2 1),
      (Ideal.eq_top_iff_one _).2 (Ideal.subset_span ⟨Fin.last d, by simp⟩)⟩, by simp [P1]⟩
  nat f x := Subtype.ext (Subtype.ext (Prod.ext rfl (by
    change Fin.snoc (α := fun _ => _) (f ∘ x.2) 1 = f ∘ Fin.snoc (α := fun _ => _) x.2 1
    rw [comp_snoc', map_one])))

def specOf {B : Type} [CommRing B] {T : Scheme.{0}} (ψ : B →+* Γ(T, ⊤)) : T ⟶ Spec (CommRingCat.of B) :=
  T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom ψ)

theorem comp_specOf {B : Type} [CommRing B] {T T' : Scheme.{0}} (f : T' ⟶ T) (ψ : B →+* Γ(T, ⊤)) :
    f ≫ specOf ψ = specOf (f.appTop.hom.comp ψ) := by
  rw [specOf, specOf, ← Category.assoc, Scheme.toSpecΓ_naturality, Category.assoc, ← Spec.map_comp]
  rfl

variable {D} in

def ringOf {N : ℕ} {A : Type} [CommRing A] (x : (Aff D N).obj A) : MvPolynomial (Fin N) D →+* A :=
  MvPolynomial.eval₂Hom x.1 x.2

theorem ringOf_map {N : ℕ} {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (x : (Aff D N).obj A) :
    ringOf ((Aff D N).map f x) = f.comp (ringOf x) := by
  refine MvPolynomial.ringHom_ext (fun c => ?_) (fun j => ?_)
  · simp [ringOf, Aff]
  · simp [ringOf, Aff]

def repA (N : ℕ) : (Aff D N).psh ⟶ yoneda.obj (Spec (CommRingCat.of (MvPolynomial (Fin N) D))) where
  app U := TypeCat.ofHom fun x => specOf (ringOf x)
  naturality U V f := by
    ext x
    change specOf (ringOf ((Aff D N).map f.unop.appTop.hom x)) = f.unop ≫ specOf (ringOf x)
    rw [comp_specOf]
    exact congrArg specOf (ringOf_map D _ x)

section Formal
open LateralTheory.E.t_E6Cut
variable {R : Type} [CommRing R] (F : Shv R)

theorem eqv_section {E E' : Spc} (s : E ⟶ E') (p : E' ⟶ E) (h : s ≫ p = 𝟙 E) (hp : Eqv R p F) : Eqv R s F := by
  intro n
  have hl : Function.LeftInverse (pull R s F n) (pull R p F n) := fun x => by
    rw [← pull_comp, h, pull_id]
  refine (Function.bijective_iff_has_inverse).2 ⟨pull R p F n, ?_, hl⟩
  exact fun y => by
    obtain ⟨x, rfl⟩ := (hp n).2 y
    rw [hl x]

theorem conn_sq (c : ℤ) {A B A' B' : Spc} (f : A ⟶ B) (f' : A' ⟶ B') (u : A ⟶ A') (v : B ⟶ B') (h : f ≫ v = u ≫ f')
    (hu : Eqv R u F) (hv : Eqv R v F) : Conn R F c f ↔ Conn R F c f' := by
  have key : ∀ n, (pull R f F n ∘ pull R v F n) = pull R u F n ∘ pull R f' F n := fun n => by
    funext x
    simp only [Function.comp]
    rw [← pull_comp, ← pull_comp, h]
  have hb : ∀ n, Function.Bijective (pull R f F n) ↔ Function.Bijective (pull R f' F n) := fun n => by
    rw [← Function.Bijective.of_comp_iff (pull R f F n) (hv n), key n, Function.Bijective.of_comp_iff' (hu n)]
  have hi : ∀ n, Function.Injective (pull R f F n) ↔ Function.Injective (pull R f' F n) := fun n => by
    rw [← Function.Injective.of_comp_iff' (pull R f F n) (hv n), key n, Function.Injective.of_comp_iff (hu n).1]
  constructor
  · intro hc n
    exact ⟨fun h' => (hb n).1 ((hc n).1 h'), fun h' => (hi n).1 ((hc n).2 h')⟩
  · intro hc n
    exact ⟨fun h' => (hb n).2 ((hc n).1 h'), fun h' => (hi n).2 ((hc n).2 h')⟩

end Formal

end UpperTheory.Aff

end
