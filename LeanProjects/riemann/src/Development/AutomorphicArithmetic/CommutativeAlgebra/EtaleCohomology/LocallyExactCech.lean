import Mathlib

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace UpperTheory.Et

abbrev PMod (R : Type) [CommRing R] : Type 2 := Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)

abbrev PC (R : Type) [CommRing R] : Type 2 := CochainComplex (PMod R) ℤ

variable {R : Type} [CommRing R]

abbrev sec (M : PMod R) (U : Scheme.{0}) : Type 1 := M.obj (op U)

abbrev rs (M : PMod R) {V U : Scheme.{0}} (g : V ⟶ U) (x : sec M U) : sec M V := (M.map g.op).hom x

abbrev ap {M N : PMod R} (α : M ⟶ N) {U : Scheme.{0}} (x : sec M U) : sec N U := (α.app (op U)).hom x

def LocT (τ : GrothendieckTopology Scheme.{0}) (U : Scheme.{0}) (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop) : Prop :=
  ∃ S : Sieve U, S ∈ τ U ∧ ∀ (V : Scheme.{0}) (g : V ⟶ U), S.arrows g → P V g

def IsCy (K : PC R) (n : ℤ) {U : Scheme.{0}} (z : sec (K.X n) U) : Prop := ap (K.d n (n + 1)) z = 0

def IsBd (K : PC R) (n : ℤ) {U : Scheme.{0}} (z : sec (K.X n) U) : Prop := ∃ y : sec (K.X (n - 1)) U, ap (K.d (n - 1) n) y = z

def Below (K : PC R) (a : ℤ) : Prop := ∀ n, n < a → ∀ (U : Scheme.{0}) (z : sec (K.X n) U), z = 0

def IsInj (τ : GrothendieckTopology Scheme.{0}) (K : PC R) : Prop := ∀ n, Injective (K.X n) ∧ Presheaf.IsSheaf τ (K.X n)

structure IsLocRes (τ : GrothendieckTopology Scheme.{0}) (M : PMod R) (K : PC R) (ι : M ⟶ K.X 0) : Prop where
  below : Below K 0
  inj : ∀ U, Function.Injective (ap ι (U := U))
  zero : ∀ (U : Scheme.{0}) (z : sec (K.X 0) U), IsCy K 0 z ↔ ∃ a, ap ι a = z
  pos : ∀ n, 0 < n → ∀ (U : Scheme.{0}) (z : sec (K.X n) U), IsCy K n z → LocT τ U fun _ g => IsBd K n (rs _ g z)

def QisAt {K L : PC R} (φ : K ⟶ L) (U : Scheme.{0}) (n : ℤ) : Prop :=
  (∀ b : sec (L.X n) U, IsCy L n b → ∃ a : sec (K.X n) U, IsCy K n a ∧ IsBd L n (b - ap (φ.f n) a)) ∧
  ∀ a : sec (K.X n) U, IsCy K n a → IsBd L n (ap (φ.f n) a) → IsBd K n a

def ConeBd {K L : PC R} (φ : K ⟶ L) (s : ℤ) {U : Scheme.{0}} (a : sec (K.X (s + 1)) U) (b : sec (L.X s) U) : Prop :=
  ∃ (a' : sec (K.X s) U) (b' : sec (L.X (s - 1)) U), ap (K.d s (s + 1)) a' = a ∧ b = ap (φ.f s) a' + ap (L.d (s - 1) s) b'

def Inv (q : ℕ) (U : Scheme.{0}) : Prop := IsUnit (q : Γ(U, ⊤))

def ContAt (K : PC R) (q : ℕ) (n : ℤ) : Prop :=
  ∀ {J : Type} [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D), Nonempty (IsColimit c) →
    (∀ j, IsUnit (q : D.obj j)) →
    (∀ z : sec (K.X n) (Spec c.pt), IsCy K n z →
      ∃ (j : J) (y : sec (K.X n) (Spec (D.obj j))), IsCy K n y ∧ IsBd K n (z - rs _ (Spec.map (show D.obj j ⟶ c.pt from c.ι.app j)) y)) ∧
    ∀ (j : J) (y : sec (K.X n) (Spec (D.obj j))), IsCy K n y → IsBd K n (rs _ (Spec.map (show D.obj j ⟶ c.pt from c.ι.app j)) y) →
      ∃ (k : J) (f : j ⟶ k), IsBd K n (rs _ (Spec.map (D.map f)) y)

structure Model (K : PC R) (n : ℤ) (H : Scheme.{0} → Type 1) [∀ X, AddCommGroup (H X)]
    (pull : ∀ {Y X : Scheme.{0}}, (Y ⟶ X) → H X → H Y) (rel : ∀ X : Scheme.{0}, sec (K.X n) X → H X → Prop) : Prop where
  ex : ∀ X z, IsCy K n z → ∃ y, rel X z y
  surj : ∀ X y, ∃ z, rel X z y
  cyc : ∀ X z y, rel X z y → IsCy K n z
  sub : ∀ X z y z' y', rel X z y → rel X z' y' → rel X (z - z') (y - y')
  zero : ∀ X z y, rel X z y → (y = 0 ↔ IsBd K n z)
  nat : ∀ {Y X : Scheme.{0}} (f : Y ⟶ X) z y, rel X z y → rel Y (rs _ f z) (pull f y)

def Gen (τ : GrothendieckTopology Scheme.{0}) (q : ℕ) (M : PMod R) {U : Scheme.{0}} (g : sec M U) : Prop :=
  q • g = 0 ∧ (∀ (V : Scheme.{0}) (k : V ⟶ U) (c : ℕ), Nonempty V → c • rs M k g = 0 → q ∣ c) ∧
  ∀ (V : Scheme.{0}) (k : V ⟶ U) (y : sec M V), LocT τ V fun _ h => ∃ c : ℕ, rs M h y = c • rs M (h ≫ k) g

section Cech
variable {Y X : Scheme.{0}} (f : Y ⟶ X)

@[ext] structure Pt {U : Scheme.{0}} (π : U ⟶ X) (p : ℕ) (W : Scheme.{0}) : Type where
  u : W ⟶ U
  y : Fin p → (W ⟶ Y)
  w : ∀ i, y i ≫ f = u ≫ π

variable {f} in

def Pt.pre {U : Scheme.{0}} {π : U ⟶ X} {p : ℕ} {W' W : Scheme.{0}} (k : W' ⟶ W) (x : Pt f π p W) : Pt f π p W' :=
  ⟨k ≫ x.u, fun i => k ≫ x.y i, fun i => by rw [Category.assoc, x.w i, Category.assoc]⟩

variable {f} in

def Pt.face {U : Scheme.{0}} {π : U ⟶ X} {p : ℕ} {W : Scheme.{0}} (x : Pt f π (p + 1) W) (i : Fin (p + 1)) : Pt f π p W :=
  ⟨x.u, fun j => x.y (i.succAbove j), fun _ => x.w _⟩

variable {f} in

def Pt.post {V U : Scheme.{0}} (g : V ⟶ U) {π : U ⟶ X} {π' : V ⟶ X} (e : g ≫ π = π') {p : ℕ} {W : Scheme.{0}}
    (x : Pt f π' p W) : Pt f π p W :=
  ⟨x.u ≫ g, x.y, fun i => by rw [x.w i, Category.assoc, e]⟩

def Cc (M : PMod R) {U : Scheme.{0}} (π : U ⟶ X) (p : ℕ) : AddSubgroup (∀ W : Scheme.{0}, Pt f π p W → sec M W) where
  carrier := {c | ∀ (W' W : Scheme.{0}) (k : W' ⟶ W) (x : Pt f π p W), rs M k (c W x) = c W' (x.pre k)}
  zero_mem' _ _ _ _ := map_zero _
  add_mem' {a b} ha hb W' W k x := (map_add _ _ _).trans (congrArg₂ (· + ·) (ha W' W k x) (hb W' W k x))
  neg_mem' {a} ha W' W k x := (map_neg _ _).trans (congrArg Neg.neg (ha W' W k x))

variable {f}

def Cc.δ {M : PMod R} {U : Scheme.{0}} {π : U ⟶ X} {p : ℕ} : Cc f M π p →+ Cc f M π (p + 1) where
  toFun c := ⟨fun W x => ∑ i : Fin (p + 1), (-1 : ℤ) ^ (i : ℕ) • c.1 W (x.face i), by
    intro W' W k x
    simp only [rs, map_sum, map_zsmul]
    exact Finset.sum_congr rfl fun i _ => congrArg _ (c.2 W' W k _)⟩
  map_zero' := by ext W x; simp
  map_add' a b := by ext W x; simp [Finset.sum_add_distrib]

def Cc.map {M N : PMod R} (α : M ⟶ N) {U : Scheme.{0}} {π : U ⟶ X} {p : ℕ} : Cc f M π p →+ Cc f N π p where
  toFun c := ⟨fun W x => ap α (c.1 W x), by
    intro W' W k x
    change _ = ap α (c.1 W' (x.pre k))
    rw [← c.2 W' W k x]
    exact (ConcreteCategory.congr_hom (α.naturality k.op) (c.1 W x)).symm⟩
  map_zero' := by ext W x; simp
  map_add' a b := by ext W x; simp

def Cc.res {M : PMod R} {V U : Scheme.{0}} (g : V ⟶ U) {π : U ⟶ X} {π' : V ⟶ X} (e : g ≫ π = π') {p : ℕ} :
    Cc f M π p →+ Cc f M π' p where
  toFun c := ⟨fun W x => c.1 W (x.post g e), by
    intro W' W k x
    exact (c.2 W' W k _).trans (congrArg (c.1 W') (Pt.ext (Category.assoc _ _ _).symm rfl))⟩
  map_zero' := rfl
  map_add' _ _ := rfl

def Cc.Cy (K : PC R) (n : ℤ) {U : Scheme.{0}} {π : U ⟶ X} {p : ℕ} (c : Cc f (K.X n) π p) : Prop :=
  Cc.map (K.d n (n + 1)) c = 0

def Cc.Bd (K : PC R) (n : ℤ) {U : Scheme.{0}} {π : U ⟶ X} {p : ℕ} (c : Cc f (K.X n) π p) : Prop :=
  ∃ b : Cc f (K.X (n - 1)) π p, Cc.map (K.d (n - 1) n) b = c

variable (f)

def RowExact (M : PMod R) : Prop := ∀ (U : Scheme.{0}) (π : U ⟶ X),
  (∀ c : Cc f M π 0, Cc.δ c = 0 → c = 0) ∧ ∀ (p : ℕ) (c : Cc f M π (p + 1)), Cc.δ c = 0 → ∃ b : Cc f M π p, Cc.δ b = c

def LocallyExactCech (τ : GrothendieckTopology Scheme.{0}) (K : PC R) (m : ℤ) : Prop :=
  ∀ (U : Scheme.{0}) (π : U ⟶ X) (p : ℕ) (x : Cc f (K.X m) π (p + 1)), Cc.Cy K m x → Cc.Bd K m (Cc.δ x) →
    LocT τ U fun _ g => ∃ c : Cc f (K.X m) (g ≫ π) p, Cc.Cy K m c ∧ Cc.Bd K m (Cc.res g rfl x - Cc.δ c)

variable {f} in

def Pt.Univ {U : Scheme.{0}} {π : U ⟶ X} {p : ℕ} {Z : Scheme.{0}} (x₀ : Pt f π p Z) : Prop :=
  ∀ (W : Scheme.{0}) (x : Pt f π p W), ∃! k : W ⟶ Z, x₀.pre k = x

end Cech

end UpperTheory.Et

end
