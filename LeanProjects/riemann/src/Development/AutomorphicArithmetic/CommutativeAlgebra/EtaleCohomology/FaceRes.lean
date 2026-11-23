import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.EtaleCohomology.CohomologicalPurity.LeafTubeCutHoc

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC LateralTheory.CohomologicalPurity

namespace UpperTheory.Et.Prd

structure DC where
  A : ℕ → ℤ → Type 1
  [grp : ∀ p s, AddCommGroup (A p s)]
  d : ∀ p s t, A p s →+ A p t
  δ : ∀ p s, A p s →+ A (p + 1) s

attribute [instance] DC.grp

structure DC.Ok (C : DC) : Prop where
  dd : ∀ p s t u x, C.d p t u (C.d p s t x) = 0
  δδ : ∀ p s x, C.δ (p + 1) s (C.δ p s x) = 0
  comm : ∀ p s t x, C.d (p + 1) s t (C.δ p s x) = C.δ p t (C.d p s t x)

abbrev DC.Tot (C : DC) : Type 1 := ∀ p s, C.A p s

def DC.Deg (C : DC) (n : ℤ) (x : C.Tot) : Prop := ∀ (p : ℕ) (s : ℤ), (p : ℤ) + s ≠ n → x p s = 0

def DC.D (C : DC) (n : ℤ) (x : C.Tot) : C.Tot
  | 0, t => C.d 0 (t - 1) t (x 0 (t - 1))
  | p + 1, t => C.d (p + 1) (t - 1) t (x (p + 1) (t - 1)) + (n + 1).negOnePow • C.δ p t (x p t)

abbrev DC.Hom (C C' : DC) : Type 1 := ∀ p s, C.A p s →+ C'.A p s

def DC.Hom.Ok {C C' : DC} (Φ : C.Hom C') : Prop :=
  (∀ p s x, Φ p (s + 1) (C.d p s (s + 1) x) = C'.d p s (s + 1) (Φ p s x)) ∧ ∀ p s x, Φ (p + 1) s (C.δ p s x) = C'.δ p s (Φ p s x)

def DC.Hom.tot {C C' : DC} (Φ : C.Hom C') (x : C.Tot) : C'.Tot := fun p s => Φ p s (x p s)

def DC.Hom.ColEx {C C' : DC} (Φ : C.Hom C') (p : ℕ) : Prop :=
  ∀ (s : ℤ) (a : C.A p (s + 1)) (y : C'.A p s), C.d p (s + 1) (s + 1 + 1) a = 0 → Φ p (s + 1) a = C'.d p s (s + 1) y →
    ∃ (a' : C.A p s) (y' : C'.A p (s - 1)), C.d p s (s + 1) a' = a ∧ y = Φ p s a' + C'.d p (s - 1) s y'

def DC.Hom.TotEx {C C' : DC} (Φ : C.Hom C') : Prop :=
  ∀ (n : ℤ) (a : C.Tot) (y : C'.Tot), C.Deg (n + 1) a → C'.Deg n y → C.D (n + 1) a = 0 → Φ.tot a = C'.D n y →
    ∃ (a' : C.Tot) (y' : C'.Tot), C.Deg n a' ∧ C'.Deg (n - 1) y' ∧ C.D n a' = a ∧ y = Φ.tot a' + C'.D (n - 1) y'

structure Sub (E : Spc) where
  mem : ∀ (p : ℕ) (U : Scheme.{0}), Sx E p U → Prop
  face : ∀ (p : ℕ) (U : Scheme.{0}) (x : Sx E (p + 1) U) (i : Fin (p + 2)), mem (p + 1) U x → mem p U (x.face i)

def Sub.bot (E : Spc) : Sub E := ⟨fun _ _ _ => False, fun _ _ _ _ h => h⟩

def Sub.img {E' E : Spc} (f : E' ⟶ E) : Sub E :=
  ⟨fun p U x => ∃ y : Sx E' p U, y.map f = x, by
    rintro p U _ i ⟨y, rfl⟩
    exact ⟨y.face i, ConcreteCategory.congr_hom
      (NatTrans.congr_app (f.naturality (SimplexCategory.δ i).op) (op U)) y⟩⟩

variable {R : Type} [CommRing R]

def Fam {E : Spc} (Z : Sub E) (p : ℕ) (M : Shv R) : AddSubgroup (∀ U : Scheme.{0}, Sx E p U → Sec M U) where
  carrier := {a | (∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (a U x) = a V (x.res g)) ∧
    ∀ U x, Z.mem p U x → a U x = 0}
  zero_mem' := ⟨fun _ _ _ _ => map_zero _, fun _ _ _ => rfl⟩
  add_mem' {a b} ha hb := ⟨fun V U g x => (map_add _ _ _).trans (congrArg₂ (· + ·) (ha.1 V U g x) (hb.1 V U g x)),
    fun U x h => by rw [Pi.add_apply, Pi.add_apply, ha.2 U x h, hb.2 U x h, add_zero]⟩
  neg_mem' {a} ha := ⟨fun V U g x => (map_neg _ _).trans (congrArg Neg.neg (ha.1 V U g x)),
    fun U x h => by rw [Pi.neg_apply, Pi.neg_apply, ha.2 U x h, neg_zero]⟩

def Fam.map {E : Spc} (Z : Sub E) (p : ℕ) {M N : Shv R} (φ : M ⟶ N) : Fam Z p M →+ Fam Z p N where
  toFun a := ⟨fun U x => Sec.map φ (a.1 U x), fun V U g x => by
      change _ = Sec.map φ (a.1 V (x.res g))
      rw [← a.2.1 V U g x]
      exact (ConcreteCategory.congr_hom (φ.hom.naturality g.op) (a.1 U x)).symm,
    fun U x h => (congrArg (Sec.map φ) (a.2.2 U x h)).trans (map_zero _)⟩
  map_zero' := by ext U x; simp
  map_add' a b := by ext U x; simp

theorem face_res {E : Spc} {p : ℕ} {V U : Scheme.{0}} (g : V ⟶ U) (x : Sx E (p + 1) U) (i : Fin (p + 2)) :
    (x.face i).res g = (x.res g).face i :=
  (ConcreteCategory.congr_hom ((E.δ i).naturality g.op) x).symm

def Fam.δ {E : Spc} (Z : Sub E) (p : ℕ) (M : Shv R) (η : ℤˣ) : Fam Z p M →+ Fam Z (p + 1) M where
  toFun a := ⟨fun U x => η • ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • a.1 U (x.face i), fun V U g x => by
      simp only [Sec.res, Units.smul_def, map_zsmul, map_sum]
      refine congrArg _ (Finset.sum_congr rfl fun i _ => congrArg _ ?_)
      rw [← face_res]; exact a.2.1 V U g _,
    fun U x h => by simp [fun i => a.2.2 U _ (Z.face p U x i h)]⟩
  map_zero' := by ext U x; simp
  map_add' a b := by ext U x; simp [Finset.sum_add_distrib]

def famDC {E : Spc} (Z : Sub E) (K : Cx R) (m : ℤ) : DC where
  A p s := Fam Z p (K.X (s + m))
  d p s t := Fam.map Z p (K.d (s + m) (t + m))
  δ p s := Fam.δ Z p _ m.negOnePow

def Comp {E E' : Spc} (j : E ⟶ E') {Z : Sub E} {K : Cx R} {m N : ℤ} (γ : Cochain ((chains R).obj E') K N)
    (x : (famDC Z K m).Tot) : Prop :=
  ∀ (p : ℕ) (s : ℤ) (h : -(p : ℤ) + N = s + m) (U : Scheme.{0}) (z : Sx E p U),
    (show Fam Z p (K.X (s + m)) from x p s).1 U z = ev γ p (s + m) h U (z.map j)

def HRel {E : Spc} {K : Cx R} {n : ℤ} (x : (famDC (Sub.bot E) K 0).Tot) (c : CohomologyClass ((chains R).obj E) K n) : Prop :=
  ∃ γ : Cocycle ((chains R).obj E) K n, CohomologyClass.mk γ = c ∧ Comp (𝟙 E) γ.1 x

def SRel {P : Arrow Spc} {K : Cx R} {m N : ℤ} (x : (famDC (Sub.img P.hom) K m).Tot)
    (c : CohomologyClass ((chains R).obj (dbl P)) K N) : Prop :=
  ∃ γ : Cocycle ((chains R).obj (dbl P)) K N, CohomologyClass.mk γ = c ∧ Comp (dbl.inl P) γ.1 x ∧
    ∀ (p : ℕ) (s : ℤ) h (U : Scheme.{0}) (z : Sx P.right p U), ev γ.1 p s h U (z.map (dbl.inr P)) = 0

structure TModel (C : DC) (n : ℤ) {H : Type 1} [AddCommGroup H] (rel : C.Tot → H → Prop) : Prop where
  ex : ∀ x, C.Deg n x → C.D n x = 0 → ∃ c, rel x c
  surj : ∀ c, ∃ x, C.Deg n x ∧ C.D n x = 0 ∧ rel x c
  sub : ∀ x c x' c', rel x c → rel x' c' → rel (x - x') (c - c')
  zero : ∀ x c, C.Deg n x → rel x c → (c = 0 ↔ ∃ y, C.Deg (n - 1) y ∧ C.D (n - 1) y = x)

def under {X : Scheme.{0}} {E : Spc} (π : E ⟶ sch.obj X) {p : ℕ} {W : Scheme.{0}} (z : Sx E p W) : W ⟶ X := z.map π

def IsProd {I J K : Cx R} (μ : Pair I J K) {X : Scheme.{0}} {E : Spc} (π : E ⟶ sch.obj X) {m : ℤ} (β : Sec (J.X m) X)
    {Z : Sub E} (Φ : (famDC (Sub.bot E) I 0).Hom (famDC Z K m)) : Prop :=
  ∀ (p : ℕ) (s : ℤ) (a : Fam (Sub.bot E) p (I.X (s + 0))) (W : Scheme.{0}) (z : Sx E p W),
    (show Fam Z p (K.X (s + m)) from Φ p s a).1 W z =
      (m * (p : ℕ)).negOnePow • μ.mul W (s + 0) m (s + m) (by omega) (a.1 W z) (Sec.res (under π z) β)

def IsRep {J : Cx R} {X : Scheme.{0}} (U : X.Opens) {m : ℤ} (β : Sec (J.X m) X)
    (c : CohomologyClass ((chains R).obj (dbl (opn U))) J m) : Prop :=
  Sec.map (J.d m (m + 1)) β = 0 ∧ Sec.res U.ι β = 0 ∧
  ∃ γ : Cocycle ((chains R).obj (dbl (opn U))) J m, CohomologyClass.mk γ = c ∧
    (∀ (W : Scheme.{0}) (x : W ⟶ X), ev γ.1 0 m (by simp) W (Sx.map (E := sch.obj X) (p := 0) (dbl.inl (opn U)) x) = Sec.res x β) ∧
    (∀ (W : Scheme.{0}) (x : W ⟶ X), ev γ.1 0 m (by simp) W (Sx.map (E := sch.obj X) (p := 0) (dbl.inr (opn U)) x) = 0) ∧
    ∀ (p : ℕ) (s : ℤ) h (W : Scheme.{0}) (z : Sx (dbl (opn U)) (p + 1) W), ev γ.1 (p + 1) s h W z = 0

end UpperTheory.Et.Prd

end
