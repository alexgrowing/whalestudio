import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.TPullTMap

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.CH
open GlobalTheory.CatH (face toLast)

namespace UpperTheory.Ru.crystallineComparison.Th

variable {C : Type 1} [Category.{0} C]

theorem fa_ext {X : Type 1} {A : AddCommGrpCat.{1}} {f g : AddCommGrpCat.of (FreeAbelianGroup X) ⟶ A}
    (h : ∀ x, f.hom (FreeAbelianGroup.of x) = g.hom (FreeAbelianGroup.of x)) : f = g := by
  refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun x => ?_)
  induction x using FreeAbelianGroup.induction_on with
  | zero => simp
  | of x => exact h x
  | neg x ih => simpa using congrArg Neg.neg (h x)
  | add x y hx hy => simp only [map_add, hx, hy]

variable (P : C ⥤ Type)

abbrev Gen (k : ℕ) (B : C) : Type 1 := Σ s : ComposableArrows P.Elements k, ((s.obj (Fin.last k)).1 ⟶ B)

def L (k : ℕ) : Coef C where
  obj B := AddCommGrpCat.of (FreeAbelianGroup (Gen P k B))
  map φ := AddCommGrpCat.ofHom (FreeAbelianGroup.map fun g => ⟨g.1, g.2 ≫ φ⟩)
  map_id B := fa_ext fun x => by simp
  map_comp φ ψ := fa_ext fun x => by simp

def gFace {k : ℕ} {B : C} (i : Fin (k + 2)) (g : Gen P (k + 1) B) : Gen P k B :=
  ⟨face i g.1, (toLast i g.1).1 ≫ g.2⟩

def dL (k : ℕ) : L P (k + 1) ⟶ L P k where
  app B := AddCommGrpCat.ofHom (FreeAbelianGroup.lift fun g => ∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) • FreeAbelianGroup.of (gFace P i g))
  naturality B B' φ := fa_ext fun g => by
    simp [L, gFace]

variable {P}

def tOf {K : Coef C} {k : ℕ} (f : Cn (elF P (zm K)) k) : L P k ⟶ K where
  app B := AddCommGrpCat.ofHom (FreeAbelianGroup.lift fun g => (K.map g.2).hom (f g.1))
  naturality B B' φ := fa_ext fun g => by
    simp [L]

def cOf {K : Coef C} {k : ℕ} (u : L P k ⟶ K) : Cn (elF P (zm K)) k :=
  fun s => (u.app (s.obj (Fin.last k)).1).hom (FreeAbelianGroup.of ⟨s, 𝟙 _⟩)

theorem L_map_of {B B' : C} (φ : B ⟶ B') {k : ℕ} (g : Gen P k B) :
    ((L P k).map φ).hom (FreeAbelianGroup.of g) = FreeAbelianGroup.of (⟨g.1, g.2 ≫ φ⟩ : Gen P k B') :=
  FreeAbelianGroup.map_of_apply _

theorem dL_of {k : ℕ} {B : C} (g : Gen P (k + 1) B) :
    ((dL P k).app B).hom (FreeAbelianGroup.of g) =
      ∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) • (FreeAbelianGroup.of (gFace P i g) : (L P k).obj B) :=
  FreeAbelianGroup.lift_apply_of _ _

theorem tOf_of {K : Coef C} {k : ℕ} (f : Cn (elF P (zm K)) k) {B : C} (g : Gen P k B) :
    ((tOf f).app B).hom (FreeAbelianGroup.of g) = (K.map g.2).hom (f g.1) :=
  FreeAbelianGroup.lift_apply_of _ _

theorem cOf_tOf {K : Coef C} {k : ℕ} (f : Cn (elF P (zm K)) k) : cOf (tOf f) = f := by
  funext s
  refine (tOf_of f _).trans ?_
  simp only [K.map_id]
  rfl

theorem u_of {K : Coef C} {k : ℕ} (u : L P k ⟶ K) {B : C} (g : Gen P k B) :
    (u.app B).hom (FreeAbelianGroup.of g) = (K.map g.2).hom (cOf u g.1) := by
  obtain ⟨s, a⟩ := g
  have h2 : ((L P k).map a).hom (FreeAbelianGroup.of (⟨s, 𝟙 _⟩ : Gen P k _)) = FreeAbelianGroup.of (⟨s, a⟩ : Gen P k B) := by
    rw [L_map_of]; simp
  have h3 := congrArg (fun f => f.hom (FreeAbelianGroup.of (⟨s, 𝟙 _⟩ : Gen P k _))) (u.naturality a)
  refine Eq.trans ?_ h3
  exact (congrArg (u.app B).hom h2).symm

theorem tOf_cOf {K : Coef C} {k : ℕ} (u : L P k ⟶ K) : tOf (cOf u) = u := by
  ext B : 2
  exact fa_ext fun g => (tOf_of _ g).trans (u_of u g).symm

theorem d_apply' {K : Coef C} {k : ℕ} (f : Cn (elF P (zm K)) k) (s : ComposableArrows P.Elements (k + 1)) :
    d (elF P (zm K)) k f s = ∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) • (K.map (toLast i s).1).hom (f (face i s)) := rfl

theorem d_cOf {K : Coef C} {k : ℕ} (u : L P k ⟶ K) : d (elF P (zm K)) k (cOf u) = cOf (dL P k ≫ u) := by
  funext s
  rw [d_apply']
  change _ = (u.app _).hom (((dL P k).app _).hom (FreeAbelianGroup.of (⟨s, 𝟙 _⟩ : Gen P (k + 1) _)))
  rw [dL_of, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, u_of]
  simp [gFace]

theorem tOf_d {K : Coef C} {k : ℕ} (f : Cn (elF P (zm K)) k) : tOf (d (elF P (zm K)) k f) = dL P k ≫ tOf f := by
  ext B : 2
  refine fa_ext fun g => (tOf_of _ g).trans ?_
  change _ = ((tOf f).app B).hom (((dL P k).app B).hom (FreeAbelianGroup.of g))
  rw [d_apply', dL_of, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, map_zsmul, tOf_of]
  simp [gFace]

theorem tOf_zero {K : Coef C} {k : ℕ} : tOf (0 : Cn (elF P (zm K)) k) = 0 := by
  ext B : 2
  refine fa_ext fun g => (tOf_of _ g).trans ?_
  exact map_zero _

theorem dL_dL (k : ℕ) : dL P (k + 1) ≫ dL P k = 0 := by
  have h := tOf_d (d (elF P (zm (L P k))) k (cOf (𝟙 _)))
  rw [CrystallineSemistableComparison.CH.d_d, tOf_zero, tOf_d, tOf_cOf, Category.comp_id] at h
  exact h.symm

theorem vanish_of_exact (hex : ∀ k, (ShortComplex.mk (dL P (k + 1)) (dL P k) (dL_dL k)).Exact)
    (K : Coef C) (hK : Injective K) (j : ℕ) : Subsingleton (TH P K (j + 1)) := by
  refine ⟨fun x y => ?_⟩
  suffices h : ∀ x : TH P K (j + 1), x = 0 by rw [h x, h y]
  intro x
  obtain ⟨f, hf, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (cx (elF P (zm K))) (j + 1)).1 x
  rw [(CrystallineSemistableComparison.P.cls_surj (cx (elF P (zm K))) (j + 1)).2.1]
  have h0 : dL P (j + 1) ≫ tOf f = 0 := by
    rw [← tOf_d]
    exact (congrArg tOf hf).trans tOf_zero
  refine ⟨cOf ((hex j).descToInjective (tOf f) h0), ?_⟩
  refine (d_cOf _).trans ?_
  have := (hex j).comp_descToInjective (tOf f) h0
  simp only at this
  rw [this, cOf_tOf]

end UpperTheory.Ru.crystallineComparison.Th
