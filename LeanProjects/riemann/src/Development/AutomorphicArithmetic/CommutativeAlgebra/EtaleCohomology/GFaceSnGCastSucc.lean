import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.VanishOfExact
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.FaceSnocCastSucc

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.CH
open GlobalTheory.CatH (face toLast)

namespace UpperTheory.Ru.crystallineComparison.Th

variable {C : Type 1} [Category.{0} C]

theorem exact_of_app (S : ShortComplex (Coef C))
    (h : ∀ B, Function.Exact (S.f.app B).hom (S.g.app B).hom) : S.Exact := by
  rw [ShortComplex.exact_iff_isZero_homology]
  refine CategoryTheory.Functor.isZero _ fun B => ?_
  have h1 : (S.map ((evaluation C AddCommGrpCat.{1}).obj B)).Exact :=
    (ShortComplex.ab_exact_iff_function_exact _).2 (h B)
  rw [ShortComplex.exact_iff_isZero_homology] at h1
  exact h1.of_iso (S.mapHomologyIso ((evaluation C AddCommGrpCat.{1}).obj B)).symm

variable {P : C ⥤ Type}

def snG {m : ℕ} {B : C} (g : Gen P m B) (z : P.obj B) (h : (P.map g.2) (g.1.obj (Fin.last m)).2 = z) : Gen P (m + 1) B :=
  ⟨snoc g.1 (X := (⟨B, z⟩ : P.Elements)) ⟨g.2, h⟩, (snε g.1 (X := (⟨B, z⟩ : P.Elements)) ⟨g.2, h⟩).1⟩

theorem snG_eq {m : ℕ} {B : C} (g : Gen P m B) {z : P.obj B} (h : (P.map g.2) (g.1.obj (Fin.last m)).2 = z) :
    snG g z h = snG g _ rfl := by
  subst h; rfl

def sn {m : ℕ} {B : C} (g : Gen P m B) : Gen P (m + 1) B := snG g _ rfl

theorem gFace_snG_last {m : ℕ} {B : C} (g : Gen P m B) (z : P.obj B) (h : (P.map g.2) (g.1.obj (Fin.last m)).2 = z) :
    gFace P (Fin.last (m + 1)) (snG g z h) = g :=
  congrArg (fun p : (Σ t : ComposableArrows P.Elements m, t.obj (Fin.last m) ⟶ (⟨B, z⟩ : P.Elements)) =>
    (⟨p.1, p.2.1⟩ : Gen P m B)) (gen_snoc_last g.1 (X := (⟨B, z⟩ : P.Elements)) ⟨g.2, h⟩)

theorem gFace_snG_castSucc {m : ℕ} {B : C} (g : Gen P (m + 1) B) (z : P.obj B) (h : (P.map g.2) (g.1.obj (Fin.last (m + 1))).2 = z)
    (i : Fin (m + 2)) (h' : (P.map (gFace P i g).2) ((gFace P i g).1.obj (Fin.last m)).2 = z) :
    gFace P i.castSucc (snG g z h) = snG (gFace P i g) z h' :=
  congrArg (fun p : (Σ t : ComposableArrows P.Elements (m + 1), t.obj (Fin.last (m + 1)) ⟶ (⟨B, z⟩ : P.Elements)) =>
    (⟨p.1, p.2.1⟩ : Gen P (m + 1) B)) (gen_snoc_castSucc g.1 (X := (⟨B, z⟩ : P.Elements)) ⟨g.2, h⟩ i)

theorem gFace_sn_last {m : ℕ} {B : C} (g : Gen P m B) : gFace P (Fin.last (m + 1)) (sn g) = g := gFace_snG_last g _ rfl

theorem gFace_sn_castSucc {m : ℕ} {B : C} (g : Gen P (m + 1) B) (i : Fin (m + 2)) :
    gFace P i.castSucc (sn g) = sn (gFace P i g) := by
  have h' : (P.map (gFace P i g).2) ((gFace P i g).1.obj (Fin.last m)).2 = (P.map g.2) (g.1.obj (Fin.last (m + 1))).2 := by
    have e := (toLast i g.1).2
    change (P.map ((toLast i g.1).1 ≫ g.2)) _ = _
    rw [P.map_comp]
    exact congrArg (P.map g.2) e
  exact (gFace_snG_castSucc g _ rfl i h').trans (snG_eq _ h')

def hh (B : C) (m : ℕ) : (L P m).obj B →+ (L P (m + 1)).obj B := (FreeAbelianGroup.map sn : FreeAbelianGroup (Gen P m B) →+ _)

theorem hh_of (B : C) (m : ℕ) (g : Gen P m B) : hh B m (FreeAbelianGroup.of g) = FreeAbelianGroup.of (sn g) :=
  FreeAbelianGroup.map_of_apply _

def ofL {k : ℕ} {B : C} (g : Gen P k B) : (L P k).obj B := FreeAbelianGroup.of g

theorem d_hh_of (B : C) (k : ℕ) (g : Gen P (k + 1) B) :
    ((dL P (k + 1)).app B).hom (hh B (k + 1) (ofL g)) = hh B k (((dL P k).app B).hom (ofL g)) + (-1 : ℤ) ^ (k + 2) • ofL g := by
  unfold ofL
  rw [hh_of, dL_of, dL_of, Fin.sum_univ_castSucc, map_sum]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_zsmul, hh_of, gFace_sn_castSucc]
    rfl
  · rw [gFace_sn_last]
    rfl

theorem d_hh (B : C) (k : ℕ) (y : (L P (k + 1)).obj B) :
    ((dL P (k + 1)).app B).hom (hh B (k + 1) y) = hh B k (((dL P k).app B).hom y) + (-1 : ℤ) ^ (k + 2) • y := by
  have key : AddCommGrpCat.ofHom (((dL P (k + 1)).app B).hom.comp (hh B (k + 1))) =
      AddCommGrpCat.ofHom ((hh B k).comp ((dL P k).app B).hom + (-1 : ℤ) ^ (k + 2) • AddMonoidHom.id ((L P (k + 1)).obj B)) := by
    exact fa_ext fun g => d_hh_of B k g
  exact congrArg (fun f => f.hom y) key

theorem exact_dL (k : ℕ) : (ShortComplex.mk (dL P (k + 1)) (dL P k) (dL_dL k)).Exact := by
  refine exact_of_app _ fun B y => ⟨fun hy => ?_, ?_⟩
  · refine ⟨(-1 : ℤ) ^ (k + 2) • hh B (k + 1) y, ?_⟩
    have e := d_hh B k y
    have hy' : ((dL P k).app B).hom y = 0 := hy
    rw [hy', map_zero, zero_add] at e
    change ((dL P (k + 1)).app B).hom _ = y
    rw [map_zsmul, e, smul_smul, ← mul_pow]
    simp
  · rintro ⟨x, rfl⟩
    exact congrArg (fun f => f.hom x) (congrArg (fun f => f.app B) (dL_dL (P := P) k))

theorem vanish (P : C ⥤ Type) (K : Coef C) (hK : Injective K) (j : ℕ) : Subsingleton (TH P K (j + 1)) :=
  vanish_of_exact exact_dL K hK j

end UpperTheory.Ru.crystallineComparison.Th
