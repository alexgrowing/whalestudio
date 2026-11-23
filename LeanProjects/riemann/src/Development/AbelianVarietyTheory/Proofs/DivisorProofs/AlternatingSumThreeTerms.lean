import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.CechOne

theorem spec_comp {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T) (h : R →+* T)
    (e : g.comp f = h) : Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom f) = Spec.map (CommRingCat.ofHom h) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, e]

variable (A B : Type) [CommRing A] [CommRing B] [Algebra A B]

abbrev fB : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of A) := Spec.map (CommRingCat.ofHom (algebraMap A B))

def P0 : Sx (cech (fB A B)) 0 (Spec (CommRingCat.of B)) :=
  cechPt (fB A B) 0 (fB A B) (fun _ => 𝟙 _) (fun _ => Category.id_comp _)

def y1 : Fin (1 + 1) → (Spec (CommRingCat.of (B ⊗[A] B)) ⟶ Spec (CommRingCat.of B)) :=
  ![Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B).toRingHom),
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B).toRingHom)]

theorem hy1 : ∀ i, y1 A B i ≫ fB A B = Spec.map (CommRingCat.ofHom (algebraMap A (B ⊗[A] B))) := by
  intro i
  fin_cases i <;> exact spec_comp _ _ _ (by rw [AlgHom.toRingHom_eq_coe]; exact AlgHom.comp_algebraMap _)

def P1 : Sx (cech (fB A B)) 1 (Spec (CommRingCat.of (B ⊗[A] B))) :=
  cechPt (fB A B) 1 (Spec.map (CommRingCat.ofHom (algebraMap A (B ⊗[A] B)))) (y1 A B) (hy1 A B)

def y2 : Fin (2 + 1) → (Spec (CommRingCat.of (B ⊗[A] (B ⊗[A] B))) ⟶ Spec (CommRingCat.of B)) :=
    ![Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] (B ⊗[A] B)).toRingHom),
      Spec.map (CommRingCat.ofHom ((Algebra.TensorProduct.includeRight : B ⊗[A] B →ₐ[A] B ⊗[A] (B ⊗[A] B)).comp
        (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B)).toRingHom),
      Spec.map (CommRingCat.ofHom ((Algebra.TensorProduct.includeRight : B ⊗[A] B →ₐ[A] B ⊗[A] (B ⊗[A] B)).comp
        (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B)).toRingHom)]

theorem hy2 : ∀ i, y2 A B i ≫ fB A B = Spec.map (CommRingCat.ofHom (algebraMap A (B ⊗[A] (B ⊗[A] B)))) := by
  intro i
  fin_cases i <;> exact spec_comp _ _ _ (by rw [AlgHom.toRingHom_eq_coe]; exact AlgHom.comp_algebraMap _)

def P2 : Sx (cech (fB A B)) 2 (Spec (CommRingCat.of (B ⊗[A] (B ⊗[A] B)))) :=
  cechPt (fB A B) 2 (Spec.map (CommRingCat.ofHom (algebraMap A (B ⊗[A] (B ⊗[A] B))))) (y2 A B) (hy2 A B)

variable {A B} in
theorem spec_algHom {B' : Type} [CommRing B'] [Algebra A B'] (φ : B →ₐ[A] B') :
    Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ fB A B = fB A B' :=
  spec_comp _ _ _ (by rw [AlgHom.toRingHom_eq_coe]; exact AlgHom.comp_algebraMap _)

def cechMap {Y Y' X : Scheme.{0}} (f : Y ⟶ X) (f' : Y' ⟶ X) (g : Y' ⟶ Y) (hg : g ≫ f = f') : cech f' ⟶ cech f :=
  Arrow.mapCechNerve (Arrow.homMk (yoneda.map g) (𝟙 _) (by simp [← hg]))

theorem freePresheaf_map_freeMk (R : Type) [CommRing R] {P Q : PSh} (α : P ⟶ Q) (U : Scheme.{0}) (x : P.obj (op U)) :
    (((freeP R).map α).app (op U)).hom (ModuleCat.freeMk (ULift.up x)) = ModuleCat.freeMk (ULift.up (α.app (op U) x)) :=
  ModuleCat.free_map_apply _ _

theorem freePresheaf_obj_map_freeMk (R : Type) [CommRing R] (P : PSh) {U V : Scheme.{0}} (g : V ⟶ U) (x : P.obj (op U)) :
    (((freeP R).obj P).map g.op).hom (ModuleCat.freeMk (ULift.up x)) = ModuleCat.freeMk (ULift.up (P.map g.op x)) :=
  ModuleCat.free_map_apply _ _

theorem val_map (R : Type) [CommRing R] {P Q : PSh} {F : Shv R} (α : P ⟶ Q) (s : (free R).obj Q ⟶ F) (U : Scheme.{0})
    (x : P.obj (op U)) : val ((free R).map α ≫ s) U x = val s U (α.app (op U) x) := by
  unfold val freeGen
  have h : ((toSheafify Scheme.etaleTopology ((freeP R).obj Q)).app (op U)).hom
      ((((freeP R).map α).app (op U)).hom (ModuleCat.freeMk (ULift.up x))) =
      ((sheafifyMap Scheme.etaleTopology ((freeP R).map α)).app (op U)).hom
        (((toSheafify Scheme.etaleTopology ((freeP R).obj P)).app (op U)).hom (ModuleCat.freeMk (ULift.up x))) :=
    congrArg (fun η => (η.app (op U)).hom (ModuleCat.freeMk (ULift.up x)))
      (toSheafify_naturality Scheme.etaleTopology ((freeP R).map α))
  rw [freePresheaf_map_freeMk] at h
  erw [h]
  rfl

theorem val_nat (R : Type) [CommRing R] {P : PSh} {F : Shv R} (s : (free R).obj P ⟶ F) {U V : Scheme.{0}} (g : V ⟶ U)
    (x : P.obj (op U)) : val s V (P.map g.op x) = Sec.pull g (val s U x) := by
  unfold val freeGen Sec.pull
  have h1 : ((toSheafify Scheme.etaleTopology ((freeP R).obj P)).app (op V)).hom
      ((((freeP R).obj P).map g.op).hom (ModuleCat.freeMk (ULift.up x))) =
      ((sheafify Scheme.etaleTopology ((freeP R).obj P)).map g.op).hom
        (((toSheafify Scheme.etaleTopology ((freeP R).obj P)).app (op U)).hom (ModuleCat.freeMk (ULift.up x))) :=
    congrArg (fun φ => φ.hom (ModuleCat.freeMk (ULift.up x)))
      ((toSheafify Scheme.etaleTopology ((freeP R).obj P)).naturality g.op)
  rw [freePresheaf_obj_map_freeMk] at h1
  erw [h1]
  exact congrArg (fun φ => φ.hom (((toSheafify Scheme.etaleTopology ((freeP R).obj P)).app (op U)).hom
    (ModuleCat.freeMk (ULift.up x)))) (s.hom.naturality g.op)

theorem map_cechPt {Y X Y' X' : Scheme.{0}} (f : Y ⟶ X) (f' : Y' ⟶ X') (k k' : ℕ) {Z : Scheme.{0}} (x : Z ⟶ X)
    (y : Fin (k + 1) → (Z ⟶ Y)) (h : ∀ i, y i ≫ f = x) (x' : Z ⟶ X') (y' : Fin (k' + 1) → (Z ⟶ Y')) (h' : ∀ i, y' i ≫ f' = x')
    (M : (cech f).obj (op ⦋k⦌) ⟶ (cech f').obj (op ⦋k'⦌))
    (hM : WidePullback.lift (arrows := fun _ : Fin (k + 1) => yoneda.map f) (yoneda.map x) (fun i => yoneda.map (y i))
        (fun i => by rw [← yoneda.map_comp, h i]) ≫ M =
      WidePullback.lift (arrows := fun _ : Fin (k' + 1) => yoneda.map f') (yoneda.map x') (fun i => yoneda.map (y' i))
        (fun i => by rw [← yoneda.map_comp, h' i])) :
    M.app (op Z) (cechPt f k x y h) = cechPt f' k' x' y' h' := by
  unfold cechPt
  rw [← hM]
  rfl

theorem cechPt_nat {Y X : Scheme.{0}} (f : Y ⟶ X) (k : ℕ) {Z Z' : Scheme.{0}} (g : Z' ⟶ Z) (x : Z ⟶ X)
    (y : Fin (k + 1) → (Z ⟶ Y)) (h : ∀ i, y i ≫ f = x) :
    ((cech f).obj (op ⦋k⦌)).map g.op (cechPt f k x y h) =
      cechPt f k (g ≫ x) (fun i => g ≫ y i) (fun i => by rw [Category.assoc, h i]) := by
  unfold cechPt
  have e : yoneda.map g ≫ WidePullback.lift (arrows := fun _ : Fin (k + 1) => yoneda.map f) (yoneda.map x)
      (fun i => yoneda.map (y i)) (fun i => by rw [← yoneda.map_comp, h i]) =
      WidePullback.lift (arrows := fun _ : Fin (k + 1) => yoneda.map f) (yoneda.map (g ≫ x))
      (fun i => yoneda.map (g ≫ y i)) (fun i => by rw [← yoneda.map_comp, Category.assoc, h i]) := by
    apply WidePullback.hom_ext
    · intro j
      erw [Category.assoc, WidePullback.lift_π, WidePullback.lift_π, yoneda.map_comp]
    · erw [Category.assoc, WidePullback.lift_base, WidePullback.lift_base, yoneda.map_comp]
  rw [← e]
  erw [← FunctorToTypes.naturality]
  simp
  rfl

theorem cechPt_face {Y X : Scheme.{0}} (f : Y ⟶ X) (k : ℕ) {Z : Scheme.{0}} (x : Z ⟶ X)
    (y : Fin (k + 2) → (Z ⟶ Y)) (h : ∀ i, y i ≫ f = x) (i : Fin (k + 2)) :
    ((cech f).δ i).app (op Z) (cechPt f (k + 1) x y h) = cechPt f k x (fun j => y (i.succAbove j)) (fun j => h _) := by
  apply map_cechPt
  apply WidePullback.hom_ext
  · intro j
    simp only [cech, SimplicialObject.δ, Arrow.cechNerve]
    erw [Category.assoc, WidePullback.lift_π, WidePullback.lift_π, WidePullback.lift_π]
    rfl
  · simp only [cech, SimplicialObject.δ, Arrow.cechNerve]
    erw [Category.assoc, WidePullback.lift_base, WidePullback.lift_base, WidePullback.lift_base]

theorem cechPt_congr {Y X : Scheme.{0}} (f : Y ⟶ X) (k : ℕ) {Z : Scheme.{0}} {x x' : Z ⟶ X}
    {y y' : Fin (k + 1) → (Z ⟶ Y)} (h : ∀ i, y i ≫ f = x) (h' : ∀ i, y' i ≫ f = x') (ex : x = x') (ey : y = y') :
    cechPt f k x y h = cechPt f k x' y' h' := by
  subst ex
  subst ey
  rfl

theorem val_add (R : Type) [CommRing R] {P : PSh} {F : Shv R} (s s' : (free R).obj P ⟶ F) (U : Scheme.{0}) (x : P.obj (op U)) :
    val (s + s') U x = val s U x + val s' U x := by
  simp [val]

theorem val_zero (R : Type) [CommRing R] {P : PSh} {F : Shv R} (U : Scheme.{0}) (x : P.obj (op U)) :
    val (0 : (free R).obj P ⟶ F) U x = 0 := by
  simp [val]

def valHom (R : Type) [CommRing R] {P : PSh} (F : Shv R) (U : Scheme.{0}) (x : P.obj (op U)) :
    ((free R).obj P ⟶ F) →+ Sec F U where
  toFun s := val s U x
  map_zero' := val_zero R U x
  map_add' s s' := val_add R s s' U x

theorem alternating_sum_two_terms {M : Type*} [AddCommGroup M] (p q : M) : (-1 : ℤ) ^ (0 : ℕ) • p + (-1 : ℤ) ^ (1 : ℕ) • q = p - q := by
  simp [sub_eq_add_neg]

theorem alternating_sum_three_terms {M : Type*} [AddCommGroup M] (p q r : M) :
    (-1 : ℤ) ^ (0 : ℕ) • p + (-1 : ℤ) ^ (1 : ℕ) • q + (-1 : ℤ) ^ (2 : ℕ) • r = p - q + r := by
  simp [sub_eq_add_neg]

theorem val_coboundary_first_level (R : Type) [CommRing R] (F : Shv R) (t : (free R).obj ((cech (fB A B)).obj (op ⦋0⦌)) ⟶ F) :
    val (cobd t) (Spec (CommRingCat.of (B ⊗[A] B))) (P1 A B) =
      ((onRings F).map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B).toRingHom)).hom
        (val t (Spec (CommRingCat.of B)) (P0 A B)) -
      ((onRings F).map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B).toRingHom)).hom
        (val t (Spec (CommRingCat.of B)) (P0 A B)) := by
  have e : ∀ i : Fin 2, ((cech (fB A B)).δ i).app (op (Spec (CommRingCat.of (B ⊗[A] B)))) (P1 A B) =
      ((cech (fB A B)).obj (op ⦋0⦌)).map (y1 A B (i.succAbove 0)).op (P0 A B) := by
    intro i
    unfold P1 P0
    refine (cechPt_face (fB A B) 0 _ (y1 A B) (hy1 A B) i).trans ?_
    refine Eq.trans ?_ (cechPt_nat (fB A B) 0 (y1 A B (i.succAbove 0)) (fB A B) (fun _ => 𝟙 _) (fun _ => Category.id_comp _)).symm
    apply cechPt_congr
    · exact (hy1 A B _).symm
    · funext j
      fin_cases j
      simp
  change valHom R F _ (P1 A B) (cobd t) = _
  unfold cobd
  rw [map_sum, Fin.sum_univ_two]
  simp only [map_zsmul]
  simp only [valHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [val_map, val_map, e, e, val_nat, val_nat]
  exact (alternating_sum_two_terms _ _).trans rfl

def g2 : Fin 3 → (Spec (CommRingCat.of (B ⊗[A] (B ⊗[A] B))) ⟶ Spec (CommRingCat.of (B ⊗[A] B))) :=
  ![Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : B ⊗[A] B →ₐ[A] B ⊗[A] (B ⊗[A] B)).toRingHom),
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id A B)
      (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B)).toRingHom),
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id A B)
      (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B)).toRingHom)]

theorem val_coboundary_second_level (R : Type) [CommRing R] (F : Shv R) (s : (free R).obj ((cech (fB A B)).obj (op ⦋1⦌)) ⟶ F) :
    val (cobd s) (Spec (CommRingCat.of (B ⊗[A] (B ⊗[A] B)))) (P2 A B) =
      ((onRings F).map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : B ⊗[A] B →ₐ[A] B ⊗[A] (B ⊗[A] B)).toRingHom)).hom (val s (Spec (CommRingCat.of (B ⊗[A] B))) (P1 A B)) -
      ((onRings F).map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id A B)
        (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B)).toRingHom)).hom (val s (Spec (CommRingCat.of (B ⊗[A] B))) (P1 A B)) +
      ((onRings F).map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id A B)
        (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B)).toRingHom)).hom (val s (Spec (CommRingCat.of (B ⊗[A] B))) (P1 A B)) := by
  have e : ∀ i : Fin 3, ((cech (fB A B)).δ i).app (op (Spec (CommRingCat.of (B ⊗[A] (B ⊗[A] B))))) (P2 A B) =
      ((cech (fB A B)).obj (op ⦋1⦌)).map (g2 A B i).op (P1 A B) := by
    intro i
    unfold P2 P1
    refine (cechPt_face (fB A B) 1 _ (y2 A B) (hy2 A B) i).trans ?_
    refine Eq.trans ?_ (cechPt_nat (fB A B) 1 (g2 A B i) _ (y1 A B) (hy1 A B)).symm
    apply cechPt_congr
    · fin_cases i <;>
      · simp only [g2]
        exact (spec_comp _ _ _ (by rw [AlgHom.toRingHom_eq_coe]; exact AlgHom.comp_algebraMap _)).symm
    · funext j
      fin_cases i <;> fin_cases j <;>
      · simp only [y1, y2, g2]
        refine (spec_comp _ _ _ ?_).symm
        ext b
        simp [Algebra.TensorProduct.one_def]
  change valHom R F _ (P2 A B) (cobd s) = _
  unfold cobd
  rw [map_sum, Fin.sum_univ_three]
  simp only [map_zsmul]
  simp only [valHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [val_map, val_map, val_map, e, e, e, val_nat, val_nat, val_nat]
  exact (alternating_sum_three_terms _ _ _).trans rfl

theorem val_cech_map_first_level (R : Type) [CommRing R] (F : Shv R) {B' : Type} [CommRing B'] [Algebra A B'] (φ : B →ₐ[A] B')
    (s : (free R).obj ((cech (fB A B)).obj (op ⦋1⦌)) ⟶ F) :
    val ((free R).map ((cechMap (fB A B) (fB A B') _ (spec_algHom φ)).app (op ⦋1⦌)) ≫ s)
        (Spec (CommRingCat.of (B' ⊗[A] B'))) (P1 A B') =
      ((onRings F).map (CommRingCat.ofHom (Algebra.TensorProduct.map φ φ).toRingHom)).hom
        (val s (Spec (CommRingCat.of (B ⊗[A] B))) (P1 A B)) := by
  rw [val_map]
  have e1 : ((cechMap (fB A B) (fB A B') _ (spec_algHom φ)).app (op ⦋1⦌)).app (op (Spec (CommRingCat.of (B' ⊗[A] B'))))
      (P1 A B') = cechPt (fB A B) 1 (Spec.map (CommRingCat.ofHom (algebraMap A (B' ⊗[A] B'))))
        (fun j => y1 A B' j ≫ Spec.map (CommRingCat.ofHom φ.toRingHom))
        (fun j => by rw [Category.assoc, spec_algHom φ, hy1 A B' j]) := by
    unfold P1
    apply map_cechPt
    apply WidePullback.hom_ext
    · intro j
      simp only [cechMap, Arrow.mapCechNerve]
      erw [Category.assoc, WidePullback.lift_π, WidePullback.lift_π_assoc, WidePullback.lift_π, yoneda.map_comp]
      rfl
    · simp only [cechMap, Arrow.mapCechNerve]
      erw [Category.assoc, WidePullback.lift_base, WidePullback.lift_base_assoc, WidePullback.lift_base]
      simp
  have e2 : cechPt (fB A B) 1 (Spec.map (CommRingCat.ofHom (algebraMap A (B' ⊗[A] B'))))
        (fun j => y1 A B' j ≫ Spec.map (CommRingCat.ofHom φ.toRingHom))
        (fun j => by rw [Category.assoc, spec_algHom φ, hy1 A B' j]) =
      ((cech (fB A B)).obj (op ⦋1⦌)).map (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map φ φ).toRingHom)).op
        (P1 A B) := by
    unfold P1
    refine Eq.trans ?_ (cechPt_nat (fB A B) 1 _ _ (y1 A B) (hy1 A B)).symm
    apply cechPt_congr
    · exact (spec_comp (algebraMap A (B ⊗[A] B)) (Algebra.TensorProduct.map φ φ).toRingHom (algebraMap A (B' ⊗[A] B'))
        (by rw [AlgHom.toRingHom_eq_coe]; exact AlgHom.comp_algebraMap _)).symm
    · funext j
      fin_cases j <;>
      · refine (spec_comp _ _ _ rfl).trans (spec_comp _ _ _ ?_).symm
        ext b
        simp
  rw [e1, e2, val_nat]
  rfl

theorem cechMap_aug {Y Y' X : Scheme.{0}} (f : Y ⟶ X) (f' : Y' ⟶ X) (g : Y' ⟶ Y) (hg : g ≫ f = f') :
    cechMap f f' g hg ≫ cechAug f = cechAug f' := by
  ext n : 1
  exact (WidePullback.lift_base _ _ _ _).trans (by first | rfl | simp [cechAug, Arrow.augmentedCechNerve])

theorem smooth_surj [Algebra.Etale A B] [Module.FaithfullyFlat A B] : Smooth (fB A B) ∧ Surjective (fB A B) := by
  have he : Etale (fB A B) := by
    rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    first
    | exact RingHom.etale_algebraMap.2 inferInstance
    | exact (RingHom.etale_algebraMap_iff).2 inferInstance
    | exact inferInstance
  refine ⟨inferInstance, ?_⟩
  have := (flat_and_surjective_SpecMap_iff (CommRingCat.ofHom (algebraMap A B))).2 ?_
  · exact this.2
  · first
    | exact RingHom.faithfullyFlat_algebraMap_iff.2 inferInstance
    | exact inferInstance

end GlobalTheory.CechOne
