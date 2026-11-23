import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.EigLatBasis
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR epsScaleR IsTangent IsLieComb IsLieBasis OAct epsPt
  IsLieEigen LieMult)
open ReciprocityTheory.ChartRestriction.G.Chart (dualMapR)
open TrivSqZeroExt (inl inr)

namespace GlobalTheory.Diag

section Act

variable (S : Scheme.{0}) (O : Type) [CommRing O] (X : Type) [AddCommGroup X] [Module O X]

def diagAct : OAct O (splitTorus S X) where
  act a := diagMap S (DistribSMul.toAddMonoidHom X a)
  hom _ := inferInstance
  one := by
    rw [← diagMap_id]; congr 1; ext x; simp
  mul a b := by
    rw [← diagMap_comp]; congr 1; ext x; simp [mul_smul]
  add a b := by
    rw [← diagMap_add]; congr 1; ext x; simp [add_smul]

theorem diagAct_act (a : O) :
    (diagAct S O X).act a = diagMap S (DistribSMul.toAddMonoidHom X a) := rfl

end Act

section Val

variable {S : Scheme.{0}} {A : Type} [CommRing A] {g : Sp A ⟶ S}
  {X Y : Type} [AddCommGroup X] [AddCommGroup Y]

def charVal (w : Over.mk g ⟶ splitTorus S X) (x : X) : A :=
  (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom (w.left.appTop.hom (chi X x))

theorem charVal_eq_coord (w : Over.mk g ⟶ splitTorus S X) (x : X) :
    charVal w x = (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom
      ((coord w).hom (AddMonoidAlgebra.single x 1)) := by
  simp [charVal, chi, coord]
  rfl

theorem charVal_ext {v w : Over.mk g ⟶ splitTorus S X} (h : ∀ x, charVal v x = charVal w x) :
    v = w := by
  refine hom_ext fun x => ?_
  have e := congrArg (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom (h x)
  simpa [charVal_eq_coord] using e

theorem charVal_one (x : X) : charVal (1 : Over.mk g ⟶ splitTorus S X) x = 1 := by
  rw [charVal_eq_coord, coord_one, map_one]

theorem charVal_mul (v w : Over.mk g ⟶ splitTorus S X) (x : X) :
    charVal (v * w) x = charVal v x * charVal w x := by
  rw [charVal_eq_coord, charVal_eq_coord, charVal_eq_coord, coord_mul, map_mul]

theorem charVal_zero (w : Over.mk g ⟶ splitTorus S X) : charVal w 0 = 1 := by
  rw [charVal_eq_coord, coord_single_zero, map_one]

theorem charVal_add (w : Over.mk g ⟶ splitTorus S X) (x y : X) :
    charVal w (x + y) = charVal w x * charVal w y := by
  rw [charVal_eq_coord, charVal_eq_coord, charVal_eq_coord, coord_single_add, map_mul]

theorem charVal_comp_diagMap (w : Over.mk g ⟶ splitTorus S X) (u : Y →+ X) (y : Y) :
    charVal (w ≫ diagMap S u) y = charVal w (u y) := by
  rw [charVal_eq_coord, charVal_eq_coord, coord_comp_diagMap_single]

theorem charVal_eq_torusFst (w : Over.mk g ⟶ splitTorus S X) (x : X) :
    charVal w x = (Spec.preimage (w.left ≫ torusFst S X)).hom (AddMonoidAlgebra.single x 1) := by
  obtain ⟨φ, hφ⟩ : ∃ φ, Spec.map φ = w.left ≫ torusFst S X := ⟨_, Spec.map_preimage _⟩
  rw [charVal_eq_coord]
  unfold coord
  rw [← hφ, Spec.preimage_map]
  have e := congrArg (fun k => k.hom ((Scheme.ΓSpecIso (torusRing ZU X)).inv.hom (AddMonoidAlgebra.single x 1)))
    (Scheme.ΓSpecIso_naturality φ)
  refine e.trans ?_
  simp

theorem torusFst_eq_iff {S' : Scheme.{0}} {A' : Type} [CommRing A'] {g' : Sp A' ⟶ S'} (φ : A →+* A')
    (w' : Over.mk g' ⟶ splitTorus S' X) (w : Over.mk g ⟶ splitTorus S X) :
    w'.left ≫ torusFst S' X = spMap φ ≫ w.left ≫ torusFst S X ↔
      ∀ x, charVal w' x = φ (charVal w x) := by
  obtain ⟨φ1, h1⟩ : ∃ φ1, Spec.map φ1 = w'.left ≫ torusFst S' X := ⟨_, Spec.map_preimage _⟩
  obtain ⟨φ2, h2⟩ : ∃ φ2, Spec.map φ2 = w.left ≫ torusFst S X := ⟨_, Spec.map_preimage _⟩
  simp only [charVal_eq_torusFst, ← h1, ← h2, Spec.preimage_map, spMap, ← Spec.map_comp]
  rw [Spec.map_inj]
  constructor
  · intro h x
    rw [h]
    rfl
  · intro h
    ext1
    apply AddMonoidAlgebra.ringHom_ext
    · intro b
      have := RingHom.congr_fun (RingHom.ext_int
        ((φ1.hom.comp AddMonoidAlgebra.singleZeroRingHom).comp (ULift.ringEquiv : ULift ℤ ≃+* ℤ).symm.toRingHom)
        (((φ2 ≫ CommRingCat.ofHom φ).hom.comp AddMonoidAlgebra.singleZeroRingHom).comp
          (ULift.ringEquiv : ULift ℤ ≃+* ℤ).symm.toRingHom)) b.down
      exact this
    · intro x
      simpa using h x

theorem left_eq_iff {A' : Type} [CommRing A'] {g' : Sp A' ⟶ S} (φ : A →+* A') (hg : g' = spMap φ ≫ g)
    (w' : Over.mk g' ⟶ splitTorus S X) (w : Over.mk g ⟶ splitTorus S X) :
    w'.left = spMap φ ≫ w.left ↔ ∀ x, charVal w' x = φ (charVal w x) := by
  rw [← torusFst_eq_iff φ w' w]
  constructor
  · intro h
    rw [h, Category.assoc]
  · intro h
    apply pullback.hom_ext
    · rw [← Category.assoc] at h
      exact h
    · have e1 := Over.w w'
      have e2 := Over.w w
      simp only [Over.mk_hom] at e1 e2
      change w'.left ≫ (splitTorus S X).hom = (spMap φ ≫ w.left) ≫ (splitTorus S X).hom
      rw [e1, Category.assoc, e2, hg]

variable (g) in

def ofVal (f : Multiplicative X →* A) : Over.mk g ⟶ splitTorus S X :=
  ofChar _ ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom.toMonoidHom.comp f)

theorem charVal_ofVal (f : Multiplicative X →* A) (x : X) :
    charVal (ofVal g f) x = f (Multiplicative.ofAdd x) := by
  rw [charVal_eq_coord, ofVal, coord_ofChar]
  simp

end Val

section Eps

variable {S : Scheme.{0}} {R : Type} [CommRing R] {g : Sp (DualNumber R) ⟶ S}
  {X Y : Type} [AddCommGroup X] [AddCommGroup Y]

variable (g) in

def epsVec (c : X →+ R) : Over.mk g ⟶ splitTorus S X :=
  ofVal g
    { toFun := fun x => 1 + inr (c x.toAdd)
      map_one' := by simp
      map_mul' := fun x y => by ext <;> simp [add_comm] }

theorem charVal_epsVec (c : X →+ R) (x : X) : charVal (epsVec g c) x = 1 + inr (c x) := by
  rw [epsVec, charVal_ofVal]
  rfl

theorem epsVec_injective : Function.Injective (epsVec g : (X →+ R) → _) := by
  intro c d h
  ext x
  have e := congrArg (fun w => (charVal w x).snd) h
  simpa [charVal_epsVec] using e

theorem epsVec_zero : epsVec g (0 : X →+ R) = 1 := by
  refine charVal_ext fun x => ?_
  simp [charVal_epsVec, charVal_one]

theorem epsVec_add (c d : X →+ R) : epsVec g (c + d) = epsVec g c * epsVec g d := by
  refine charVal_ext fun x => ?_
  rw [charVal_mul, charVal_epsVec, charVal_epsVec, charVal_epsVec]
  ext <;> simp [add_comm]

theorem epsVec_sum {n : ℕ} (c : Fin n → (X →+ R)) :
    epsVec g (∑ i, c i) = (List.ofFn fun i => epsVec g (c i)).prod := by
  induction n with
  | zero => simp [epsVec_zero]
  | succ n ih =>
    rw [Fin.sum_univ_succ, epsVec_add, List.ofFn_succ, List.prod_cons, ih]

theorem epsVec_comp_diagMap (c : X →+ R) (u : Y →+ X) :
    epsVec g c ≫ diagMap S u = epsVec g (c.comp u) := by
  refine charVal_ext fun y => ?_
  rw [charVal_comp_diagMap, charVal_epsVec, charVal_epsVec]
  rfl

def epsCoeff (w : Over.mk g ⟶ splitTorus S X) (hw : ∀ x, (charVal w x).fst = 1) : X →+ R where
  toFun x := (charVal w x).snd
  map_zero' := by rw [charVal_zero]; rfl
  map_add' x y := by rw [charVal_add]; simp [hw, add_comm]

theorem epsVec_epsCoeff (w : Over.mk g ⟶ splitTorus S X) (hw : ∀ x, (charVal w x).fst = 1) :
    epsVec g (epsCoeff w hw) = w := by
  refine charVal_ext fun x => ?_
  rw [charVal_epsVec]
  ext
  · simp [hw x]
  · simp [epsCoeff]

theorem exists_epsVec_iff (w : Over.mk g ⟶ splitTorus S X) :
    (∃ c, epsVec g c = w) ↔ ∀ x, (charVal w x).fst = 1 := by
  constructor
  · rintro ⟨c, rfl⟩ x
    simp [charVal_epsVec]
  · intro h
    exact ⟨epsCoeff w h, epsVec_epsCoeff w h⟩

theorem reduces_iff {t : Sp R ⟶ S} (ht : t = spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ g)
    (w : Over.mk g ⟶ splitTorus S X) :
    spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ w.left = (1 : Over.mk t ⟶ splitTorus S X).left ↔
      ∀ x, (charVal w x).fst = 1 := by
  rw [eq_comm, left_eq_iff _ ht]
  simp [charVal_one, eq_comm]

theorem left_eq_epsScaleR_iff (a : R) (hg : g = spMap (epsScaleR a) ≫ g) (c : X →+ R)
    (u : Over.mk g ⟶ splitTorus S X) :
    u.left = spMap (epsScaleR a) ≫ (epsVec g c).left ↔ u = epsVec g (a • c) := by
  rw [left_eq_iff _ hg]
  constructor
  · intro h
    refine charVal_ext fun x => ?_
    rw [h, charVal_epsVec, charVal_epsVec]
    ext <;> simp [epsScaleR, mul_comm]
  · rintro rfl x
    rw [charVal_epsVec, charVal_epsVec]
    ext <;> simp [epsScaleR, mul_comm]

theorem exists_prod_iff (hg : ∀ a : R, g = spMap (epsScaleR a) ≫ g) {n : ℕ} (a : Fin n → R)
    (c : Fin n → (X →+ R)) (w : Over.mk g ⟶ splitTorus S X) :
    (∃ u : Fin n → (Over.mk g ⟶ splitTorus S X),
      (∀ i, (u i).left = spMap (epsScaleR (a i)) ≫ (epsVec g (c i)).left) ∧ w = (List.ofFn u).prod) ↔
      w = epsVec g (∑ i, a i • c i) := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    have hu' : ∀ i, u i = epsVec g (a i • c i) := fun i =>
      (left_eq_epsScaleR_iff (a i) (hg (a i)) (c i) (u i)).1 (hu i)
    rw [epsVec_sum]
    exact congrArg (fun f => (List.ofFn f).prod) (funext hu')
  · rintro rfl
    exact ⟨fun i => epsVec g (a i • c i),
      fun i => (left_eq_epsScaleR_iff (a i) (hg (a i)) (c i) _).2 rfl, epsVec_sum _⟩

theorem epsScaleR_base (a : R) :
    spMap (algebraMap R (DualNumber R)) = spMap (epsScaleR a) ≫ spMap (algebraMap R (DualNumber R)) := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext r <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]

theorem fstHom_base :
    spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ spMap (algebraMap R (DualNumber R)) = 𝟙 _ := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  convert Spec.map_id (CommRingCat.of R)
  ext r
  simp

end Eps

section Lie

variable {R : Type} [CommRing R] {X Y : Type} [AddCommGroup X] [AddCommGroup Y]

def lieVec (c : X →+ R) : epsR R ⟶ splitTorus (Sp R) X := epsVec _ c

theorem charVal_lieVec (c : X →+ R) (x : X) : charVal (lieVec c) x = 1 + inr (c x) := charVal_epsVec c x

theorem isTangent_iff_charVal (w : epsR R ⟶ splitTorus (Sp R) X) :
    IsTangent w ↔ ∀ x, (charVal w x).fst = 1 := by
  unfold IsTangent
  convert reduces_iff (t := 𝟙 _) fstHom_base.symm w using 2
  show _ = Over.Hom.left (toUnit (Over.mk (𝟙 (Sp R))) ≫ η)
  rw [Over.comp_left]
  exact (Category.id_comp _).symm

theorem isTangent_iff_exists (w : epsR R ⟶ splitTorus (Sp R) X) :
    IsTangent w ↔ ∃ c, lieVec c = w := by
  rw [isTangent_iff_charVal]
  exact (exists_epsVec_iff w).symm

theorem isTangent_lieVec (c : X →+ R) : IsTangent (lieVec c) := (isTangent_iff_exists _).2 ⟨c, rfl⟩

theorem lieVec_injective : Function.Injective (lieVec : (X →+ R) → _) := epsVec_injective

theorem lieVec_add (c d : X →+ R) : lieVec (c + d) = lieVec c * lieVec d := epsVec_add c d

theorem left_eq_iff_lieVec_smul (a : R) (c : X →+ R) (u : epsR R ⟶ splitTorus (Sp R) X) :
    u.left = spMap (epsScaleR a) ≫ (lieVec c).left ↔ u = lieVec (a • c) := left_eq_epsScaleR_iff a (epsScaleR_base a) c u

theorem lieVec_smul_left (a : R) (c : X →+ R) :
    (lieVec (a • c)).left = spMap (epsScaleR a) ≫ (lieVec c).left := (left_eq_iff_lieVec_smul a c _).2 rfl

theorem lieVec_smul (a : R) (c : X →+ R) : lieVec (a • c) = GrpTangent.epsScale a ≫ lieVec c := by
  apply Over.OverMorphism.ext
  rw [lieVec_smul_left, Over.comp_left]
  rfl

theorem lieVec_comp_diagMap (c : X →+ R) (u : Y →+ X) :
    lieVec c ≫ diagMap (Sp R) u = lieVec (c.comp u) := epsVec_comp_diagMap c u

theorem isLieComb_iff {n : ℕ} (a : Fin n → R) (c : Fin n → (X →+ R))
    (w : epsR R ⟶ splitTorus (Sp R) X) :
    IsLieComb a (fun i => lieVec (c i)) w ↔ w = lieVec (∑ i, a i • c i) := by
  unfold IsLieComb
  exact exists_prod_iff (fun b => epsScaleR_base b) a c w

variable (R X) in

def lieEquiv : {w : epsR R ⟶ splitTorus (Sp R) X // IsTangent w} ≃ (X →+ R) where
  toFun w := epsCoeff w.1 ((isTangent_iff_charVal _).1 w.2)
  invFun c := ⟨lieVec c, isTangent_lieVec c⟩
  left_inv _ := Subtype.ext (epsVec_epsCoeff _ _)
  right_inv _ := epsVec_injective (epsVec_epsCoeff _ _)

theorem isLieBasis_iff {n : ℕ} (c : Fin n → (X →+ R)) :
    IsLieBasis (fun i => lieVec (c i)) ↔
      LinearIndependent R c ∧ ⊤ ≤ Submodule.span R (Set.range c) := by
  have key : IsLieBasis (fun i => lieVec (c i)) ↔ ∀ d : X →+ R, ∃! a : Fin n → R, d = ∑ i, a i • c i := by
    unfold IsLieBasis
    constructor
    · rintro ⟨-, h⟩ d
      obtain ⟨a, ha, hu⟩ := h (lieVec d) (isTangent_lieVec d)
      exact ⟨a, lieVec_injective ((isLieComb_iff a c _).1 ha),
        fun b hb => hu b ((isLieComb_iff b c _).2 (congrArg lieVec hb))⟩
    · intro h
      refine ⟨fun i => isTangent_lieVec _, fun w hw => ?_⟩
      obtain ⟨d, rfl⟩ := (isTangent_iff_exists w).1 hw
      obtain ⟨a, ha, hu⟩ := h d
      exact ⟨a, (isLieComb_iff a c _).2 (congrArg lieVec ha),
        fun b hb => hu b (lieVec_injective ((isLieComb_iff b c _).1 hb))⟩
  rw [key]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · rw [Fintype.linearIndependent_iff]
      intro a ha i
      obtain ⟨z, -, hz⟩ := h 0
      have h0 : a = z := hz a ha.symm
      have h1 : (0 : Fin n → R) = z := hz 0 (by simp)
      rw [h0, ← h1]
      rfl
    · rintro d -
      obtain ⟨a, ha, -⟩ := h d
      rw [ha]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · rintro ⟨hli, hsp⟩ d
    have hd : d ∈ Submodule.span R (Set.range c) := hsp Submodule.mem_top
    rw [Submodule.mem_span_range_iff_exists_fun] at hd
    obtain ⟨a, ha⟩ := hd
    refine ⟨a, ha.symm, fun b hb => ?_⟩
    have h0 := Fintype.linearIndependent_iff.1 hli (b - a)
      (by simp [sub_smul, Finset.sum_sub_distrib, ← hb, ha])
    funext i
    simpa [sub_eq_zero] using h0 i

theorem isLieBasis_of_basis {n : ℕ} (b : Module.Basis (Fin n) R (X →+ R)) :
    IsLieBasis (fun i => lieVec (b i)) := (isLieBasis_iff _).2 ⟨b.linearIndependent, b.span_eq.ge⟩

def transpose (R : Type) [CommRing R] (u : Y →+ X) : (X →+ R) →ₗ[R] (Y →+ R) where
  toFun c := c.comp u
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem transpose_apply (u : Y →+ X) (c : X →+ R) : transpose R u c = c.comp u := rfl

section Basis

variable {I J : Type} [Fintype I] [Fintype J]

variable (R) in

def dualBasis (b : Module.Basis I ℤ X) : Module.Basis I R (X →+ R) :=
  Module.Basis.ofEquivFun
    { toFun := fun c i => c (b i)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      invFun := fun f => (b.constr ℤ f).toAddMonoidHom
      left_inv := fun c => congrArg LinearMap.toAddMonoidHom
        (b.constr_eq (S := ℤ) (f := c.toIntLinearMap) fun _ => rfl)
      right_inv := fun f => funext fun i => b.constr_basis ℤ f i }

theorem dualBasis_repr (b : Module.Basis I ℤ X) (c : X →+ R) (i : I) :
    (dualBasis R b).repr c i = c (b i) := rfl

theorem dualBasis_apply (b : Module.Basis I ℤ X) (i : I) (x : X) :
    dualBasis R b i x = (b.repr x i : R) := by
  have key : ∀ j, dualBasis R b i (b j) = (b.repr (b j) i : R) := by
    intro j
    rw [← dualBasis_repr, Module.Basis.repr_self, Module.Basis.repr_self]
    by_cases h : i = j
    · subst h
      simp
    · simp [h, Ne.symm h]
  have e : (dualBasis R b i).toIntLinearMap = (Int.castAddHom R).toIntLinearMap.comp (b.coord i) :=
    b.ext fun j => by simpa using key j
  simpa using congrArg (fun f => f x) e

theorem toMatrix_transpose [DecidableEq I] [DecidableEq J] (b : Module.Basis I ℤ X)
    (b' : Module.Basis J ℤ Y) (u : Y →+ X) :
    LinearMap.toMatrix (dualBasis R b) (dualBasis R b') (transpose R u) =
      ((LinearMap.toMatrix b' b u.toIntLinearMap).map (Int.castRingHom R)).transpose := by
  ext j i
  rw [LinearMap.toMatrix_apply, Matrix.transpose_apply, Matrix.map_apply, LinearMap.toMatrix_apply,
    dualBasis_repr, transpose_apply, AddMonoidHom.comp_apply, dualBasis_apply]
  rfl

theorem dualBasis_comp [DecidableEq J] (b : Module.Basis I ℤ X)
    (b' : Module.Basis J ℤ Y) (u : Y →+ X) (i : I) :
    (dualBasis R b i).comp u =
      ∑ j, (LinearMap.toMatrix b' b u.toIntLinearMap i j : R) • dualBasis R b' j := by
  conv_lhs => rw [← (dualBasis R b').sum_repr ((dualBasis R b i).comp u)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [dualBasis_repr, AddMonoidHom.comp_apply, dualBasis_apply, LinearMap.toMatrix_apply]
  rfl

end Basis

instance free_addHom [Module.Free ℤ X] [Module.Finite ℤ X] : Module.Free R (X →+ R) :=
  Module.Free.of_basis (dualBasis R (Module.Free.chooseBasis ℤ X))

instance finite_addHom [Module.Free ℤ X] [Module.Finite ℤ X] : Module.Finite R (X →+ R) :=
  Module.Finite.of_basis (dualBasis R (Module.Free.chooseBasis ℤ X))

theorem charpoly_transpose [Module.Free ℤ X] [Module.Finite ℤ X] (u : X →+ X) :
    (transpose R u).charpoly = u.toIntLinearMap.charpoly.map (Int.castRingHom R) := by
  classical
  let b := Module.Free.chooseBasis ℤ X
  rw [← LinearMap.charpoly_toMatrix (transpose R u) (dualBasis R b), toMatrix_transpose b b u,
    Matrix.charpoly_transpose, Matrix.charpoly_map, LinearMap.charpoly_toMatrix]

theorem isLieBasis_dualBasis {n : ℕ} (b : Module.Basis (Fin n) ℤ X) :
    IsLieBasis (fun i => lieVec (dualBasis R b i)) := isLieBasis_of_basis (dualBasis R b)

theorem isLieComb_comp_diagMap {n m : ℕ} (b : Module.Basis (Fin n) ℤ X) (b' : Module.Basis (Fin m) ℤ Y)
    (u : Y →+ X) (i : Fin n) :
    IsLieComb (fun j => (LinearMap.toMatrix b' b u.toIntLinearMap i j : R))
      (fun j => lieVec (dualBasis R b' j)) (lieVec (dualBasis R b i) ≫ diagMap (Sp R) u) := by
  rw [lieVec_comp_diagMap, isLieComb_iff, dualBasis_comp b b' u i]

end Lie

section Fibre

variable {S : Scheme.{0}} {k : Type} [Field k] (t : Sp k ⟶ S) {O : Type} [CommRing O]
  {X : Type} [AddCommGroup X] [Module O X] (τ : O →+* k)

theorem epsScaleR_base_comp (a : k) : spMap (algebraMap k (DualNumber k)) ≫ t =
    spMap (epsScaleR a) ≫ spMap (algebraMap k (DualNumber k)) ≫ t := by
  rw [← Category.assoc, ← epsScaleR_base]

theorem isLieEigen_iff (v : epsPt t ⟶ splitTorus S X) :
    IsLieEigen (diagAct S O X) t τ v ↔
      ∃ c : X →+ k, epsVec _ c = v ∧ ∀ (a : O) (x : X), c (a • x) = τ a * c x := by
  unfold IsLieEigen
  have ht : t = spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ spMap (algebraMap k (DualNumber k)) ≫ t := by
    rw [← Category.assoc, fstHom_base, Category.id_comp]
  rw [reduces_iff ht v, ← exists_epsVec_iff]
  constructor
  · rintro ⟨⟨c, rfl⟩, h2⟩
    refine ⟨c, rfl, fun a x => ?_⟩
    have h := (left_eq_epsScaleR_iff (τ a) (epsScaleR_base_comp t (τ a)) c _).1 (h2 a)
    rw [diagAct_act, epsVec_comp_diagMap] at h
    have := congrArg (fun f => f x) (epsVec_injective h)
    simpa using this
  · rintro ⟨c, rfl, hc⟩
    refine ⟨⟨c, rfl⟩, fun a => ?_⟩
    refine (left_eq_epsScaleR_iff (τ a) (epsScaleR_base_comp t (τ a)) c _).2 ?_
    rw [diagAct_act, epsVec_comp_diagMap]
    congr 1
    ext x
    simpa using hc a x

variable (X) in

def eigenHom {k : Type} [CommRing k] (τ : O →+* k) : Submodule k (X →+ k) where
  carrier := {c | ∀ (a : O) (x : X), c (a • x) = τ a * c x}
  add_mem' hc hd a x := by simp [hc a x, hd a x, mul_add]
  zero_mem' a x := by simp
  smul_mem' r c hc a x := by simp [hc a x, mul_left_comm]

theorem lieMult_iff (n : ℕ) :
    LieMult (diagAct S O X) t τ n ↔ Nonempty (Module.Basis (Fin n) k (eigenHom X τ)) := by
  have hg : ∀ a : k, spMap (algebraMap k (DualNumber k)) ≫ t =
      spMap (epsScaleR a) ≫ spMap (algebraMap k (DualNumber k)) ≫ t := epsScaleR_base_comp t
  have key : LieMult (diagAct S O X) t τ n ↔
      ∃ e : Fin n → eigenHom X τ, ∀ d : eigenHom X τ, ∃! c : Fin n → k, d = ∑ i, c i • e i := by
    unfold LieMult
    constructor
    · rintro ⟨v, hv, h⟩
      choose e he hce using fun i => (isLieEigen_iff t τ (v i)).1 (hv i)
      refine ⟨fun i => ⟨e i, hce i⟩, fun d => ?_⟩
      obtain ⟨c, hc, hu⟩ := h (epsVec _ d.1) ((isLieEigen_iff t τ _).2 ⟨d.1, rfl, d.2⟩)
      have hv' : v = fun i => epsVec _ (e i) := funext fun i => (he i).symm
      subst hv'
      refine ⟨c, ?_, fun c' hc' => hu c' ?_⟩
      · apply Subtype.ext
        have := (exists_prod_iff hg c e _).1 hc
        simpa using epsVec_injective this
      · refine (exists_prod_iff hg c' e _).2 ?_
        rw [hc']
        simp
    · rintro ⟨e, h⟩
      refine ⟨fun i => epsVec _ (e i).1, fun i => (isLieEigen_iff t τ _).2 ⟨_, rfl, (e i).2⟩,
        fun w hw => ?_⟩
      obtain ⟨d, rfl, hd⟩ := (isLieEigen_iff t τ w).1 hw
      obtain ⟨c, hc, hu⟩ := h ⟨d, hd⟩
      refine ⟨c, (exists_prod_iff hg c (fun i => (e i).1) _).2 ?_, fun c' hc' => hu c' ?_⟩
      · have := congrArg Subtype.val hc
        simp at this
        rw [this]
      · apply Subtype.ext
        have := epsVec_injective ((exists_prod_iff hg c' (fun i => (e i).1) _).1 hc')
        simpa using this
  rw [key]
  constructor
  · rintro ⟨e, h⟩
    have hli : LinearIndependent k e := by
      rw [Fintype.linearIndependent_iff]
      intro a ha i
      obtain ⟨z, -, hz⟩ := h 0
      have h0 : a = z := hz a ha.symm
      have h1 : (0 : Fin n → k) = z := hz 0 (by simp)
      rw [h0, ← h1]
      rfl
    have hsp : ⊤ ≤ Submodule.span k (Set.range e) := by
      rintro d -
      obtain ⟨a, ha, -⟩ := h d
      rw [ha]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    exact ⟨Module.Basis.mk hli hsp⟩
  · rintro ⟨b⟩
    exact ⟨b, fun d => ⟨b.repr d, (b.sum_repr d).symm, fun c hc => by rw [hc, b.repr_sum_self]⟩⟩

end Fibre

end GlobalTheory.Diag

namespace GlobalTheory

open Diag

end GlobalTheory
