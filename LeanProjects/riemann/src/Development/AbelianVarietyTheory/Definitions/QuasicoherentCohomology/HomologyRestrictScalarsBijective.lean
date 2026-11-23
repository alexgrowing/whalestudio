import Mathlib
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.IsIsoTermComparisonRestrictScalars
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CubeComplexAcyclicIffQuasiIsoCechAug

open CategoryTheory Limits

universe v v' u u'

noncomputable section

namespace GlobalTheory

variable {ι : Type} [LinearOrder ι] {R : Type u} [Ring R] {S : Type u'} [Ring S]

def cechClass (A : Cube.{v} ι R) (p : ℕ) :
    LinearMap.ker (Cube.d A (p + 1)) →ₗ[R] (cechComplex A).homology p :=
  ((cechCyclesIso A p).inv ≫ (cechComplex A).homologyπ p).hom

open CategoryTheory Limits in
variable {ι : Type} [LinearOrder ι] {R : Type u} [Ring R] {S : Type u'} [Ring S] in

theorem _root_.GlobalTheory.iCycles_cechCyclesIso_inv (A : _root_.GlobalTheory.Cube.{v} ι R) (p : ℕ)
    (x : LinearMap.ker (_root_.GlobalTheory.Cube.d A (p + 1))) :
    ((_root_.GlobalTheory.cechComplex A).iCycles p).hom ((_root_.GlobalTheory.cechCyclesIso A p).inv.hom x) = x.1 := by
  have e : (_root_.GlobalTheory.cechCyclesIso A p).hom.hom
      ((_root_.GlobalTheory.cechCyclesIso A p).inv.hom x) = x := by
    simp
  rw [← _root_.GlobalTheory.cechCyclesIso_hom_subtype]
  change ((_root_.GlobalTheory.cechCyclesIso A p).hom.hom
    ((_root_.GlobalTheory.cechCyclesIso A p).inv.hom x)).1 = x.1
  rw [e]

open CategoryTheory Limits in
variable {ι : Type} [LinearOrder ι] {R : Type u} [Ring R] {S : Type u'} [Ring S] in

theorem _root_.GlobalTheory.cechClass_surjective (A : _root_.GlobalTheory.Cube.{v} ι R) (p : ℕ) :
    Function.Surjective (_root_.GlobalTheory.cechClass A p) :=
  (ModuleCat.epi_iff_surjective _).1
    (inferInstance : Epi ((_root_.GlobalTheory.cechCyclesIso A p).inv ≫ (_root_.GlobalTheory.cechComplex A).homologyπ p))

theorem cechClass_eq_zero_iff_prev (A : Cube.{v} ι R) (q p : ℕ)
    (h : (ComplexShape.up ℕ).prev p = q) (x : LinearMap.ker (Cube.d A (p + 1))) :
    cechClass A p x = 0 ↔ ∃ y, ((cechComplex A).d q p).hom y = x.1 := by
  have hex := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
    (ShortComplex.exact_of_g_is_cokernel
      (ShortComplex.mk _ _ ((cechComplex A).toCycles_comp_homologyπ q p))
      ((cechComplex A).homologyIsCokernel q p h))
  refine (hex ((cechCyclesIso A p).inv.hom x)).trans (exists_congr fun y => ?_)
  rw [← iCycles_cechCyclesIso_inv A p x, ← (cechComplex A).toCycles_i q p]
  exact ((ModuleCat.mono_iff_injective ((cechComplex A).iCycles p)).1 inferInstance).eq_iff.symm

open CategoryTheory Limits in
variable {ι : Type} [LinearOrder ι] {R : Type u} [Ring R] {S : Type u'} [Ring S] in

theorem _root_.GlobalTheory.cechClass_succ_eq_zero_iff (A : _root_.GlobalTheory.Cube.{v} ι R) (p : ℕ)
    (x : LinearMap.ker (_root_.GlobalTheory.Cube.d A (p + 1 + 1))) :
    _root_.GlobalTheory.cechClass A (p + 1) x = 0 ↔
      ∃ y, _root_.GlobalTheory.Cube.d A (p + 1) y = x.1 := by
  set K := _root_.GlobalTheory.cechComplex A
  have hex : (ShortComplex.mk (K.toCycles p (p + 1)) (K.homologyπ (p + 1)) (by simp)).Exact :=
    ShortComplex.exact_of_g_is_cokernel _ (K.homologyIsCokernel p (p + 1) (by simp))
  have hrange : LinearMap.range (K.toCycles p (p + 1)).hom =
      LinearMap.ker (K.homologyπ (p + 1)).hom := hex.moduleCat_range_eq_ker
  have hi : Function.Injective (K.iCycles (p + 1)).hom :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  have hd : ∀ y, (K.iCycles (p + 1)).hom ((K.toCycles p (p + 1)).hom y) =
      _root_.GlobalTheory.Cube.d A (p + 1) y := by
    intro y
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, HomologicalComplex.toCycles_i,
      _root_.GlobalTheory.cechComplex_d]
    rfl
  change (K.homologyπ (p + 1)).hom ((_root_.GlobalTheory.cechCyclesIso A (p + 1)).inv.hom x) = 0 ↔ _
  rw [← LinearMap.mem_ker, ← hrange, LinearMap.mem_range]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨y, ?_⟩
    have := congrArg (K.iCycles (p + 1)).hom hy
    rw [_root_.GlobalTheory.iCycles_cechCyclesIso_inv, hd] at this
    exact this
  · rintro ⟨y, hy⟩
    refine ⟨y, hi ?_⟩
    rw [_root_.GlobalTheory.iCycles_cechCyclesIso_inv]
    exact (hd y).trans hy

open CategoryTheory Limits in
variable {ι : Type} [LinearOrder ι] {R : Type u} [Ring R] {S : Type u'} [Ring S] in
private theorem cechClass_zero_eq_iso_inv (A : _root_.GlobalTheory.Cube.{v} ι R) :
    _root_.GlobalTheory.cechClass A 0 = (_root_.GlobalTheory.cechHomologyZeroIso A).inv.hom := by
  have e : (_root_.GlobalTheory.cechCyclesIso A 0).inv ≫ (_root_.GlobalTheory.cechComplex A).homologyπ 0 =
      (_root_.GlobalTheory.cechHomologyZeroIso A).inv := by
    rw [Iso.inv_comp_eq, ← _root_.GlobalTheory.homologyπ_cechHomologyZeroIso_hom, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  rw [_root_.GlobalTheory.cechClass, e]

open CategoryTheory Limits in
variable {ι : Type} [LinearOrder ι] {R : Type u} [Ring R] {S : Type u'} [Ring S] in
private theorem cechClass_zero_bijective' (A : _root_.GlobalTheory.Cube.{v} ι R) :
    Function.Bijective (_root_.GlobalTheory.cechClass A 0) := by
  rw [cechClass_zero_eq_iso_inv]
  exact (_root_.GlobalTheory.cechHomologyZeroIso A).symm.toLinearEquiv.bijective

open CategoryTheory Limits in
variable {ι : Type} [LinearOrder ι] {R : Type u} [Ring R] {S : Type u'} [Ring S] in

theorem _root_.GlobalTheory.cechClass_zero_eq_zero_iff (A : _root_.GlobalTheory.Cube.{v} ι R)
    (x : LinearMap.ker (_root_.GlobalTheory.Cube.d A (0 + 1))) :
    _root_.GlobalTheory.cechClass A 0 x = 0 ↔ x = 0 :=
  (cechClass_zero_bijective' A).1.eq_iff' (map_zero _)

open CategoryTheory Limits in
variable {ι : Type} [LinearOrder ι] {R : Type u} [Ring R] {S : Type u'} [Ring S] in

theorem _root_.GlobalTheory.cechClass_zero_bijective (A : _root_.GlobalTheory.Cube.{v} ι R) :
    Function.Bijective (_root_.GlobalTheory.cechClass A 0) :=
  cechClass_zero_bijective' A

theorem cechHomologyZeroIso_cechClass (A : Cube.{v} ι R) (x : LinearMap.ker (Cube.d A (0 + 1))) :
    (cechHomologyZeroIso A).hom.hom (cechClass A 0 x) = x := by
  have h : ((cechCyclesIso A 0).inv ≫ (cechComplex A).homologyπ 0) ≫ (cechHomologyZeroIso A).hom =
      𝟙 _ := by
    rw [Category.assoc, homologyπ_cechHomologyZeroIso_hom, Iso.inv_hom_id]
  exact congr(($h).hom x)

open CategoryTheory Limits in
variable {ι : Type} [LinearOrder ι] {R : Type u} [Ring R] {S : Type u'} [Ring S] in

theorem _root_.GlobalTheory.homologyMap_cechClass {A B : _root_.GlobalTheory.Cube.{v} ι R} (φ : A ⟶ B) (p : ℕ)
    (x : LinearMap.ker (_root_.GlobalTheory.Cube.d A (p + 1)))
    (y : LinearMap.ker (_root_.GlobalTheory.Cube.d B (p + 1)))
    (h : _root_.GlobalTheory.Cube.termMap φ (p + 1) x.1 = y.1) :
    (HomologicalComplex.homologyMap (_root_.GlobalTheory.cechComplexMap φ) p).hom (_root_.GlobalTheory.cechClass A p x) =
      _root_.GlobalTheory.cechClass B p y := by
  have hi : Function.Injective ((_root_.GlobalTheory.cechComplex B).iCycles p).hom :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  have hc : (HomologicalComplex.cyclesMap (_root_.GlobalTheory.cechComplexMap φ) p).hom
      ((_root_.GlobalTheory.cechCyclesIso A p).inv.hom x) = (_root_.GlobalTheory.cechCyclesIso B p).inv.hom y := by
    apply hi
    rw [_root_.GlobalTheory.iCycles_cechCyclesIso_inv, ← LinearMap.comp_apply, ← ModuleCat.hom_comp,
      HomologicalComplex.cyclesMap_i, ModuleCat.hom_comp, LinearMap.comp_apply,
      _root_.GlobalTheory.iCycles_cechCyclesIso_inv, ← h]
    rfl
  simp only [_root_.GlobalTheory.cechClass, ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [← hc, ← LinearMap.comp_apply, ← ModuleCat.hom_comp,
    HomologicalComplex.homologyπ_naturality]
  rfl

open CategoryTheory Limits in
variable {ι : Type} [LinearOrder ι] {R : Type u} [Ring R] {S : Type u'} [Ring S] in

theorem _root_.GlobalTheory.Cube.termMap_mem_ker {A B : _root_.GlobalTheory.Cube.{v} ι R} (φ : A ⟶ B) {p : ℕ}
    {x : _root_.GlobalTheory.Cube.Term A p}
    (h : x ∈ LinearMap.ker (_root_.GlobalTheory.Cube.d A p)) :
    _root_.GlobalTheory.Cube.termMap φ p x ∈ LinearMap.ker (_root_.GlobalTheory.Cube.d B p) := by
  rw [LinearMap.mem_ker, ← _root_.GlobalTheory.Cube.termMap_d, LinearMap.mem_ker.1 h,
    map_zero]

open CategoryTheory Limits in
variable {ι : Type} [LinearOrder ι] {R : Type u} [Ring R] {S : Type u'} [Ring S] in

theorem _root_.GlobalTheory.cechAugHomology_apply (A : _root_.GlobalTheory.Cube.{v} ι R) (a : A.obj ∅) :
    (_root_.GlobalTheory.cechAugHomology A).hom a =
      _root_.GlobalTheory.cechClass A 0
        ⟨_root_.GlobalTheory.Cube.aug A a, _root_.GlobalTheory.Cube.d_aug A a⟩ := by
  rw [cechClass_zero_eq_iso_inv]
  have hinj : Function.Injective (_root_.GlobalTheory.cechHomologyZeroIso A).hom.hom :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  apply hinj
  have h := congrArg (fun g => ModuleCat.Hom.hom g a)
    (_root_.GlobalTheory.cechAugHomology_comp A)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
    Submodule.subtype_apply] at h
  apply Subtype.ext
  rw [h]
  simp

structure Cube.SemiHom (f : R →+* S) (A : Cube.{v} ι R) (B : Cube.{v'} ι S) where

  app : ∀ s, A.obj s →ₛₗ[f] B.obj s

  app_res : ∀ {s t : Finset ι} (h : s ⊆ t) (x : A.obj s),
    app t (Cube.res A h x) = Cube.res B h (app s x)

namespace Cube.SemiHom

variable {f : R →+* S} {A A' : Cube.{v} ι R} {B B' : Cube.{v'} ι S} (ψ : Cube.SemiHom f A B)

omit [LinearOrder ι] in

@[simps]
def ofHom (φ : A ⟶ A') : Cube.SemiHom (RingHom.id R) A A' where
  app s := (φ.app s).hom
  app_res := Cube.app_res φ

omit [LinearOrder ι] in

def term (p : ℕ) : Cube.Term A p →ₛₗ[f] Cube.Term B p where
  toFun x s := ψ.app s.1 (x s)
  map_add' x y := funext fun s => map_add _ _ _
  map_smul' r x := funext fun s => map_smulₛₗ (ψ.app s.1) r (x s)

omit [LinearOrder ι] in

@[simp]
theorem term_apply (p : ℕ) (x : Cube.Term A p) (s : {s : Finset ι // s.card = p}) :
    ψ.term p x s = ψ.app s.1 (x s) := rfl

open CategoryTheory Limits in
variable {ι : Type} [LinearOrder ι] {R : Type u} [Ring R] {S : Type u'} [Ring S] in
variable {f : R →+* S} {A A' : _root_.GlobalTheory.Cube.{v} ι R} {B B' : _root_.GlobalTheory.Cube.{v'} ι S}
  (ψ : _root_.GlobalTheory.Cube.SemiHom f A B) in

theorem _root_.GlobalTheory.Cube.SemiHom.term_d (p : ℕ) (x : _root_.GlobalTheory.Cube.Term A p) :
    ψ.term (p + 1) (_root_.GlobalTheory.Cube.d A p x) =
      _root_.GlobalTheory.Cube.d B p (ψ.term p x) := by
  funext t
  rw [_root_.GlobalTheory.Cube.SemiHom.term_apply, _root_.GlobalTheory.Cube.d_apply,
    _root_.GlobalTheory.Cube.d_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, _root_.GlobalTheory.Cube.SemiHom.app_res, _root_.GlobalTheory.Cube.SemiHom.term_apply]

omit [LinearOrder ι] in

theorem term_aug (a : A.obj ∅) : ψ.term 1 (Cube.aug A a) = Cube.aug B (ψ.app ∅ a) :=
  funext fun _ => ψ.app_res _ a

open CategoryTheory Limits in
variable {ι : Type} [LinearOrder ι] {R : Type u} [Ring R] {S : Type u'} [Ring S] in
variable {f : R →+* S} {A A' : _root_.GlobalTheory.Cube.{v} ι R} {B B' : _root_.GlobalTheory.Cube.{v'} ι S}
  (ψ : _root_.GlobalTheory.Cube.SemiHom f A B) in
omit [LinearOrder ι] in

theorem _root_.GlobalTheory.Cube.SemiHom.term_bijective
    (h : ∀ s : Finset ι, s.Nonempty → Function.Bijective (ψ.app s)) (p : ℕ) :
    Function.Bijective (ψ.term (p + 1)) := by
  have hne : ∀ s : {s : Finset ι // s.card = p + 1}, s.1.Nonempty := fun s =>
    Finset.card_pos.1 (by rw [s.2]; exact Nat.succ_pos p)
  refine ⟨fun x y hxy => funext fun s => (h s.1 (hne s)).1 (congrFun hxy s), fun y => ?_⟩
  refine ⟨fun s => ((h s.1 (hne s)).2 (y s)).choose, funext fun s => ?_⟩
  exact ((h s.1 (hne s)).2 (y s)).choose_spec

def cocycle (p : ℕ) : LinearMap.ker (Cube.d A p) →ₛₗ[f] LinearMap.ker (Cube.d B p) :=
  ((ψ.term p).domRestrict _).codRestrict _ fun x => by
    rw [LinearMap.mem_ker, LinearMap.domRestrict_apply, ← term_d, x.2, map_zero]

@[simp]
theorem coe_cocycle (p : ℕ) (x : LinearMap.ker (Cube.d A p)) :
    (ψ.cocycle p x).1 = ψ.term p x.1 := rfl

open CategoryTheory Limits in
variable {ι : Type} [LinearOrder ι] {R : Type u} [Ring R] {S : Type u'} [Ring S] in
variable {f : R →+* S} {A A' : _root_.GlobalTheory.Cube.{v} ι R} {B B' : _root_.GlobalTheory.Cube.{v'} ι S}
  (ψ : _root_.GlobalTheory.Cube.SemiHom f A B) in

theorem _root_.GlobalTheory.Cube.SemiHom.cechClass_cocycle_eq_zero (p : ℕ)
    (x : LinearMap.ker (_root_.GlobalTheory.Cube.d A (p + 1)))
    (h : _root_.GlobalTheory.cechClass A p x = 0) :
    _root_.GlobalTheory.cechClass B p (ψ.cocycle (p + 1) x) = 0 := by
  cases p with
  | zero =>
    rw [_root_.GlobalTheory.cechClass_zero_eq_zero_iff] at h ⊢
    rw [h, map_zero]
  | succ p =>
    rw [_root_.GlobalTheory.cechClass_succ_eq_zero_iff] at h ⊢
    obtain ⟨y, hy⟩ := h
    exact ⟨ψ.term (p + 1) y, by rw [← _root_.GlobalTheory.Cube.SemiHom.term_d, hy, _root_.GlobalTheory.Cube.SemiHom.coe_cocycle]⟩

def homology (p : ℕ) : (cechComplex A).homology p →ₛₗ[f] (cechComplex B).homology p :=
  ((LinearMap.ker (cechClass A p)).liftQ ((cechClass B p).comp (ψ.cocycle (p + 1)))
    (ψ.cechClass_cocycle_eq_zero p)).comp
    ((cechClass A p).quotKerEquivOfSurjective (cechClass_surjective A p)).symm.toLinearMap

open CategoryTheory Limits in
variable {ι : Type} [LinearOrder ι] {R : Type u} [Ring R] {S : Type u'} [Ring S] in
variable {f : R →+* S} {A A' : _root_.GlobalTheory.Cube.{v} ι R} {B B' : _root_.GlobalTheory.Cube.{v'} ι S}
  (ψ : _root_.GlobalTheory.Cube.SemiHom f A B) in

@[simp]
theorem _root_.GlobalTheory.Cube.SemiHom.homology_cechClass (p : ℕ)
    (x : LinearMap.ker (_root_.GlobalTheory.Cube.d A (p + 1))) :
    ψ.homology p (_root_.GlobalTheory.cechClass A p x) =
      _root_.GlobalTheory.cechClass B p (ψ.cocycle (p + 1) x) := by
  have e : ((_root_.GlobalTheory.cechClass A p).quotKerEquivOfSurjective
      (_root_.GlobalTheory.cechClass_surjective A p)).symm (_root_.GlobalTheory.cechClass A p x) = Submodule.Quotient.mk x :=
    (LinearEquiv.symm_apply_eq _).2 rfl
  simp only [_root_.GlobalTheory.Cube.SemiHom.homology, LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [e]
  rfl

theorem homology_ofHom (φ : A ⟶ A') (p : ℕ) :
    (ofHom φ).homology p = (HomologicalComplex.homologyMap (cechComplexMap φ) p).hom := by
  ext x
  obtain ⟨x, rfl⟩ := cechClass_surjective A p x
  rw [homology_cechClass]
  exact (homologyMap_cechClass φ p x _ rfl).symm

open CategoryTheory Limits in
variable {ι : Type} [LinearOrder ι] {R : Type u} [Ring R] {S : Type u'} [Ring S] in
variable {f : R →+* S} {A A' : _root_.GlobalTheory.Cube.{v} ι R} {B B' : _root_.GlobalTheory.Cube.{v'} ι S}
  (ψ : _root_.GlobalTheory.Cube.SemiHom f A B) in

theorem _root_.GlobalTheory.Cube.SemiHom.homology_bijective
    (h : ∀ s : Finset ι, s.Nonempty → Function.Bijective (ψ.app s))
    (p : ℕ) : Function.Bijective (ψ.homology p) := by
  have hT := ψ.term_bijective h
  constructor
  · rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨x, rfl⟩ := _root_.GlobalTheory.cechClass_surjective A p z
    rw [_root_.GlobalTheory.Cube.SemiHom.homology_cechClass] at hz
    cases p with
    | zero =>
      rw [_root_.GlobalTheory.cechClass_zero_eq_zero_iff] at hz ⊢
      have hx := congrArg Subtype.val hz
      rw [_root_.GlobalTheory.Cube.SemiHom.coe_cocycle] at hx
      apply Subtype.ext
      apply (hT 0).1
      rw [hx]
      simp
    | succ p =>
      rw [_root_.GlobalTheory.cechClass_succ_eq_zero_iff] at hz ⊢
      obtain ⟨y, hy⟩ := hz
      obtain ⟨y', rfl⟩ := (hT p).2 y
      refine ⟨y', (hT (p + 1)).1 ?_⟩
      rw [_root_.GlobalTheory.Cube.SemiHom.term_d, hy, _root_.GlobalTheory.Cube.SemiHom.coe_cocycle]
  · intro z
    obtain ⟨y, rfl⟩ := _root_.GlobalTheory.cechClass_surjective B p z
    obtain ⟨x', hx'⟩ := (hT p).2 y.1
    have hker : x' ∈ LinearMap.ker (_root_.GlobalTheory.Cube.d A (p + 1)) := by
      rw [LinearMap.mem_ker]
      apply (hT (p + 1)).1
      rw [_root_.GlobalTheory.Cube.SemiHom.term_d, hx', map_zero]
      exact LinearMap.mem_ker.1 y.2
    refine ⟨_root_.GlobalTheory.cechClass A p ⟨x', hker⟩, ?_⟩
    rw [_root_.GlobalTheory.Cube.SemiHom.homology_cechClass]
    congr 1
    exact Subtype.ext hx'

open CategoryTheory Limits in
variable {ι : Type} [LinearOrder ι] {R : Type u} [Ring R] {S : Type u'} [Ring S] in
variable {f : R →+* S} {A A' : _root_.GlobalTheory.Cube.{v} ι R} {B B' : _root_.GlobalTheory.Cube.{v'} ι S}
  (ψ : _root_.GlobalTheory.Cube.SemiHom f A B) in

theorem _root_.GlobalTheory.Cube.SemiHom.homology_naturality (ψ' : _root_.GlobalTheory.Cube.SemiHom f A' B') (α : A ⟶ A')
    (β : B ⟶ B')
    (h : ∀ s, s.Nonempty → ∀ x, ψ'.app s ((α.app s).hom x) =
      (β.app s).hom (ψ.app s x)) (p : ℕ)
    (x : (_root_.GlobalTheory.cechComplex A).homology p) :
    ψ'.homology p
        ((HomologicalComplex.homologyMap (_root_.GlobalTheory.cechComplexMap α) p).hom x) =
      (HomologicalComplex.homologyMap (_root_.GlobalTheory.cechComplexMap β) p).hom
        (ψ.homology p x) := by
  obtain ⟨x, rfl⟩ := _root_.GlobalTheory.cechClass_surjective A p x
  rw [_root_.GlobalTheory.homologyMap_cechClass α p x
      ⟨_root_.GlobalTheory.Cube.termMap α (p + 1) x.1, _root_.GlobalTheory.Cube.termMap_mem_ker α x.2⟩ rfl,
    _root_.GlobalTheory.Cube.SemiHom.homology_cechClass, _root_.GlobalTheory.Cube.SemiHom.homology_cechClass,
    _root_.GlobalTheory.homologyMap_cechClass β p _
      ⟨_root_.GlobalTheory.Cube.termMap β (p + 1) (ψ.cocycle (p + 1) x).1,
        _root_.GlobalTheory.Cube.termMap_mem_ker β (ψ.cocycle (p + 1) x).2⟩ rfl]
  congr 1
  apply Subtype.ext
  funext s
  simp only [_root_.GlobalTheory.Cube.SemiHom.coe_cocycle, _root_.GlobalTheory.Cube.SemiHom.term_apply, _root_.GlobalTheory.Cube.termMap_apply]
  exact h s.1 (Finset.card_pos.1 (by rw [s.2]; exact Nat.succ_pos p)) (x.1 s)

theorem homology_homology {Q : Type*} [Ring Q] {g : S →+* Q} {k : R →+* Q} {C : Cube ι Q}
    (χ : Cube.SemiHom g B C) (ω : Cube.SemiHom k A C)
    (h : ∀ s, s.Nonempty → ∀ x, χ.app s (ψ.app s x) = ω.app s x) (p : ℕ)
    (x : (cechComplex A).homology p) : χ.homology p (ψ.homology p x) = ω.homology p x := by
  obtain ⟨x, rfl⟩ := cechClass_surjective A p x
  rw [homology_cechClass, homology_cechClass, homology_cechClass]
  exact congrArg _ (Subtype.ext (funext fun s =>
    h s.1 (Finset.card_pos.1 (by have := s.2; omega)) _))

open CategoryTheory Limits in
variable {ι : Type} [LinearOrder ι] {R : Type u} [Ring R] {S : Type u'} [Ring S] in
variable {f : R →+* S} {A A' : _root_.GlobalTheory.Cube.{v} ι R} {B B' : _root_.GlobalTheory.Cube.{v'} ι S}
  (ψ : _root_.GlobalTheory.Cube.SemiHom f A B) in

theorem _root_.GlobalTheory.Cube.SemiHom.homology_cechAugHomology (a : A.obj ∅) :
    ψ.homology 0 ((_root_.GlobalTheory.cechAugHomology A).hom a) =
      (_root_.GlobalTheory.cechAugHomology B).hom (ψ.app ∅ a) := by
  rw [_root_.GlobalTheory.cechAugHomology_apply, _root_.GlobalTheory.cechAugHomology_apply, _root_.GlobalTheory.Cube.SemiHom.homology_cechClass]
  congr 1
  apply Subtype.ext
  funext s
  rw [_root_.GlobalTheory.Cube.SemiHom.coe_cocycle, _root_.GlobalTheory.Cube.SemiHom.term_apply]
  unfold _root_.GlobalTheory.Cube.aug
  simp [_root_.GlobalTheory.Cube.SemiHom.app_res]

omit [LinearOrder ι] in

def restrictScalars (f : R →+* S) (B : Cube.{v} ι S) :
    Cube.SemiHom f (B ⋙ ModuleCat.restrictScalars f) B where
  app s := { toFun := fun x => x, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  app_res _ _ := rfl

theorem homology_restrictScalars_bijective (f : R →+* S) (B : Cube.{v} ι S) (p : ℕ) :
    Function.Bijective ((restrictScalars f B).homology p) :=
  homology_bijective _ (fun _ _ => Function.bijective_id) p

omit [LinearOrder ι] in

def constRingHom (ι : Type) (f : R →+* S) :
    Cube.SemiHom f (Cube.const ι (ModuleCat.of R R)) (Cube.const ι (ModuleCat.of S S)) where
  app _ := f.toSemilinearMap
  app_res _ _ := rfl

example (s : {s : Finset (Fin 2) // s.card = 1}) :
    (constRingHom (Fin 2) (Int.castRingHom ℚ)).term 1 (fun _ => (2 : ℤ)) s = (2 : ℚ) := rfl

end Cube.SemiHom

end GlobalTheory
