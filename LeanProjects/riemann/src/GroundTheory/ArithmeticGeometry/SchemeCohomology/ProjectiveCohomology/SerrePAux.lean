import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.GlobalGen
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.PSpaceFinite
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.ModulesAbExact
import GroundTheory.ArithmeticGeometry.SchemeCohomology.SheafH
import GroundTheory.ArithmeticGeometry.SchemeCohomology.CechNaturality.CechFunctor
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits MonoidalCategory
  MvPolynomial

universe w' u

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

section Additive

variable {X : Scheme.{u}}

lemma modulesAbMap_add {F G : X.Modules} (φ ψ : F ⟶ G) :
    modulesAbMap (φ + ψ) = modulesAbMap φ + modulesAbMap ψ := by
  ext U x
  rfl

variable [HasExt.{w'} (Sheaf (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat.{u})]
  (A : Type*) [CommRing A] [Algebra A Γ(X, ⊤)]

lemma H.linearMap_add {F G : X.Modules} (φ ψ : F ⟶ G) (p : ℕ) :
    H.linearMap.{w'} A (φ + ψ) p = H.linearMap A φ p + H.linearMap A ψ p := by
  ext x
  simp only [H.linearMap_apply, LinearMap.add_apply, modulesAbMap_add, Sheaf.H.map_add_apply]

lemma H.linearMap_comp {F G K : X.Modules} (φ : F ⟶ G) (ψ : G ⟶ K) (p : ℕ) :
    H.linearMap.{w'} A (φ ≫ ψ) p = (H.linearMap A ψ p).comp (H.linearMap A φ p) := by
  ext x
  simp only [H.linearMap_apply, LinearMap.comp_apply, modulesAbMap_comp, Sheaf.H.map_comp_apply]

lemma H.linearMap_id (F : X.Modules) (p : ℕ) :
    H.linearMap.{w'} A (𝟙 F) p = LinearMap.id := by
  ext x
  simp only [H.linearMap_apply, LinearMap.id_apply, modulesAbMap_id, Sheaf.H.map_id_apply]

lemma H.linearMap_zero (F G : X.Modules) (p : ℕ) :
    H.linearMap.{w'} A (0 : F ⟶ G) p = 0 := by
  have h := H.linearMap_add.{w'} A (0 : F ⟶ G) 0 p
  rw [add_zero] at h
  exact left_eq_add.mp h

lemma H.linearMap_sum {F G : X.Modules} {ι : Type*} (s : Finset ι) (φ : ι → (F ⟶ G)) (p : ℕ) :
    H.linearMap.{w'} A (∑ i ∈ s, φ i) p = ∑ i ∈ s, H.linearMap A (φ i) p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [H.linearMap_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, H.linearMap_add, ih]

def H.linearEquivOfIso {F G : X.Modules} (e : F ≅ G) (p : ℕ) :
    Sheaf.H.{w'} (modulesAb F) p ≃ₗ[A] Sheaf.H.{w'} (modulesAb G) p :=
  ((H.moduleFunctor.{w'} A p).mapIso e).toLinearEquiv

end Additive

section Delta

variable {X : Scheme.{u}}

def abSC (S : ShortComplex X.Modules) :
    ShortComplex (Sheaf (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat.{u}) :=
  ShortComplex.mk (modulesAbMap S.f) (modulesAbMap S.g) (by
    rw [← modulesAbMap_comp, S.zero]
    exact (SheafOfModules.toSheaf X.ringCatSheaf).map_zero _ _)

lemma shortExact_abSC {S : ShortComplex X.Modules} (hS : S.ShortExact) : (abSC S).ShortExact :=
  shortExact_abShortComplex hS

variable [HasExt.{w'} (Sheaf (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat.{u})]
  (A : Type*) [CommRing A] [Algebra A Γ(X, ⊤)]
  {S : ShortComplex X.Modules} (hS : (abSC S).ShortExact)

def abSmulEnd (S : ShortComplex X.Modules) (r : Γ(X, ⊤)) : abSC S ⟶ abSC S where
  τ₁ := modulesAbMap (smulHom S.X₁ r)
  τ₂ := modulesAbMap (smulHom S.X₂ r)
  τ₃ := modulesAbMap (smulHom S.X₃ r)
  comm₁₂ := smulAbRingHom_comp S.f r
  comm₂₃ := smulAbRingHom_comp S.g r

def H.δLinear (p : ℕ) :
    Sheaf.H.{w'} (modulesAb S.X₃) p →ₗ[A] Sheaf.H.{w'} (modulesAb S.X₁) (p + 1) where
  toFun := H.δ hS p (p + 1) rfl
  map_add' := map_add _
  map_smul' a x :=
    H.δ_naturality hS hS (abSmulEnd S (algebraMap A Γ(X, ⊤) a)) p (p + 1) rfl x

lemma H.δLinear_apply (p : ℕ) (x : Sheaf.H.{w'} (modulesAb S.X₃) p) :
    H.δLinear A hS p x = H.δ hS p (p + 1) rfl x := rfl

end Delta

section Finite

theorem finite_of_exact_noetherian {R M₁ M₂ M₃ : Type*} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃] [Module R M₁] [Module R M₂] [Module R M₃]
    [Module.Finite R M₁] [Module.Finite R M₃] (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃)
    (hfg : ∀ y, g y = 0 → ∃ x, f x = y) : Module.Finite R M₂ := by
  have hker : LinearMap.ker g ≤ LinearMap.range f := fun y hy => hfg y hy
  have hN3 : IsNoetherian R M₃ := isNoetherian_of_isNoetherianRing_of_finite R M₃
  have hrg : (LinearMap.range g).FG := IsNoetherian.noetherian _
  have hrf : (LinearMap.range f).FG := by
    rw [LinearMap.range_eq_map]; exact Module.Finite.fg_top.map f
  have hN : IsNoetherian R (LinearMap.range f) := isNoetherian_of_fg_of_noetherian _ hrf
  have hkf : (LinearMap.ker g).FG := by
    have h0 : ((LinearMap.ker g).comap (LinearMap.range f).subtype).FG := IsNoetherian.noetherian _
    have h := h0.map (LinearMap.range f).subtype
    rwa [Submodule.map_comap_eq, Submodule.range_subtype, inf_eq_right.mpr hker] at h
  refine ⟨Submodule.fg_of_fg_map_of_fg_inf_ker g ?_ ?_⟩
  · rw [Submodule.map_top]; exact hrg
  · rw [top_inf_eq]; exact hkf

end Finite

section Sandwich

variable {X : Scheme.{u}}
  [HasExt.{w'} (Sheaf (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat.{u})]
  (A : Type*) [CommRing A] [Algebra A Γ(X, ⊤)]
  {S : ShortComplex X.Modules} (hS : S.ShortExact)

include hS in

theorem finite_H_X₃ [IsNoetherianRing A] (p : ℕ)
    [Module.Finite A (Sheaf.H.{w'} (modulesAb S.X₂) p)]
    [Module.Finite A (Sheaf.H.{w'} (modulesAb S.X₁) (p + 1))] :
    Module.Finite A (Sheaf.H.{w'} (modulesAb S.X₃) p) :=
  finite_of_exact_noetherian (H.linearMap A S.g p) (H.δLinear A (shortExact_abSC hS) p)
    fun y hy => H.exact₃ (shortExact_abSC hS) rfl y hy

include hS in

theorem subsingleton_H_X₃ (p : ℕ) [Subsingleton (Sheaf.H.{w'} (modulesAb S.X₂) p)]
    [Subsingleton (Sheaf.H.{w'} (modulesAb S.X₁) (p + 1))] :
    Subsingleton (Sheaf.H.{w'} (modulesAb S.X₃) p) := by
  have key : ∀ y : Sheaf.H.{w'} (modulesAb S.X₃) p, y = 0 := fun y => by
    have : Subsingleton (Sheaf.H.{w'} (abSC S).X₁ (p + 1)) :=
      ‹Subsingleton (Sheaf.H.{w'} (modulesAb S.X₁) (p + 1))›
    obtain ⟨x, hx⟩ := H.exact₃ (shortExact_abSC hS) rfl y (Subsingleton.elim _ _)
    have : Subsingleton (Sheaf.H.{w'} (abSC S).X₂ p) := ‹Subsingleton (Sheaf.H.{w'} (modulesAb S.X₂) p)›
    rw [← hx, Subsingleton.elim x 0, map_zero]
    rfl
  exact ⟨fun y z => (key y).trans (key z).symm⟩

end Sandwich

namespace ProjSpace

variable {A : Type u} [CommRing A] {n : ℕ}

abbrev twistEquiv (k : ℤ) : (projectiveSpace A n).Modules ≌ (projectiveSpace A n).Modules :=
  tensorEquivOfInvertible (isInvertibleSheaf_twistingSheaf (A := A) (n := n) k)

lemma twistEquiv_obj (k : ℤ) (M : (projectiveSpace A n).Modules) :
    (twistEquiv k).functor.obj M = twist M k := by
  rw [twistEquiv, tensorEquivOfInvertible_functor]
  rfl

lemma twistEquiv_additive (k : ℤ) : (twistEquiv (A := A) (n := n) k).functor.Additive :=
  Functor.additive_of_preserves_binary_products _

variable (A n) in

abbrev freeP (I : Type u) : (projectiveSpace A n).Modules :=
  SheafOfModules.free (R := (projectiveSpace A n).ringCatSheaf) I

def ιP {I : Type u} (i : I) : 𝟙_ (projectiveSpace A n).Modules ⟶ freeP A n I :=
  SheafOfModules.ιFree i

def πP {I : Type u} [DecidableEq I] (i : I) : freeP A n I ⟶ 𝟙_ (projectiveSpace A n).Modules :=
  Cofan.IsColimit.desc (SheafOfModules.isColimitFreeCofan I) fun j => if j = i then 𝟙 _ else 0

lemma freeSheaf_hom_ext {I : Type u} {M : (projectiveSpace A n).Modules} (f g : freeP A n I ⟶ M)
    (h : ∀ j, ιP j ≫ f = ιP j ≫ g) : f = g :=
  Cofan.IsColimit.hom_ext (SheafOfModules.isColimitFreeCofan I) f g fun j => by
    rw [SheafOfModules.freeCofan_inj]
    exact h j

lemma ιP_πP {I : Type u} [DecidableEq I] (i j : I) :
    ιP (A := A) (n := n) j ≫ πP i = if j = i then 𝟙 _ else 0 := by
  have := Cofan.IsColimit.fac (SheafOfModules.isColimitFreeCofan
    (R := (projectiveSpace A n).ringCatSheaf) I) (fun j => if j = i then 𝟙 _ else 0) j
  rw [SheafOfModules.freeCofan_inj] at this
  exact this

lemma free_total {I : Type u} [Fintype I] [DecidableEq I] :
    ∑ i, πP (A := A) (n := n) i ≫ ιP i = 𝟙 (freeP A n I) := by
  refine freeSheaf_hom_ext _ _ fun j => ?_
  rw [Preadditive.comp_sum, Category.comp_id, Finset.sum_eq_single j]
  · rw [← Category.assoc, ιP_πP, if_pos rfl, Category.id_comp]
  · intro b _ hb
    rw [← Category.assoc, ιP_πP, if_neg (Ne.symm hb), zero_comp]
  · intro h
    exact absurd (Finset.mem_univ j) h

lemma finite_sections_unit (U : (projectiveSpace A n).Opens) :
    Module.Finite Γ(projectiveSpace A n, U) Γ(𝟙_ (projectiveSpace A n).Modules, U) := by
  let one : Γ(𝟙_ (projectiveSpace A n).Modules, U) := (show Γ(projectiveSpace A n, U) from 1)
  refine ⟨⟨{one}, ?_⟩⟩
  rw [eq_top_iff]
  intro x _
  rw [Finset.coe_singleton, Submodule.mem_span_singleton]
  exact ⟨(show Γ(projectiveSpace A n, U) from x), mul_one (show Γ(projectiveSpace A n, U) from x)⟩

lemma twist_total (k : ℤ) {I : Type u} [Fintype I] [DecidableEq I] :
    ∑ i, (twistEquiv (A := A) (n := n) k).functor.map (πP i) ≫
      (twistEquiv k).functor.map (ιP i) = 𝟙 ((twistEquiv k).functor.obj (freeP A n I)) := by
  have : (twistEquiv (A := A) (n := n) k).functor.Additive := twistEquiv_additive k
  set F := (twistEquiv (A := A) (n := n) k).functor
  calc ∑ i, F.map (πP i) ≫ F.map (ιP i)
      = ∑ i, F.map (πP (A := A) (n := n) i ≫ ιP i) := by
        simp only [Functor.map_comp]
    _ = F.map (∑ i, πP (A := A) (n := n) i ≫ ιP i) := (F.map_sum _ _).symm
    _ = F.map (𝟙 _) := congrArg F.map free_total
    _ = 𝟙 _ := F.map_id _

lemma sum_app_apply {M N : (projectiveSpace A n).Modules} {ι : Type*} (s : Finset ι)
    (φ : ι → (M ⟶ N)) (U : (projectiveSpace A n).Opens) (x : Γ(M, U)) :
    (∑ i ∈ s, φ i).app U x = ∑ i ∈ s, (φ i).app U x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp [Finset.sum_insert ha, ih]

theorem isCoherent_freeP (I : Type u) [Finite I] : IsCoherent (freeP A n I) := by
  classical
  have := Fintype.ofFinite I
  refine ⟨inferInstanceAs (SheafOfModules.free I).IsQuasicoherent, fun U _ => ?_⟩
  have := finite_sections_unit (A := A) (n := n) U
  let ιL : I → Γ(𝟙_ (projectiveSpace A n).Modules, U)
      →ₗ[Γ(projectiveSpace A n, U)] Γ(freeP A n I, U) := fun i =>
    { toFun := (ιP i).app U
      map_add' := map_add _
      map_smul' := fun r x => Scheme.Modules.Hom.app_smul _ r x }
  let Φ : (I → Γ(𝟙_ (projectiveSpace A n).Modules, U))
      →ₗ[Γ(projectiveSpace A n, U)] Γ(freeP A n I, U) := ∑ i, (ιL i).comp (LinearMap.proj i)
  refine Module.Finite.of_surjective Φ fun x => ⟨fun i => (πP i).app U x, ?_⟩
  have h := congrArg (fun φ => Scheme.Modules.Hom.app φ U x)
    (free_total (A := A) (n := n) (I := I))
  simp only [sum_app_apply, Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.id_app,
    ConcreteCategory.comp_apply, ConcreteCategory.id_apply] at h
  simp only [Φ, ιL, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply,
    LinearMap.coe_mk, AddHom.coe_mk]
  exact h

variable [HasExt.{w'} (Sheaf (Opens.grothendieckTopology (projectiveSpace A n).toTopCat) AddCommGrpCat.{u})]

attribute [local instance] algebraOfOver

lemma H_twist_free_eq {I : Type u} [Fintype I] [DecidableEq I] (k : ℤ) (p : ℕ)
    (x : Sheaf.H.{w'} (modulesAb ((twistEquiv (A := A) (n := n) k).functor.obj (freeP A n I))) p) :
    x = ∑ i, H.linearMap A ((twistEquiv k).functor.map (ιP i)) p
      (H.linearMap A ((twistEquiv k).functor.map (πP i)) p x) := by
  conv_lhs => rw [← LinearMap.id_apply (R := A) x, ← H.linearMap_id, ← twist_total k]
  rw [H.linearMap_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [H.linearMap_comp, LinearMap.comp_apply]

def H_twistUnitEquiv (k : ℤ) (p : ℕ) :
    Sheaf.H.{w'} (modulesAb ((twistEquiv (A := A) (n := n) k).functor.obj
      (𝟙_ (projectiveSpace A n).Modules))) p ≃ₗ[A]
      Sheaf.H.{w'} (modulesAb (twistingSheaf (grading A n) k)) p :=
  H.linearEquivOfIso A (eqToIso (twistEquiv_obj k _) ≪≫ λ_ _) p

lemma finite_H_twist_free (I : Type u) [Finite I] (k : ℤ) (p : ℕ) :
    Module.Finite A (Sheaf.H.{w'}
      (modulesAb ((twistEquiv (A := A) (n := n) k).functor.obj (freeP A n I))) p) := by
  classical
  have := Fintype.ofFinite I
  have h1 : Module.Finite A (Sheaf.H.{w'} (modulesAb ((twistEquiv (A := A) (n := n) k).functor.obj
      (𝟙_ (projectiveSpace A n).Modules))) p) :=
    have := finite_H_twistingSheaf.{w'} (A := A) (n := n) k p
    Module.Finite.equiv (H_twistUnitEquiv (A := A) (n := n) k p).symm
  let Φ : (I → Sheaf.H.{w'} (modulesAb ((twistEquiv (A := A) (n := n) k).functor.obj
      (𝟙_ (projectiveSpace A n).Modules))) p) →ₗ[A]
      Sheaf.H.{w'} (modulesAb ((twistEquiv (A := A) (n := n) k).functor.obj (freeP A n I))) p :=
    ∑ i, (H.linearMap A ((twistEquiv k).functor.map (ιP i)) p).comp (LinearMap.proj i)
  refine Module.Finite.of_surjective Φ fun x => ⟨fun i =>
    H.linearMap A ((twistEquiv k).functor.map (πP i)) p x, ?_⟩
  conv_rhs => rw [H_twist_free_eq k p x]
  simp [Φ, LinearMap.sum_apply]

lemma subsingleton_H_twist_free (I : Type u) [Finite I] {k : ℤ} (hk : 0 ≤ k) {p : ℕ}
    (hp : 0 < p) : Subsingleton (Sheaf.H.{w'}
      (modulesAb ((twistEquiv (A := A) (n := n) k).functor.obj (freeP A n I))) p) := by
  classical
  have := Fintype.ofFinite I
  have h1 : Subsingleton (Sheaf.H.{w'} (modulesAb ((twistEquiv (A := A) (n := n) k).functor.obj
      (𝟙_ (projectiveSpace A n).Modules))) p) :=
    have := subsingleton_H_twistingSheaf.{w'} (A := A) (n := n) hk hp
    (H_twistUnitEquiv (A := A) (n := n) k p).toEquiv.subsingleton
  refine ⟨fun x y => ?_⟩
  rw [H_twist_free_eq k p x, H_twist_free_eq k p y]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Subsingleton.elim
    (H.linearMap A ((twistEquiv k).functor.map (πP i)) p x)
    (H.linearMap A ((twistEquiv k).functor.map (πP i)) p y)]

end ProjSpace

end

end GroundTheory.Arith.SchemeCoh
