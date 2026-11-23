import Mathlib
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ToAbSheafPreservesFiniteLimits

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits

universe t v u

noncomputable section

namespace GlobalTheory

variable {X : Scheme.{u}}

instance hasSheafify_topCat (T : TopCat.{u}) :
    HasSheafify (Opens.grothendieckTopology T) AddCommGrpCat.{u} := inferInstance

instance hasExt_sheaf_topCat (T : TopCat.{u}) :
    HasExt.{u} (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u}) := inferInstance

instance hasSheafify_scheme (X : Scheme.{u}) :
    HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u} := inferInstance

instance hasExt_sheaf_scheme (X : Scheme.{u}) :
    HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) := inferInstance

def cohOn (F : X.Modules) (U : X.Opens) (n : ℕ) : Type u :=
  Sheaf.H'.{u} ((toAbSheaf X).obj F) n U

abbrev coh (F : X.Modules) (n : ℕ) : Type u := cohOn F ⊤ n

namespace cohOn

def action (F : X.Modules) (U : X.Opens) (n : ℕ) :
    Γ(X, ⊤) →+* AddMonoid.End (Sheaf.H'.{u} ((toAbSheaf X).obj F) n U) :=
  (SiteCoh.endAction ((toAbSheaf X).obj F) n U).comp
    ((functorEndRingHom (toAbSheaf X) F).comp (smulEnd F))

lemma action_apply (F : X.Modules) (U : X.Opens) (n : ℕ) (r : Γ(X, ⊤))
    (x : Sheaf.H'.{u} ((toAbSheaf X).obj F) n U) :
    action F U n r x = SiteCoh.map ((toAbSheaf X).map (smulHom F r)) n U x :=
  SiteCoh.endAction_apply _ x

instance instAddCommGroup (F : X.Modules) (U : X.Opens) (n : ℕ) : AddCommGroup (cohOn F U n) :=
  addCommGroupOfAction (M := Sheaf.H'.{u} ((toAbSheaf X).obj F) n U) inferInstance (action F U n)

def toH' (F : X.Modules) (U : X.Opens) (n : ℕ) :
    cohOn F U n ≃+ Sheaf.H'.{u} ((toAbSheaf X).obj F) n U :=
  WithAction.toBase (action F U n)

section Module

variable (R : Type v) [CommRing R] [Algebra R Γ(X, ⊤)]

instance instModule (F : X.Modules) (U : X.Opens) (n : ℕ) : Module R (cohOn F U n) :=
  { WithAction.instModule (action F U n) R with
    smul := fun r x ↦ action F U n (algebraMap R Γ(X, ⊤) r) x }

example (F : X.Modules) (U : X.Opens) (n : ℕ) :
    instModule ℤ F U n = AddCommGroup.toIntModule (cohOn F U n) := by
  with_reducible_and_instances rfl

variable {R} in

lemma toH'_smul {F : X.Modules} {U : X.Opens} {n : ℕ} (r : R) (x : cohOn F U n) :
    toH' F U n (r • x) =
      SiteCoh.map ((toAbSheaf X).map (smulHom F (algebraMap R Γ(X, ⊤) r))) n U (toH' F U n x) :=
  (WithAction.toBase_smul (action F U n) r x).trans (action_apply F U n _ _)

instance instIsScalarTower (S : Type t) [CommRing S] [Algebra S Γ(X, ⊤)] [Algebra R S]
    [IsScalarTower R S Γ(X, ⊤)] (F : X.Modules) (U : X.Opens) (n : ℕ) :
    IsScalarTower R S (cohOn F U n) :=
  WithAction.instIsScalarTower (action F U n) R S

instance instSMulCommClass (S : Type t) [CommRing S] [Algebra S Γ(X, ⊤)]
    (F : X.Modules) (U : X.Opens) (n : ℕ) : SMulCommClass R S (cohOn F U n) :=
  WithAction.instSMulCommClass (action F U n) R S

def map {F G : X.Modules} (φ : F ⟶ G) (U : X.Opens) (n : ℕ) : cohOn F U n →ₗ[R] cohOn G U n :=
  WithAction.linearMap (action F U n) (action G U n) R
    (SiteCoh.map ((toAbSheaf X).map φ) n U).hom fun r x ↦ by
      rw [action_apply, action_apply, ← SiteCoh.map_comp_apply, ← SiteCoh.map_comp_apply,
        ← Functor.map_comp, ← Functor.map_comp, smulHom_comp]

def res (F : X.Modules) {U V : X.Opens} (h : V ≤ U) (n : ℕ) : cohOn F U n →ₗ[R] cohOn F V n :=
  WithAction.linearMap (action F U n) (action F V n) R
    (SiteCoh.res ((toAbSheaf X).obj F) n (homOfLE h)).hom fun r x ↦ by
      rw [action_apply, action_apply, SiteCoh.res_map_apply]

variable {F G H : X.Modules} {U V W : X.Opens} {n : ℕ}

lemma toH'_map (φ : F ⟶ G) (x : cohOn F U n) :
    toH' G U n (map R φ U n x) = SiteCoh.map ((toAbSheaf X).map φ) n U (toH' F U n x) := rfl

lemma toH'_res (h : V ≤ U) (x : cohOn F U n) :
    toH' F V n (res R F h n x) =
      SiteCoh.res ((toAbSheaf X).obj F) n (homOfLE h) (toH' F U n x) := rfl

lemma map_eq_map (S : Type t) [CommRing S] [Algebra S Γ(X, ⊤)] (φ : F ⟶ G) (x : cohOn F U n) :
    map R φ U n x = map S φ U n x := rfl

lemma res_eq_res (S : Type t) [CommRing S] [Algebra S Γ(X, ⊤)] (h : V ≤ U) (x : cohOn F U n) :
    res R F h n x = res S F h n x := rfl

lemma smul_eq_map (r : R) (x : cohOn F U n) :
    r • x = map R (smulHom F (algebraMap R Γ(X, ⊤) r)) U n x := rfl

@[simp] lemma map_smulHom_apply (r : Γ(X, ⊤)) (x : cohOn F U n) :
    map R (smulHom F r) U n x = r • x := rfl

variable (F U n) in

@[simp] lemma map_id : map R (𝟙 F) U n = LinearMap.id := by
  ext x
  apply (toH' F U n).injective
  rw [toH'_map, CategoryTheory.Functor.map_id, SiteCoh.map_id_apply, LinearMap.id_apply]

variable (U n) in

lemma map_comp (φ : F ⟶ G) (ψ : G ⟶ H) :
    map R (φ ≫ ψ) U n = map R ψ U n ∘ₗ map R φ U n := by
  ext x
  apply (toH' H U n).injective
  rw [LinearMap.comp_apply, toH'_map, toH'_map, toH'_map, Functor.map_comp,
    SiteCoh.map_comp_apply]

lemma map_map (φ : F ⟶ G) (ψ : G ⟶ H) (x : cohOn F U n) :
    map R ψ U n (map R φ U n x) = map R (φ ≫ ψ) U n x := by
  rw [map_comp]; rfl

variable (U n) in

lemma map_add_hom (φ ψ : F ⟶ G) : map R (φ + ψ) U n = map R φ U n + map R ψ U n := by
  ext x
  apply (toH' G U n).injective
  rw [LinearMap.add_apply, map_add, toH'_map, toH'_map, toH'_map, Functor.map_add,
    SiteCoh.map_add_apply]

variable (F G U n) in

@[simps! apply] def mapAddHom : (F ⟶ G) →+ (cohOn F U n →ₗ[R] cohOn G U n) :=
  AddMonoidHom.mk' (fun φ ↦ map R φ U n) (map_add_hom R U n)

variable (F G U n) in

@[simp] lemma map_zero_hom : map R (0 : F ⟶ G) U n = 0 := map_zero (mapAddHom R F G U n)

variable (U n) in

lemma map_neg_hom (φ : F ⟶ G) : map R (-φ) U n = -map R φ U n := map_neg (mapAddHom R F G U n) φ

variable (U n) in

lemma map_sub_hom (φ ψ : F ⟶ G) : map R (φ - ψ) U n = map R φ U n - map R ψ U n :=
  map_sub (mapAddHom R F G U n) φ ψ

variable (U n) in

lemma map_sum_hom {ι : Type t} (s : Finset ι) (φ : ι → (F ⟶ G)) :
    map R (∑ i ∈ s, φ i) U n = ∑ i ∈ s, map R (φ i) U n :=
  map_sum (mapAddHom R F G U n) φ s

variable (U n) in

lemma map_smul_hom (r : Γ(X, ⊤)) (φ : F ⟶ G) : map R (r • φ) U n = r • map R φ U n := by
  rw [smul_hom_def, map_comp]; rfl

variable (F U n) in

@[simp] lemma res_refl : res R F (le_refl U) n = LinearMap.id := by
  ext x
  apply (toH' F U n).injective
  rw [toH'_res, show homOfLE (le_refl U) = 𝟙 U from rfl, SiteCoh.res_id_apply,
    LinearMap.id_apply]

variable (F n) in

lemma res_comp_res (h : V ≤ U) (h' : W ≤ V) :
    res R F h' n ∘ₗ res R F h n = res R F (h'.trans h) n := by
  ext x
  apply (toH' F W n).injective
  rw [LinearMap.comp_apply, toH'_res, toH'_res, toH'_res, ← SiteCoh.res_comp_apply,
    homOfLE_comp]

@[simp] lemma res_res (h : V ≤ U) (h' : W ≤ V) (x : cohOn F U n) :
    res R F h' n (res R F h n x) = res R F (h'.trans h) n x :=
  LinearMap.congr_fun (res_comp_res R F n h h') x

lemma res_map (φ : F ⟶ G) (h : V ≤ U) (x : cohOn F U n) :
    res R G h n (map R φ U n x) = map R φ V n (res R F h n x) := by
  apply (toH' G V n).injective
  rw [toH'_res, toH'_map, toH'_map, toH'_res, SiteCoh.res_map_apply]

variable (n) in

lemma res_comp_map (φ : F ⟶ G) (h : V ≤ U) :
    res R G h n ∘ₗ map R φ U n = map R φ V n ∘ₗ res R F h n :=
  LinearMap.ext (res_map R φ h)

variable (U n) in

@[simps! apply symm_apply] def mapIso (e : F ≅ G) : cohOn F U n ≃ₗ[R] cohOn G U n :=
  LinearEquiv.ofLinearMap (map R e.hom U n) (map R e.inv U n)
    (by rw [← map_comp, e.inv_hom_id, map_id]) (by rw [← map_comp, e.hom_inv_id, map_id])

variable (U n) in

lemma map_bijective (φ : F ⟶ G) [IsIso φ] : Function.Bijective (map R φ U n) :=
  (mapIso R U n (asIso φ)).bijective

variable (F n) in

@[simps! apply symm_apply] def congrOpens (h : U = V) : cohOn F U n ≃ₗ[R] cohOn F V n :=
  LinearEquiv.ofLinearMap (res R F h.ge n) (res R F h.le n)
    (by rw [res_comp_res, res_refl]) (by rw [res_comp_res, res_refl])

end Module

abbrev moduleOfRingHom {R : Type v} [CommRing R] (f : R →+* Γ(X, ⊤)) (F : X.Modules)
    (U : X.Opens) (n : ℕ) : Module R (cohOn F U n) :=
  letI := f.toAlgebra
  instModule R F U n

lemma moduleOfRingHom_smul {R : Type v} [CommRing R] (f : R →+* Γ(X, ⊤)) {F : X.Modules}
    {U : X.Opens} {n : ℕ} (r : R) (x : cohOn F U n) :
    letI := moduleOfRingHom f F U n
    r • x = f r • x := rfl

lemma subsingleton_of_isZero {F : X.Modules} (h : IsZero F) (U : X.Opens) (n : ℕ) :
    Subsingleton (cohOn F U n) :=
  subsingleton_of_forall_eq 0 fun x ↦ by
    have h₁ : map ℤ (𝟙 F) U n x = x := by rw [map_id]; rfl
    rw [← h₁, h.eq_of_src (𝟙 F) 0, map_zero_hom]; rfl

open ZeroObject in

instance subsingleton_zero (U : X.Opens) (n : ℕ) : Subsingleton (cohOn (0 : X.Modules) U n) :=
  subsingleton_of_isZero (isZero_zero _) U n

instance subsingleton_bot (F : X.Modules) (n : ℕ) : Subsingleton (cohOn F ⊥ n) :=
  haveI : Subsingleton (((SiteCoh.freeSheaf (Opens.grothendieckTopology X)).obj
      (⊥ : X.Opens)).obj.obj (op ⊥)) :=
    AddCommGrpCat.subsingleton_of_isZero
      (TopCat.Sheaf.isTerminalOfEmpty (X := X.toPresheafedSpace.carrier) _).isZero
  SiteCoh.subsingleton_of_subsingleton_freeSheaf ((toAbSheaf X).obj F) n ⊥

lemma subsingleton_of_injective (F : X.Modules) [Injective ((toAbSheaf X).obj F)] (U : X.Opens)
    (n : ℕ) : Subsingleton (cohOn F U (n + 1)) :=
  SiteCoh.subsingleton_of_injective ((toAbSheaf X).obj F) n U

section Products

variable (R : Type v) [CommRing R] [Algebra R Γ(X, ⊤)] {ι : Type t} (U : X.Opens) (n : ℕ)

@[simps! apply symm_apply] def biconeEquiv [Fintype ι] {F : ι → X.Modules} {c : Bicone F}
    (hc : c.IsBilimit) : cohOn c.pt U n ≃ₗ[R] ∀ i, cohOn (F i) U n :=
  LinearEquiv.ofLinearMap (LinearMap.pi fun i ↦ map R (c.π i) U n)
    (∑ i, map R (c.ι i) U n ∘ₗ LinearMap.proj i)
    (by
      classical
      refine LinearMap.ext fun x ↦ funext fun i ↦ ?_
      simp only [LinearMap.comp_apply, LinearMap.pi_apply, LinearMap.sum_apply, map_sum,
        LinearMap.proj_apply, LinearMap.id_apply, map_map]
      rw [Finset.sum_eq_single i]
      · rw [bicone_ι_π_self, map_id, LinearMap.id_apply]
      · intro j _ hj
        rw [bicone_ι_π_ne _ hj, map_zero_hom, LinearMap.zero_apply]
      · simp)
    (by
      refine LinearMap.ext fun x ↦ ?_
      simp only [LinearMap.comp_apply, LinearMap.pi_apply, LinearMap.sum_apply,
        LinearMap.proj_apply, LinearMap.id_apply, map_map]
      rw [← LinearMap.sum_apply, ← map_sum_hom, IsBilimit.total hc, map_id, LinearMap.id_apply])

lemma pi_map_bijective [Finite ι] {F : ι → X.Modules} {c : Fan F} (hc : IsLimit c) :
    Function.Bijective (LinearMap.pi fun i ↦ map R (c.proj i) U n) := by
  cases nonempty_fintype ι
  exact (biconeEquiv R U n (biconeIsBilimitOfLimitConeOfIsLimit hc)).bijective

def fanEquiv [Finite ι] {F : ι → X.Modules} {c : Fan F} (hc : IsLimit c) :
    cohOn c.pt U n ≃ₗ[R] ∀ i, cohOn (F i) U n :=
  LinearEquiv.ofBijective _ (pi_map_bijective R U n hc)

@[simp] lemma fanEquiv_apply [Finite ι] {F : ι → X.Modules} {c : Fan F} (hc : IsLimit c)
    (x : cohOn c.pt U n) (i : ι) : fanEquiv R U n hc x i = map R (c.proj i) U n x := rfl

def piEquiv [Finite ι] (F : ι → X.Modules) : cohOn (∏ᶜ F) U n ≃ₗ[R] ∀ i, cohOn (F i) U n :=
  fanEquiv R U n (productIsProduct F)

@[simp] lemma piEquiv_apply [Finite ι] (F : ι → X.Modules) (x : cohOn (∏ᶜ F) U n) (i : ι) :
    piEquiv R U n F x i = map R (Pi.π F i) U n x := rfl

attribute [local instance] Abelian.hasFiniteBiproducts

def biproductEquiv [Finite ι] (F : ι → X.Modules) :
    cohOn (⨁ F) U n ≃ₗ[R] ∀ i, cohOn (F i) U n :=
  fanEquiv R U n (c := Fan.mk (⨁ F) (biproduct.π F)) (biproduct.isLimit F)

@[simp] lemma biproductEquiv_apply [Finite ι] (F : ι → X.Modules) (x : cohOn (⨁ F) U n) (i : ι) :
    biproductEquiv R U n F x i = map R (biproduct.π F i) U n x := rfl

@[simps! apply symm_apply] def biprodEquiv (F G : X.Modules) :
    cohOn (F ⊞ G) U n ≃ₗ[R] cohOn F U n × cohOn G U n :=
  LinearEquiv.ofLinearMap ((map R biprod.fst U n).prod (map R biprod.snd U n))
    ((map R biprod.inl U n).coprod (map R biprod.inr U n))
    (by
      refine LinearMap.ext fun x ↦ Prod.ext ?_ ?_ <;>
      simp [map_map])
    (by
      rw [LinearMap.coprod_comp_prod, ← map_comp, ← map_comp, ← map_add_hom, biprod.total,
        map_id])

end Products
end cohOn

def sectionsOn (F : X.Modules) (U : X.Opens) : Type u := Γ(F, U)

namespace sectionsOn

def action (F : X.Modules) (U : X.Opens) : Γ(X, ⊤) →+* AddMonoid.End Γ(F, U) :=
  (Module.toAddMonoidEnd Γ(X, U) Γ(F, U)).comp (restrictGlobal X U)

lemma action_apply (F : X.Modules) (U : X.Opens) (r : Γ(X, ⊤)) (x : Γ(F, U)) :
    action F U r x = restrictGlobal X U r • x := rfl

instance instAddCommGroup (F : X.Modules) (U : X.Opens) : AddCommGroup (sectionsOn F U) :=
  addCommGroupOfAction (M := Γ(F, U)) inferInstance (action F U)

def toΓ (F : X.Modules) (U : X.Opens) : sectionsOn F U ≃+ Γ(F, U) := WithAction.toBase (action F U)

variable (R : Type v) [CommRing R] [Algebra R Γ(X, ⊤)]

instance instModule (F : X.Modules) (U : X.Opens) : Module R (sectionsOn F U) :=
  { WithAction.instModule (action F U) R with
    smul := fun r x ↦ action F U (algebraMap R Γ(X, ⊤) r) x }

example (F : X.Modules) (U : X.Opens) :
    instModule ℤ F U = AddCommGroup.toIntModule (sectionsOn F U) := by
  with_reducible_and_instances rfl

variable {R} in

lemma toΓ_smul {F : X.Modules} {U : X.Opens} (r : R) (x : sectionsOn F U) :
    toΓ F U (r • x) = restrictGlobal X U (algebraMap R Γ(X, ⊤) r) • toΓ F U x := rfl

instance instIsScalarTower (S : Type t) [CommRing S] [Algebra S Γ(X, ⊤)] [Algebra R S]
    [IsScalarTower R S Γ(X, ⊤)] (F : X.Modules) (U : X.Opens) : IsScalarTower R S (sectionsOn F U) :=
  WithAction.instIsScalarTower (action F U) R S

instance instSMulCommClass (S : Type t) [CommRing S] [Algebra S Γ(X, ⊤)]
    (F : X.Modules) (U : X.Opens) : SMulCommClass R S (sectionsOn F U) :=
  WithAction.instSMulCommClass (action F U) R S

def map {F G : X.Modules} (φ : F ⟶ G) (U : X.Opens) : sectionsOn F U →ₗ[R] sectionsOn G U :=
  WithAction.linearMap (action F U) (action G U) R (φ.app U).hom
    fun r x ↦ φ.app_smul (restrictGlobal X U r) x

def res (F : X.Modules) {U V : X.Opens} (h : V ≤ U) : sectionsOn F U →ₗ[R] sectionsOn F V :=
  WithAction.linearMap (action F U) (action F V) R (F.presheaf.map (homOfLE h).op).hom
    fun r x ↦ by rw [action_apply, action_apply, F.map_smul, map_restrictGlobal]

variable {F G H : X.Modules} {U V W : X.Opens}

@[simp] lemma toΓ_map (φ : F ⟶ G) (x : sectionsOn F U) :
    toΓ G U (map R φ U x) = φ.app U (toΓ F U x) := rfl

@[simp] lemma toΓ_res (h : V ≤ U) (x : sectionsOn F U) :
    toΓ F V (res R F h x) = F.presheaf.map (homOfLE h).op (toΓ F U x) := rfl

variable (F U) in

@[simp] lemma map_id : map R (𝟙 F) U = LinearMap.id := rfl

variable (U) in

lemma map_comp (φ : F ⟶ G) (ψ : G ⟶ H) : map R (φ ≫ ψ) U = map R ψ U ∘ₗ map R φ U := rfl

variable (U) in

lemma map_add_hom (φ ψ : F ⟶ G) : map R (φ + ψ) U = map R φ U + map R ψ U := rfl

variable (F U) in

@[simp] lemma res_refl : res R F (le_refl U) = LinearMap.id := by
  ext x
  apply (toΓ F U).injective
  rw [toΓ_res, show homOfLE (le_refl U) = 𝟙 U from rfl, op_id, CategoryTheory.Functor.map_id]
  rfl

variable (F) in

lemma res_comp_res (h : V ≤ U) (h' : W ≤ V) : res R F h' ∘ₗ res R F h = res R F (h'.trans h) := by
  ext x
  apply (toΓ F W).injective
  rw [LinearMap.comp_apply, toΓ_res, toΓ_res, toΓ_res, ← ConcreteCategory.comp_apply,
    ← Functor.map_comp]
  rfl

lemma res_map (φ : F ⟶ G) (h : V ≤ U) (x : sectionsOn F U) :
    res R G h (map R φ U x) = map R φ V (res R F h x) :=
  (ConcreteCategory.congr_hom (φ.mapPresheaf.naturality (homOfLE h).op) x).symm

variable (F U) in

def equivOfSMul [Module R Γ(F, U)]
    (h : ∀ (r : R) (x : Γ(F, U)), r • x = restrictGlobal X U (algebraMap R Γ(X, ⊤) r) • x) :
    sectionsOn F U ≃ₗ[R] Γ(F, U) :=
  { toΓ F U with map_smul' := fun r x ↦ (toΓ_smul r x).trans (h r _).symm }

@[simp] lemma equivOfSMul_apply [Module R Γ(F, U)]
    (h : ∀ (r : R) (x : Γ(F, U)), r • x = restrictGlobal X U (algebraMap R Γ(X, ⊤) r) • x)
    (x : sectionsOn F U) : equivOfSMul R F U h x = toΓ F U x := rfl

variable (F) in

def topEquiv : sectionsOn F ⊤ ≃ₗ[Γ(X, ⊤)] Γ(F, ⊤) :=
  equivOfSMul Γ(X, ⊤) F ⊤ fun r x ↦ by rw [restrictGlobal_top]; rfl

def specEquiv {A : CommRingCat.{u}} (F : (Spec A).Modules) (U : (Spec A).Opens) :
    sectionsOn F U ≃ₗ[A] Γ(F, U) :=
  equivOfSMul A F U fun r x ↦ by
    rw [Scheme.Modules.smul_Spec_def]
    congr 1

end sectionsOn

namespace cohOn

variable (R : Type v) [CommRing R] [Algebra R Γ(X, ⊤)]

def zeroEquiv (F : X.Modules) (U : X.Opens) : cohOn F U 0 ≃ₗ[R] sectionsOn F U :=
  WithAction.linearEquiv (action F U 0) (sectionsOn.action F U) R
    (SiteCoh.zeroEquiv ((toAbSheaf X).obj F) U) fun r x ↦ by
      rw [action_apply]
      exact SiteCoh.zeroEquiv_map ((toAbSheaf X).map (smulHom F r)) U x

variable {F G : X.Modules} {U V : X.Opens}

lemma toΓ_zeroEquiv (x : cohOn F U 0) :
    sectionsOn.toΓ F U (zeroEquiv R F U x) =
      SiteCoh.zeroEquiv ((toAbSheaf X).obj F) U (toH' F U 0 x) := rfl

lemma zeroEquiv_map (φ : F ⟶ G) (x : cohOn F U 0) :
    zeroEquiv R G U (map R φ U 0 x) = sectionsOn.map R φ U (zeroEquiv R F U x) :=
  SiteCoh.zeroEquiv_map ((toAbSheaf X).map φ) U (toH' F U 0 x)

lemma zeroEquiv_res (h : V ≤ U) (x : cohOn F U 0) :
    zeroEquiv R F V (res R F h 0 x) = sectionsOn.res R F h (zeroEquiv R F U x) :=
  SiteCoh.zeroEquiv_res ((toAbSheaf X).obj F) (homOfLE h) (toH' F U 0 x)

variable (F U) in

def zeroAddEquiv : cohOn F U 0 ≃+ Γ(F, U) :=
  (zeroEquiv ℤ F U).toAddEquiv.trans (sectionsOn.toΓ F U)

lemma zeroAddEquiv_smul (r : R) (x : cohOn F U 0) :
    zeroAddEquiv F U (r • x) = restrictGlobal X U (algebraMap R Γ(X, ⊤) r) • zeroAddEquiv F U x :=
  congrArg (sectionsOn.toΓ F U) ((zeroEquiv R F U).map_smul r x)

def zeroEquivSpec {A : CommRingCat.{u}} (F : (Spec A).Modules) (U : (Spec A).Opens) :
    cohOn F U 0 ≃ₗ[A] Γ(F, U) :=
  (zeroEquiv A F U).trans (sectionsOn.specEquiv F U)

end cohOn

abbrev structureModule (X : Scheme.{u}) : X.Modules := SheafOfModules.unit X.ringCatSheaf

def structureModuleΓEquiv (X : Scheme.{u}) (U : X.Opens) :
    Γ(structureModule X, U) ≃ₗ[Γ(X, U)] Γ(X, U) where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

namespace coh

def zeroEquiv (F : X.Modules) : coh F 0 ≃ₗ[Γ(X, ⊤)] Γ(F, ⊤) :=
  (cohOn.zeroEquiv Γ(X, ⊤) F ⊤).trans (sectionsOn.topEquiv F)

lemma zeroEquiv_map {F G : X.Modules} (φ : F ⟶ G) (x : coh F 0) :
    zeroEquiv G (cohOn.map Γ(X, ⊤) φ ⊤ 0 x) = φ.app ⊤ (zeroEquiv F x) :=
  congrArg (sectionsOn.toΓ G ⊤) (cohOn.zeroEquiv_map Γ(X, ⊤) φ x)

def toH (F : X.Modules) (n : ℕ) : coh F n ≃+ Sheaf.H.{u} ((toAbSheaf X).obj F) n :=
  (cohOn.toH' F ⊤ n).trans (SiteCoh.terminalEquiv ((toAbSheaf X).obj F) n isTerminalTop)

lemma toH_map (R : Type v) [CommRing R] [Algebra R Γ(X, ⊤)] {F G : X.Modules} (φ : F ⟶ G)
    (n : ℕ) (x : coh F n) :
    toH G n (cohOn.map R φ ⊤ n x) = Sheaf.H.map ((toAbSheaf X).map φ) n (toH F n x) :=
  SiteCoh.terminalEquiv_map ((toAbSheaf X).map φ) n isTerminalTop (cohOn.toH' F ⊤ n x)

lemma equiv₀_toH (F : X.Modules) (x : coh F 0) :
    Sheaf.H.equiv₀ ((toAbSheaf X).obj F) isTerminalTop (toH F 0 x) = zeroEquiv F x :=
  SiteCoh.equiv₀_terminalEquiv ((toAbSheaf X).obj F) isTerminalTop (cohOn.toH' F ⊤ 0 x)

def zeroUnitEquiv (X : Scheme.{u}) :
    coh (structureModule X) 0 ≃ₗ[Γ(X, ⊤)] Γ(X, ⊤) :=
  (zeroEquiv (structureModule X)).trans (structureModuleΓEquiv X ⊤)

def zeroUnitSpecEquiv (A : CommRingCat.{u}) :
    coh (structureModule (Spec A)) 0 ≃ₗ[A] A :=
  ((zeroUnitEquiv (Spec A)).restrictScalars A).trans
    (LinearEquiv.ofBijective (Algebra.linearMap A Γ(Spec A, ⊤)) (by
      have h : ⇑(Algebra.linearMap A Γ(Spec A, ⊤)) = (Scheme.ΓSpecIso A).inv :=
        funext fun r ↦ restrictGlobal_top ((Scheme.ΓSpecIso A).inv r)
      rw [h]
      exact ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso A).inv)).symm

def zeroTildeEquiv {A : CommRingCat.{u}} (M : ModuleCat.{u} A) : coh (tilde M) 0 ≃ₗ[A] M :=
  (cohOn.zeroEquivSpec (tilde M) ⊤).trans (tilde.isoTop M).toLinearEquiv.symm

end coh

section Functors

variable (R : Type v) [CommRing R] [Algebra R Γ(X, ⊤)]

@[simps] def cohOnFunctor (U : X.Opens) (n : ℕ) : X.Modules ⥤ ModuleCat.{u} R where
  obj F := ModuleCat.of R (cohOn F U n)
  map φ := ModuleCat.ofHom (cohOn.map R φ U n)
  map_id F := by rw [cohOn.map_id]; rfl
  map_comp φ ψ := by rw [cohOn.map_comp]; rfl

instance cohOnFunctor_additive (U : X.Opens) (n : ℕ) : (cohOnFunctor R U n).Additive where
  map_add {_ _ φ ψ} := ModuleCat.hom_ext (cohOn.map_add_hom R U n φ ψ)

@[simps] def cohPresheaf (F : X.Modules) (n : ℕ) : X.Opensᵒᵖ ⥤ ModuleCat.{u} R where
  obj U := ModuleCat.of R (cohOn F U.unop n)
  map i := ModuleCat.ofHom (cohOn.res R F i.unop.le n)
  map_id U := ModuleCat.hom_ext (cohOn.res_refl R F U.unop n)
  map_comp i j := ModuleCat.hom_ext (cohOn.res_comp_res R F n i.unop.le j.unop.le).symm

@[simps] def sectionsOnFunctor (U : X.Opens) : X.Modules ⥤ ModuleCat.{u} R where
  obj F := ModuleCat.of R (sectionsOn F U)
  map φ := ModuleCat.ofHom (sectionsOn.map R φ U)
  map_id _ := rfl
  map_comp _ _ := rfl

instance sectionsOnFunctor_additive (U : X.Opens) : (sectionsOnFunctor R U).Additive where
  map_add := rfl

@[simps] def sectionsPresheaf (F : X.Modules) : X.Opensᵒᵖ ⥤ ModuleCat.{u} R where
  obj U := ModuleCat.of R (sectionsOn F U.unop)
  map i := ModuleCat.ofHom (sectionsOn.res R F i.unop.le)
  map_id U := ModuleCat.hom_ext (sectionsOn.res_refl R F U.unop)
  map_comp i j := ModuleCat.hom_ext (sectionsOn.res_comp_res R F i.unop.le j.unop.le).symm

end Functors

abbrev algebraΓOfHom {R : Type u} [CommRing R] (f : X ⟶ Spec (.of R)) : Algebra R Γ(X, ⊤) :=
  ((Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop).hom.toAlgebra

lemma algebraΓOfHom_algebraMap {R : Type u} [CommRing R] (f : X ⟶ Spec (.of R)) (r : R) :
    letI := algebraΓOfHom f
    algebraMap R Γ(X, ⊤) r = f.appTop ((Scheme.ΓSpecIso (.of R)).inv r) := rfl

abbrev algebraΓSpec (A : CommRingCat.{u}) : Algebra A Γ(Spec A, ⊤) := inferInstance

lemma algebraΓOfHom_id (R : Type u) [CommRing R] :
    algebraΓOfHom (𝟙 (Spec (.of R))) = algebraΓSpec (.of R) :=
  Algebra.algebra_ext _ _ fun r ↦ (restrictGlobal_top ((Scheme.ΓSpecIso (.of R)).inv r)).symm

abbrev algebraΓOfOver (R : Type u) [CommRing R] (X : Scheme.{u}) [X.Over (Spec (.of R))] :
    Algebra R Γ(X, ⊤) :=
  algebraΓOfHom (X ↘ Spec (.of R))

namespace OverSpec

scoped[GlobalTheory.OverSpec] attribute [instance 50] GlobalTheory.algebraΓOfOver

example (R : Type u) [CommRing R] [X.Over (Spec (.of R))] (F : X.Modules) (n : ℕ) :
    Module R (coh F n) := inferInstance

end OverSpec

def hdim (k : Type v) [Field k] [Algebra k Γ(X, ⊤)] (F : X.Modules) (n : ℕ) : ℕ :=
  Module.finrank k (coh F n)

section hdim

variable (k : Type v) [Field k] [Algebra k Γ(X, ⊤)] {F G : X.Modules} (n : ℕ)

lemma hdim_def (F : X.Modules) : hdim k F n = Module.finrank k (coh F n) := rfl

lemma hdim_eq_rank [Module.Finite k (coh F n)] :
    (hdim k F n : Cardinal) = Module.rank k (coh F n) :=
  Module.finrank_eq_rank k _

lemma hdim_eq_zero_iff [Module.Finite k (coh F n)] : hdim k F n = 0 ↔ Subsingleton (coh F n) :=
  Module.finrank_zero_iff

lemma hdim_eq_zero_of_subsingleton [Subsingleton (coh F n)] : hdim k F n = 0 :=
  Module.finrank_zero_of_subsingleton

lemma hdim_congr (e : F ≅ G) : hdim k F n = hdim k G n :=
  (cohOn.mapIso k ⊤ n e).finrank_eq

lemma hdim_biprod [Module.Finite k (coh F n)] [Module.Finite k (coh G n)] :
    hdim k (F ⊞ G) n = hdim k F n + hdim k G n :=
  (cohOn.biprodEquiv k ⊤ n F G).finrank_eq.trans Module.finrank_prod

lemma hdim_pi {ι : Type t} [Fintype ι] (F : ι → X.Modules) [∀ i, Module.Finite k (coh (F i) n)] :
    hdim k (∏ᶜ F) n = ∑ i, hdim k (F i) n :=
  (cohOn.piEquiv k ⊤ n F).finrank_eq.trans (Module.finrank_pi_fintype k)

lemma hdim_zero (F : X.Modules) : hdim k F 0 = Module.finrank k (sectionsOn F ⊤) :=
  (cohOn.zeroEquiv k F ⊤).finrank_eq

end hdim

instance cohOn.finite_biprod (R : Type v) [CommRing R] [Algebra R Γ(X, ⊤)] (F G : X.Modules)
    (U : X.Opens) (n : ℕ) [Module.Finite R (cohOn F U n)] [Module.Finite R (cohOn G U n)] :
    Module.Finite R (cohOn (F ⊞ G) U n) :=
  Module.Finite.equiv (cohOn.biprodEquiv R U n F G).symm

instance cohOn.finite_pi (R : Type v) [CommRing R] [Algebra R Γ(X, ⊤)] {ι : Type t} [Finite ι]
    (F : ι → X.Modules) (U : X.Opens) (n : ℕ) [∀ i, Module.Finite R (cohOn (F i) U n)] :
    Module.Finite R (cohOn (∏ᶜ F) U n) :=
  Module.Finite.equiv (cohOn.piEquiv R U n F).symm

example (k : Type u) [Field k] :
    letI : Algebra k Γ(Spec (.of k), ⊤) := algebraΓSpec (.of k)
    Module.Finite k (coh (structureModule (Spec (.of k))) 0) ∧
      hdim k (structureModule (Spec (.of k))) 0 = 1 :=
  letI : Algebra k Γ(Spec (.of k), ⊤) := algebraΓSpec (.of k)
  ⟨Module.Finite.equiv (coh.zeroUnitSpecEquiv (.of k)).symm,
    (coh.zeroUnitSpecEquiv (.of k)).finrank_eq.trans (Module.finrank_self k)⟩

example : Nontrivial (coh (structureModule (Spec (.of ℤ))) 0) :=
  (coh.zeroUnitSpecEquiv (.of ℤ)).toEquiv.nontrivial

example (F : X.Modules) (U : X.Opens) (n : ℕ) (x : cohOn F U n) :
    cohOn.map ℤ (-𝟙 F) U n x = -x := by
  rw [cohOn.map_neg_hom, cohOn.map_id]; rfl

end GlobalTheory
