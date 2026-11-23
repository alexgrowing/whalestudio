import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsIsoFromNormalization
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.IsLocalizedModuleGermLinearPointOfPrime

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits Opposite TensorProduct

universe u

noncomputable section

namespace GlobalTheory.StalkProd

variable {X : Scheme.{u}}

def homMk {F G : X.Modules} (φ : ∀ U : X.Opens, Γ(F, U) →ₗ[Γ(X, U)] Γ(G, U))
    (hφ : ∀ {U V : X.Opens} (i : V ⟶ U) (s : Γ(F, U)),
      φ V (F.presheaf.map i.op s) = G.presheaf.map i.op (φ U s)) : F ⟶ G :=
  SheafOfModules.Hom.mk <| PresheafOfModules.homMk
    { app := fun U => AddCommGrpCat.ofHom (φ U.unop).toAddMonoidHom
      naturality := fun _ _ i => by
        ext s
        exact hφ i.unop s }
    (fun U r m => (φ U.unop).map_smul r m)

@[simp] theorem homMk_app {F G : X.Modules} (φ : ∀ U : X.Opens, Γ(F, U) →ₗ[Γ(X, U)] Γ(G, U))
    (hφ : ∀ {U V : X.Opens} (i : V ⟶ U) (s : Γ(F, U)),
      φ V (F.presheaf.map i.op s) = G.presheaf.map i.op (φ U s)) (U : X.Opens) (s : Γ(F, U)) :
    (homMk φ hφ).app U s = φ U s := rfl

section Pi

variable (E : X → Type u) [∀ x, AddCommGroup (E x)] [∀ x, Module (X.presheaf.stalk x) (E x)]

def presheafAb : TopCat.Presheaf Ab.{u} X where
  obj U := AddCommGrpCat.of (∀ x : U.unop, E x)
  map i := AddCommGrpCat.ofHom
    { toFun := fun s x => s ⟨x.1, i.unop.le x.2⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }

theorem isSheaf_presheafAb : (presheafAb E).IsSheaf := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheaf_comp (forget Ab.{u})]
  exact TopCat.Presheaf.toTypes_isSheaf X E

abbrev secModule (U : X.Opens) : Module Γ(X, U) (∀ x : U, E x) :=
  @Pi.module U (fun x : U => E x.1) Γ(X, U) _ _ fun x => Module.compHom (E x.1) (X.presheaf.germ U x.1 x.2).hom

def pi : X.Modules :=
  letI : ∀ U, Module (X.ringCatSheaf.obj.obj U) ((presheafAb E).obj U) :=
    fun U => secModule E U.unop
  { val := PresheafOfModules.ofPresheaf (presheafAb E) fun U V i r s => by
      funext x
      show X.presheaf.germ U.unop x.1 _ r • s ⟨x.1, i.unop.le x.2⟩ =
        X.presheaf.germ V.unop x.1 x.2 (X.presheaf.map i r) • s ⟨x.1, i.unop.le x.2⟩
      rw [← Quiver.Hom.op_unop i, X.presheaf.germ_res_apply i.unop x.1 x.2 r]
    isSheaf := isSheaf_presheafAb E }

variable {E}

def fam {U : X.Opens} (s : Γ(pi E, U)) : ∀ x : U, E x := s

def mk {U : X.Opens} (s : ∀ x : U, E x) : Γ(pi E, U) := s

@[simp] theorem fam_mk {U : X.Opens} (s : ∀ x : U, E x) : fam (mk s) = s := rfl

@[simp] theorem fam_smul {U : X.Opens} (r : Γ(X, U)) (s : Γ(pi E, U)) (x : U) :
    fam (r • s) x = X.presheaf.germ U x.1 x.2 r • fam s x := rfl

@[simp] theorem fam_add {U : X.Opens} (s t : Γ(pi E, U)) (x : U) :
    fam (s + t) x = fam s x + fam t x := rfl

@[simp] theorem fam_zero {U : X.Opens} (x : U) : fam (0 : Γ(pi E, U)) x = 0 := rfl

@[simp] theorem fam_res {U V : X.Opens} (i : V ⟶ U) (s : Γ(pi E, U)) (x : V) :
    fam ((pi E).presheaf.map i.op s) x = fam s ⟨x.1, i.le x.2⟩ := rfl

variable {E' : X → Type u} [∀ x, AddCommGroup (E' x)] [∀ x, Module (X.presheaf.stalk x) (E' x)]

def piMap (L : ∀ x, E x →ₗ[X.presheaf.stalk x] E' x) : pi E ⟶ pi E' :=
  homMk (fun U =>
    { toFun := fun s => mk fun x => L x.1 (fam s x)
      map_add' := fun s t => funext fun x => map_add (L x.1) _ _
      map_smul' := fun r s => funext fun x => (L x.1).map_smul _ _ })
    fun _ _ => rfl

@[simp] theorem fam_piMap_app (L : ∀ x, E x →ₗ[X.presheaf.stalk x] E' x) {U : X.Opens}
    (s : Γ(pi E, U)) (x : U) : fam ((piMap L).app U s) x = L x.1 (fam s x) := rfl

end Pi

def germs (F : X.Modules) : F ⟶ pi (fun x => (F.presheaf.stalk x : Type u)) :=
  homMk (fun U =>
    { toFun := fun s => mk fun x => F.presheaf.germ U x.1 x.2 s
      map_add' := fun s t => funext fun x => map_add _ _ _
      map_smul' := fun r s => funext fun x => QCoh.germ_smul F x.1 x.2 r s })
    fun i s => funext fun x => F.presheaf.germ_res_apply i x.1 x.2 s

@[simp] theorem fam_germs_app (F : X.Modules) {U : X.Opens} (s : Γ(F, U)) (x : U) :
    fam ((germs F).app U s) x = F.presheaf.germ U x.1 x.2 s := rfl

section Tensor

variable {Y : Scheme.{u}} (f : X ⟶ Y)

abbrev stalkAlgebra (x : X) : Algebra (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
  (f.stalkMap x).hom.toAlgebra

attribute [local instance] stalkAlgebra

variable (M : Y.Modules)

def tensorStalk (x : X) : Type u :=
  X.presheaf.stalk x ⊗[Y.presheaf.stalk (f x)] (M.presheaf.stalk (f x) : Type u)

instance (x : X) : AddCommGroup (tensorStalk f M x) :=
  inferInstanceAs (AddCommGroup (X.presheaf.stalk x ⊗[Y.presheaf.stalk (f x)]
    (M.presheaf.stalk (f x) : Type u)))

instance (x : X) : Module (X.presheaf.stalk x) (tensorStalk f M x) :=
  inferInstanceAs (Module (X.presheaf.stalk x) (X.presheaf.stalk x ⊗[Y.presheaf.stalk (f x)]
    (M.presheaf.stalk (f x) : Type u)))

def oneTmul (x : X) (m : (M.presheaf.stalk (f x) : Type u)) : tensorStalk f M x :=
  (1 : X.presheaf.stalk x) ⊗ₜ[Y.presheaf.stalk (f x)] m

theorem oneTmul_add (x : X) (m n : (M.presheaf.stalk (f x) : Type u)) :
    oneTmul f M x (m + n) = oneTmul f M x m + oneTmul f M x n :=
  TensorProduct.tmul_add _ _ _

theorem oneTmul_smul (x : X) (a : Y.presheaf.stalk (f x)) (m : (M.presheaf.stalk (f x) : Type u)) :
    oneTmul f M x (a • m) = f.stalkMap x a • oneTmul f M x m := by
  change (1 : X.presheaf.stalk x) ⊗ₜ[Y.presheaf.stalk (f x)] (a • m) =
    (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) a) •
      ((1 : X.presheaf.stalk x) ⊗ₜ[Y.presheaf.stalk (f x)] m)
  rw [algebraMap_smul, TensorProduct.tmul_smul]

theorem oneTmul_germ_smul {V : Y.Opens} (r : Γ(Y, V)) (s : Γ(M, V)) (x : X) (hx : f x ∈ V) :
    oneTmul f M x (M.presheaf.germ V (f x) hx (r • s)) =
      X.presheaf.germ (f ⁻¹ᵁ V) x hx (f.app V r) • oneTmul f M x (M.presheaf.germ V (f x) hx s) := by
  rw [QCoh.germ_smul, oneTmul_smul, Scheme.Hom.germ_stalkMap_apply]

theorem oneTmul_germ_res {U V : Y.Opens} (i : V ⟶ U) (s : Γ(M, U)) (x : X) (hx : f x ∈ V) :
    oneTmul f M x (M.presheaf.germ V (f x) hx (M.presheaf.map i.op s)) =
      oneTmul f M x (M.presheaf.germ U (f x) (i.le hx) s) := by
  rw [M.presheaf.germ_res_apply]

def toPi : M ⟶ (Scheme.Modules.pushforward f).obj (pi (tensorStalk f M)) :=
  homMk (fun V =>
    { toFun := fun s => (mk fun x => oneTmul f M x.1 (M.presheaf.germ V (f x.1) x.2 s) :
        Γ(pi (tensorStalk f M), f ⁻¹ᵁ V))
      map_add' := fun s t => funext fun x => by
        show oneTmul f M x.1 (M.presheaf.germ V (f x.1) x.2 (s + t)) = _
        rw [map_add, oneTmul_add]; rfl
      map_smul' := fun r s => funext fun x => by
        exact oneTmul_germ_smul f M r s x.1 x.2 })
    fun i s => funext fun x => oneTmul_germ_res f M i s x.1 x.2

def fromPullback : (Scheme.Modules.pullback f).obj M ⟶ pi (tensorStalk f M) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).symm (toPi f M)

def stalkUnit (x : X) : (M.presheaf.stalk (f x) : Type u) →+
    (((Scheme.Modules.pullback f).obj M).presheaf.stalk x : Type u) :=
  ((TopCat.Presheaf.stalkFunctor Ab.{u} (f x)).map
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).mapPresheaf ≫
    TopCat.Presheaf.stalkPushforward Ab.{u} f.base ((Scheme.Modules.pullback f).obj M).presheaf x).hom

theorem stalkUnit_germ (x : X) {V : Y.Opens} (hx : f x ∈ V) (s : Γ(M, V)) :
    stalkUnit f M x (M.presheaf.germ V (f x) hx s) =
      ((Scheme.Modules.pullback f).obj M).presheaf.germ (f ⁻¹ᵁ V) x hx
        (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app V s) := by
  have e1 := QCoh.stalkFunctor_map_germ ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M) (f x) hx s
  have h' := congr(ConcreteCategory.hom $(TopCat.Presheaf.stalkPushforward_germ Ab.{u} f.base
    ((Scheme.Modules.pullback f).obj M).presheaf V x hx)
    (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app V s))
  refine Eq.trans ?_ h'
  exact congrArg (TopCat.Presheaf.stalkPushforward Ab.{u} f.base _ x).hom e1

theorem stalkUnit_smul (x : X) (a : Y.presheaf.stalk (f x)) (m : (M.presheaf.stalk (f x) : Type u)) :
    stalkUnit f M x (a • m) = f.stalkMap x a • stalkUnit f M x m := by
  obtain ⟨U, hU, r, rfl⟩ := Y.presheaf.exists_germ_eq a
  obtain ⟨V, hV, s, rfl⟩ := M.presheaf.exists_germ_eq m
  have hx : f x ∈ U ⊓ V := ⟨hU, hV⟩
  rw [← Y.presheaf.germ_res_apply (homOfLE (inf_le_left : U ⊓ V ≤ U)) (f x) hx,
    ← M.presheaf.germ_res_apply (homOfLE (inf_le_right : U ⊓ V ≤ V)) (f x) hx,
    ← QCoh.germ_smul, stalkUnit_germ, stalkUnit_germ, Scheme.Hom.germ_stalkMap_apply]
  exact (congrArg _ (Scheme.Modules.Hom.app_smul _ _ _)).trans (QCoh.germ_smul _ _ _ _ _)

def stalkLift (x : X) :
    tensorStalk f M x →ₗ[X.presheaf.stalk x] (((Scheme.Modules.pullback f).obj M).presheaf.stalk x : Type u) :=
  letI : Module (Y.presheaf.stalk (f x)) (((Scheme.Modules.pullback f).obj M).presheaf.stalk x : Type u) :=
    Module.compHom _ (f.stalkMap x).hom
  haveI : IsScalarTower (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)
      (((Scheme.Modules.pullback f).obj M).presheaf.stalk x : Type u) :=
    .of_algebraMap_smul fun _ _ => rfl
  LinearMap.liftBaseChange (X.presheaf.stalk x)
    { toFun := stalkUnit f M x
      map_add' := map_add _
      map_smul' := stalkUnit_smul f M x }

variable {M} {M' : Y.Modules}

def tensorStalkMap (φ : M ⟶ M') (x : X) : tensorStalk f M x →ₗ[X.presheaf.stalk x] tensorStalk f M' x :=
  (QCoh.stalkLinear φ (f x)).baseChange (X.presheaf.stalk x)

end Tensor

end GlobalTheory.StalkProd
