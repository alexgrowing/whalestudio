import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.CechNaturality.NaturalLeray
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.ImmersionPush
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits

universe w u

noncomputable section

section Transport

variable {Y X : TopCat.{u}} {κ : Type w} {P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}}
  {P' : (Opens Y)ᵒᵖ ⥤ AddCommGrpCat.{u}}
  (φ : Opens Y → Opens X) (hφ : Monotone φ)
  (e : ∀ W, P'.obj (op W) ≃+ P.obj (op (φ W)))
  (he : ∀ {V W : Opens Y} (h : V ≤ W) (x : P'.obj (op W)),
    e V (res P' h x) = res P (hφ h) (e W x))
  (U : κ → Opens Y) (hinter : ∀ {n : ℕ} (i : Fin (n + 1) → κ), φ (inter U i) = inter (φ ∘ U) i)

def transE (n : ℕ) : Cochain P' U n →+ Cochain P (φ ∘ U) n where
  toFun σ i := res P (hinter i).ge (e _ (σ i))
  map_zero' := funext fun i => by simp
  map_add' σ τ := funext fun i => by simp

def transE' (n : ℕ) : Cochain P (φ ∘ U) n →+ Cochain P' U n where
  toFun σ i := (e _).symm (res P (hinter i).le (σ i))
  map_zero' := funext fun i => by simp
  map_add' σ τ := funext fun i => by simp

include he in
lemma transE_d (n : ℕ) (σ : Cochain P' U n) :
    transE φ e U hinter (n + 1) (d P' U n σ) = d P (φ ∘ U) n (transE φ e U hinter n σ) :=
  funext fun i => by
    simp only [transE, AddMonoidHom.coe_mk, ZeroHom.coe_mk, d_apply, map_sum, map_zsmul, he,
      res_res]

lemma transE_transE' (n : ℕ) (σ : Cochain P (φ ∘ U) n) :
    transE φ e U hinter n (transE' φ e U hinter n σ) = σ :=
  funext fun i => by
    simp only [transE, transE', AddMonoidHom.coe_mk, ZeroHom.coe_mk, AddEquiv.apply_symm_apply,
      res_res, res_refl]

lemma transE'_transE (n : ℕ) (σ : Cochain P' U n) :
    transE' φ e U hinter n (transE φ e U hinter n σ) = σ :=
  funext fun i => by
    simp only [transE, transE', AddMonoidHom.coe_mk, ZeroHom.coe_mk, res_res, res_refl,
      AddEquiv.symm_apply_apply]

include he in
lemma transE'_d (n : ℕ) (σ : Cochain P (φ ∘ U) n) :
    transE' φ e U hinter (n + 1) (d P (φ ∘ U) n σ) = d P' U n (transE' φ e U hinter n σ) := by
  conv_lhs => rw [← transE_transE' φ e U hinter n σ, ← transE_d φ hφ e he U hinter]
  rw [transE'_transE]

include he in
lemma transE_mem_coboundaries {n : ℕ} {σ : Cochain P' U n} (hσ : σ ∈ coboundaries P' U n) :
    transE φ e U hinter n σ ∈ coboundaries P (φ ∘ U) n := by
  cases n with
  | zero =>
    rw [coboundaries_zero, AddSubgroup.mem_bot] at hσ ⊢
    rw [hσ, map_zero]
  | succ n =>
    obtain ⟨τ, rfl⟩ := hσ
    exact ⟨transE φ e U hinter n τ, (transE_d φ hφ e he U hinter n τ).symm⟩

include he in
lemma transE'_mem_coboundaries {n : ℕ} {σ : Cochain P (φ ∘ U) n}
    (hσ : σ ∈ coboundaries P (φ ∘ U) n) : transE' φ e U hinter n σ ∈ coboundaries P' U n := by
  cases n with
  | zero =>
    rw [coboundaries_zero, AddSubgroup.mem_bot] at hσ ⊢
    rw [hσ, map_zero]
  | succ n =>
    obtain ⟨τ, rfl⟩ := hσ
    exact ⟨transE' φ e U hinter n τ, (transE'_d φ hφ e he U hinter n τ).symm⟩

def transCocycles (n : ℕ) : cocycles P' U n →+ cocycles P (φ ∘ U) n :=
  AddMonoidHom.codRestrict ((transE φ e U hinter n).comp (cocycles P' U n).subtype) _ fun σ => by
    rw [mem_cocycles]
    change d P (φ ∘ U) n (transE φ e U hinter n σ.1) = 0
    rw [← transE_d φ hφ e he U hinter, (mem_cocycles σ.1).1 σ.2, map_zero]

def transCocycles' (n : ℕ) : cocycles P (φ ∘ U) n →+ cocycles P' U n :=
  AddMonoidHom.codRestrict ((transE' φ e U hinter n).comp (cocycles P (φ ∘ U) n).subtype) _
    fun σ => by
      rw [mem_cocycles]
      change d P' U n (transE' φ e U hinter n σ.1) = 0
      rw [← transE'_d φ hφ e he U hinter, (mem_cocycles σ.1).1 σ.2, map_zero]

def cechHTransport (n : ℕ) : cechH P' U n ≃+ cechH P (φ ∘ U) n where
  toFun := QuotientAddGroup.map _ _ (transCocycles φ hφ e he U hinter n) fun σ hσ => by
    rw [AddSubgroup.mem_comap, AddSubgroup.mem_addSubgroupOf]
    exact transE_mem_coboundaries φ hφ e he U hinter (AddSubgroup.mem_addSubgroupOf.1 hσ)
  invFun := QuotientAddGroup.map _ _ (transCocycles' φ hφ e he U hinter n) fun σ hσ => by
    rw [AddSubgroup.mem_comap, AddSubgroup.mem_addSubgroupOf]
    exact transE'_mem_coboundaries φ hφ e he U hinter (AddSubgroup.mem_addSubgroupOf.1 hσ)
  left_inv x := by
    obtain ⟨σ, hσ, rfl⟩ := exists_cls x
    exact cls_congr U (transE'_transE φ e U hinter n σ)
      (by rw [transE'_transE]; exact hσ) hσ
  right_inv x := by
    obtain ⟨σ, hσ, rfl⟩ := exists_cls x
    exact cls_congr (φ ∘ U) (transE_transE' φ e U hinter n σ)
      (by rw [transE_transE']; exact hσ) hσ
  map_add' := map_add _

lemma cechHTransport_cls {n : ℕ} (σ : Cochain P' U n) (hσ : d P' U n σ = 0) :
    cechHTransport φ hφ e he U hinter n (cls σ hσ) =
      cls (transE φ e U hinter n σ) (by rw [← transE_d φ hφ e he U hinter, hσ, map_zero]) := rfl

lemma cechHTransport_naturality (α' : P' ⟶ P') (α : P ⟶ P)
    (hα : ∀ (W : Opens Y) (x : P'.obj (op W)), e W (α'.app (op W) x) = α.app (op (φ W)) (e W x))
    (n : ℕ) (x : cechH P' U n) :
    cechHTransport φ hφ e he U hinter n (cechHMap U α' n x) =
      cechHMap (φ ∘ U) α n (cechHTransport φ hφ e he U hinter n x) := by
  obtain ⟨σ, hσ, rfl⟩ := exists_cls x
  rw [cechHMap_cls, cechHTransport_cls, cechHTransport_cls, cechHMap_cls]
  refine cls_congr (φ ∘ U) (funext fun i => ?_) _ _
  simp only [transE, push, AddMonoidHom.coe_mk, ZeroHom.coe_mk, hα]
  exact (app_res α _ _).symm

end Transport

section Scheme

variable {X Y : Scheme.{u}} (i : X ⟶ Y)

lemma preimage_inter {κ : Type w} (U : κ → Y.Opens) {n : ℕ} (t : Fin n → κ) :
    i ⁻¹ᵁ inter (X := Y.toTopCat) U t = inter (X := X.toTopCat) (fun j => i ⁻¹ᵁ U j) t := by
  refine SetLike.ext fun x => ?_
  change i.base x ∈ inter (X := Y.toTopCat) U t ↔ _
  rw [mem_inter_iff, mem_inter_iff]
  rfl

def cechHPushforwardEquiv (F : X.Modules) {κ : Type w} (U : κ → Y.Opens) (n : ℕ) :
    cechH (modulesAb ((Scheme.Modules.pushforward i).obj F)).obj U n ≃+
      cechH (modulesAb F).obj (fun j => i ⁻¹ᵁ U j) n :=
  cechHTransport (P := (modulesAb F).obj) (P' := (modulesAb ((Scheme.Modules.pushforward i).obj F)).obj)
    (fun W => i ⁻¹ᵁ W) (Opens.map i.base).monotone (fun _ => AddEquiv.refl _) (fun _ _ => rfl) U
    (fun t => preimage_inter i U t) n

lemma cechHPushforwardEquiv_naturality (F : X.Modules) {κ : Type w} (U : κ → Y.Opens) (n : ℕ)
    (α' : (modulesAb ((Scheme.Modules.pushforward i).obj F)).obj ⟶
      (modulesAb ((Scheme.Modules.pushforward i).obj F)).obj)
    (α : (modulesAb F).obj ⟶ (modulesAb F).obj)
    (hα : ∀ (W : Y.Opens) (x : (modulesAb ((Scheme.Modules.pushforward i).obj F)).obj.obj (op W)),
      α'.app (op W) x = α.app (op (i ⁻¹ᵁ W)) x)
    (x : cechH (modulesAb ((Scheme.Modules.pushforward i).obj F)).obj U n) :
    cechHPushforwardEquiv i F U n (cechHMap U α' n x) =
      cechHMap (fun j => i ⁻¹ᵁ U j) α n (cechHPushforwardEquiv i F U n x) :=
  cechHTransport_naturality (P := (modulesAb F).obj)
    (P' := (modulesAb ((Scheme.Modules.pushforward i).obj F)).obj)
    (fun W => i ⁻¹ᵁ W) (Opens.map i.base).monotone (fun _ => AddEquiv.refl _) (fun _ _ => rfl) U
    (fun t => preimage_inter i U t) α' α hα n x

variable (A : Type u) [CommRing A] [X.Over (Spec (.of A))] [Y.Over (Spec (.of A))]
  [i.IsOver (Spec (.of A))]

attribute [local instance] algebraOfOver

include i in

lemma algebraMap_eq_appTop (a : A) :
    algebraMap A Γ(X, ⊤) a = i.appTop (algebraMap A Γ(Y, ⊤) a) := by
  change (X ↘ Spec (.of A)).appTop _ = i.appTop ((Y ↘ Spec (.of A)).appTop _)
  rw [← CategoryTheory.comp_over i (Spec (.of A)), Scheme.Hom.comp_appTop]
  rfl

lemma smulHom_pushforward_app (F : X.Modules) (a : A) (W : Y.Opens)
    (x : (modulesAb ((Scheme.Modules.pushforward i).obj F)).obj.obj (op W)) :
    (smulAbRingHom ((Scheme.Modules.pushforward i).obj F) (algebraMap A Γ(Y, ⊤) a)).hom.app (op W)
      x = (smulAbRingHom F (algebraMap A Γ(X, ⊤) a)).hom.app (op (i ⁻¹ᵁ W)) x := by
  change i.app W (restrictTop W (algebraMap A Γ(Y, ⊤) a)) • (show Γ(F, i ⁻¹ᵁ W) from x) =
    restrictTop (i ⁻¹ᵁ W) (algebraMap A Γ(X, ⊤) a) • (show Γ(F, i ⁻¹ᵁ W) from x)
  rw [algebraMap_eq_appTop i A a, restrictTop, restrictTop, app_resO]
  rfl

def cechHPushforwardLinearEquiv (F : X.Modules) {κ : Type w} (U : κ → Y.Opens) (n : ℕ) :
    cechH (modulesAb ((Scheme.Modules.pushforward i).obj F)).obj U n ≃ₗ[A]
      cechH (modulesAb F).obj (fun j => i ⁻¹ᵁ U j) n :=
  (cechHPushforwardEquiv i F U n).toLinearEquiv fun a x =>
    cechHPushforwardEquiv_naturality i F U n _ _ (fun W x => smulHom_pushforward_app i A F a W x) x

end Scheme

end

end GroundTheory.Arith.SchemeCoh
