import PositivityTheory.AutomorphicForms.PublishedInputs.CyclicBaseChange.SConjSpaceC
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFinsetDefiniteUnitaryDoubleCosets

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep UpperTheory.V.Af

namespace UpperTheory.CBC.GaloisActionOnAdeles

variable {M : Type} [Field M]

theorem isometry_withAbs (τ : M ≃+* M) (v w : InfinitePlace M) (h : ∀ x, w (τ x) = v x) :
    Isometry (WithAbs.congr v.1 w.1 τ) := by
  refine AddMonoidHomClass.isometry_of_norm (WithAbs.congr v.1 w.1 τ) fun x => ?_
  exact h _

def locMap (τ : M ≃+* M) (v w : InfinitePlace M) (h : ∀ x, w (τ x) = v x) : v.Completion →+* w.Completion :=
  (InfinitePlace.Completion.equiv w).symm.toRingHom.comp
    ((UniformSpace.Completion.mapRingHom (WithAbs.congr v.1 w.1 τ).toRingHom
      (isometry_withAbs τ v w h).continuous).comp (InfinitePlace.Completion.equiv v).toRingHom)

theorem continuous_locMap (τ : M ≃+* M) (v w : InfinitePlace M) (h : ∀ x, w (τ x) = v x) :
    Continuous (locMap τ v w h) :=
  (InfinitePlace.Completion.continuous_ofCompletion w).comp
    ((UniformSpace.Completion.continuous_map).comp (InfinitePlace.Completion.continuous_toCompletion v))

theorem locMap_coe (τ : M ≃+* M) (v w : InfinitePlace M) (h : ∀ x, w (τ x) = v x) (x : M) :
    locMap τ v w h (x : v.Completion) = ((τ x : M) : w.Completion) := by
  change InfinitePlace.Completion.ofCompletion ((UniformSpace.Completion.mapRingHom (WithAbs.congr v.1 w.1 τ).toRingHom
    (isometry_withAbs τ v w h).continuous) ((WithAbs.toAbs v.1 x : WithAbs v.1) : v.1.Completion)) = _
  exact congrArg InfinitePlace.Completion.ofCompletion (UniformSpace.Completion.mapRingHom_coe _ _)

theorem locMap_comp (τ τ' : M ≃+* M) (u v w : InfinitePlace M) (h : ∀ x, v (τ x) = u x) (h' : ∀ x, w (τ' x) = v x)
    (h'' : ∀ x, w ((τ.trans τ') x) = u x) (y : u.Completion) :
    locMap τ' v w h' (locMap τ u v h y) = locMap (τ.trans τ') u w h'' y := by
  induction y using InfinitePlace.Completion.induction_on with
  | hp => exact isClosed_eq ((continuous_locMap _ _ _ _).comp (continuous_locMap _ _ _ _)) (continuous_locMap _ _ _ _)
  | ih a =>
    have e1 := locMap_coe τ u v h (WithAbs.equiv u.1 a)
    have e2 := locMap_coe τ' v w h' (τ (WithAbs.equiv u.1 a))
    have e3 := locMap_coe (τ.trans τ') u w h'' (WithAbs.equiv u.1 a)
    change locMap τ' v w h' (locMap τ u v h (WithAbs.equiv u.1 a : u.Completion)) = _
    rw [e1, e2]
    change _ = locMap (τ.trans τ') u w h'' (WithAbs.equiv u.1 a : u.Completion)
    rw [e3]
    rfl

theorem locMap_eq_self (τ : M ≃+* M) (hτ : ∀ x, τ x = x) (u : InfinitePlace M) (h : ∀ x, u (τ x) = u x)
    (y : u.Completion) : locMap τ u u h y = y := by
  induction y using InfinitePlace.Completion.induction_on with
  | hp => exact isClosed_eq (continuous_locMap _ _ _ _) continuous_id
  | ih a =>
    change locMap _ u u h (WithAbs.equiv u.1 a : u.Completion) = _
    rw [locMap_coe, hτ]
    rfl

def placePerm (σ : M ≃+* M) : InfinitePlace M ≃ InfinitePlace M where
  toFun w := w.comap σ.symm.toRingHom
  invFun w := w.comap σ.toRingHom
  left_inv w := InfinitePlace.ext _ _ fun x => by
    change ((w.comap σ.symm.toRingHom).comap σ.toRingHom) x = w x
    rw [InfinitePlace.comap_apply, InfinitePlace.comap_apply]
    simp
  right_inv w := InfinitePlace.ext _ _ fun x => by
    change ((w.comap σ.toRingHom).comap σ.symm.toRingHom) x = w x
    rw [InfinitePlace.comap_apply, InfinitePlace.comap_apply]
    simp

theorem placePerm_apply (σ : M ≃+* M) (w : InfinitePlace M) (x : M) : placePerm σ w (σ x) = w x := by
  rw [show placePerm σ w = w.comap σ.symm.toRingHom from rfl, InfinitePlace.comap_apply]
  simp

theorem placePerm_symm_apply (σ : M ≃+* M) (w : InfinitePlace M) (x : M) : w (σ.symm x) = placePerm σ w x := by
  rw [← placePerm_apply σ w (σ.symm x), RingEquiv.apply_symm_apply]

def locEquiv (σ : M ≃+* M) (w : InfinitePlace M) : w.Completion ≃+* (placePerm σ w).Completion where
  __ := locMap σ w (placePerm σ w) (placePerm_apply σ w)
  invFun := locMap σ.symm (placePerm σ w) w (placePerm_symm_apply σ w)
  left_inv y := by
    change locMap σ.symm (placePerm σ w) w (placePerm_symm_apply σ w)
      (locMap σ w (placePerm σ w) (placePerm_apply σ w) y) = y
    rw [locMap_comp σ σ.symm w (placePerm σ w) w _ _ (fun x => by simp)]
    exact locMap_eq_self _ (fun x => by simp) _ _ y
  right_inv y := by
    change locMap σ w (placePerm σ w) (placePerm_apply σ w)
      (locMap σ.symm (placePerm σ w) w (placePerm_symm_apply σ w) y) = y
    rw [locMap_comp σ.symm σ (placePerm σ w) w (placePerm σ w) _ _ (fun x => by simp)]
    exact locMap_eq_self _ (fun x => by simp) _ _ y

theorem continuous_locEquiv (σ : M ≃+* M) (w : InfinitePlace M) : Continuous (locEquiv σ w) :=
  continuous_locMap σ w (placePerm σ w) (placePerm_apply σ w)

def infEquiv (σ : M ≃+* M) : InfiniteAdeleRing M ≃+* InfiniteAdeleRing M :=
  (RingEquiv.piCongrRight fun w => locEquiv σ w).trans
    (RingEquiv.piCongrLeft (fun v : InfinitePlace M => v.Completion) (placePerm σ))

theorem continuous_infEquiv (σ : M ≃+* M) : Continuous (infEquiv σ) :=
  (Homeomorph.piCongrLeft (Y := fun v : InfinitePlace M => v.Completion) (placePerm σ)).continuous.comp
    (continuous_pi fun w => (continuous_locEquiv σ w).comp (continuous_apply w))

theorem infEquiv_algebraMap (σ : M ≃+* M) (x : M) :
    infEquiv σ (algebraMap M (InfiniteAdeleRing M) x) = algebraMap M (InfiniteAdeleRing M) (σ x) := by
  funext v
  obtain ⟨w, rfl⟩ := (placePerm σ).surjective v
  change (Equiv.piCongrLeft (fun v : InfinitePlace M => v.Completion) (placePerm σ)
    (fun w => locEquiv σ w (algebraMap M (InfiniteAdeleRing M) x w))) (placePerm σ w) = _
  rw [Equiv.piCongrLeft_apply_apply]
  exact locMap_coe σ w (placePerm σ w) (placePerm_apply σ w) x

variable [NumberField M]

theorem conjFin_symm_conjFin (σ : M ≃+* M) (y : Af M) : conjFin σ.symm (conjFin σ y) = y := by
  have := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField M
  refine congrFun ((GlobalTheory.AdeleCharTwist.denseRange_fin (F := M)).equalizer
    ((continuous_conjFin _).comp (continuous_conjFin _)) continuous_id (funext fun k => ?_)) y
  simp only [Function.comp_apply, id]
  rw [conjFin_algebraMap, conjFin_algebraMap, RingEquiv.symm_apply_apply]

def finEquiv (σ : M ≃+* M) : Af M ≃+* Af M where
  __ := conjFin σ
  invFun := conjFin σ.symm
  left_inv y := conjFin_symm_conjFin σ y
  right_inv y := by simpa using conjFin_symm_conjFin σ.symm y

end UpperTheory.CBC.GaloisActionOnAdeles

open UpperTheory.CBC.GaloisActionOnAdeles in

def UpperTheory.CBC.SGalAdEx : Prop :=
  ∀ (M : Type) [Field M] [NumberField M] (σ : M ≃+* M), ∃ s : Ad M ≃+* Ad M, UpperTheory.CBC.IsGalAd σ s

open UpperTheory.CBC.GaloisActionOnAdeles in
theorem UpperTheory.CBC.SGalAdEx_holds : UpperTheory.CBC.SGalAdEx := by
  intro M _ _ σ
  refine ⟨RingEquiv.prodCongr (infEquiv σ) (finEquiv σ), ?_, fun x => ?_, fun x => rfl⟩
  · exact (continuous_infEquiv σ).prodMap (continuous_conjFin σ)
  · exact Prod.ext (infEquiv_algebraMap σ x) (conjFin_algebraMap σ x)
