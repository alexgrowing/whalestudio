import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IotaQInjective

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.WedgeOf

namespace GlobalTheory.CompanionTheory.WedgeOf.Shuffle

theorem exists_tensorPi (R : Type) [CommRing R] (I J : Type) [Finite I] [Finite J] (A : I → Type) (B : J → Type)
    [∀ i, AddCommGroup (A i)] [∀ i, Module R (A i)] [∀ j, AddCommGroup (B j)] [∀ j, Module R (B j)] :
    ∃ Φ : (∀ i, A i) ⊗[R] (∀ j, B j) ≃ₗ[R] ∀ x : I × J, A x.1 ⊗[R] B x.2,
      ∀ (f : ∀ i, A i) (g : ∀ j, B j) (x : I × J), Φ (f ⊗ₜ g) x = f x.1 ⊗ₜ g x.2 := by
  classical
  haveI := Fintype.ofFinite I
  haveI := Fintype.ofFinite J
  let e : (∀ j, ∀ i, A i ⊗[R] B j) ≃ₗ[R] ∀ x : I × J, A x.1 ⊗[R] B x.2 :=
    { toFun := fun g x ↦ g x.2 x.1
      invFun := fun h j i ↦ h (i, j)
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  refine ⟨(TensorProduct.piRight R R (∀ i, A i) B) ≪≫ₗ
    (LinearEquiv.piCongrRight fun j ↦ (TensorProduct.comm R _ _) ≪≫ₗ (TensorProduct.piRight R R (B j) A) ≪≫ₗ
      (LinearEquiv.piCongrRight fun i ↦ TensorProduct.comm R _ _)) ≪≫ₗ e, fun f g x ↦ ?_⟩
  simp [e]

variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)

abbrev Ar (C : Type) [Category.{0} C] : Type := Σ T : C, Σ T' : C, (T ⟶ T')

theorem finite_ar [Finite C] [Quiver.IsThin C] : Finite (Ar C) := by
  haveI : ∀ T T' : C, Finite (T ⟶ T') := fun _ _ ↦ Finite.of_subsingleton
  infer_instance

def oneCochainsPiArrowsEquiv : C1 F ≃ₗ[R] ∀ x : Ar C, F.obj x.2.1 where
  toFun f x := f x.1 x.2.1 x.2.2
  invFun g T T' φ := g ⟨T, T', φ⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

abbrev E : Type := ∀ x : Ar C × Ar C, F.obj x.1.2.1 ⊗[R] F.obj x.2.2.1

def shuffle : C2 (box F) →ₗ[R] E F where
  toFun z x := z (x.1.1, x.2.1) (x.1.2.1, x.2.1) (x.1.2.1, x.2.2.1) (x.1.2.2, 𝟙 _) (𝟙 _, x.2.2.2)
    - z (x.1.1, x.2.1) (x.1.1, x.2.2.1) (x.1.2.1, x.2.2.1) (𝟙 _, x.2.2.2) (x.1.2.2, 𝟙 _)
  map_add' z z' := by
    funext x
    simp only [Pi.add_apply]
    abel
  map_smul' r z := by
    funext x
    simp only [Pi.smul_apply, RingHom.id_apply, smul_sub]

theorem mp_box {a a' b b' : C} (φ : a ⟶ a') (ψ : b ⟶ b') (t : F.obj a ⊗[R] F.obj b) :
    (mp (box F) (T := (a, b)) (T' := (a', b')) (φ, ψ)) t =
      TensorProduct.map (mp F φ).toLinearMap (mp F ψ).toLinearMap t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => rfl
  | add u v hu hv => simp only [map_add, hu, hv]

theorem shuffle_cup (f h : Z1 F) (x : Ar C × Ar C) :
    shuffle F (cupZ (box F) ((boxL F).pullbackOneCocycle f) ((boxR F).pullbackOneCocycle h)).1 x =
      f.1 _ _ x.1.2.2 ⊗ₜ h.1 _ _ x.2.2.2 := by
  obtain ⟨⟨a, a', φ⟩, ⟨b, b', ψ⟩⟩ := x
  change (mp (box F) (T := (a', b)) (T' := (a', b')) (𝟙 a', ψ)) (f.1 a a' φ ⊗ₜ 1) * (1 ⊗ₜ h.1 b b' ψ) -
    (mp (box F) (T := (a, b')) (T' := (a', b')) (φ, 𝟙 b')) (f.1 a a (𝟙 a) ⊗ₜ 1) * (1 ⊗ₜ h.1 b' b' (𝟙 b')) = _
  rw [Z1.id f a, mp_box]
  simp [mp_id]

theorem shuffle_mk (z : C2 (box F)) {a a' b b' : C} (φ : a ⟶ a') (ψ : b ⟶ b') :
    shuffle F z (⟨a, a', φ⟩, ⟨b, b', ψ⟩) =
      z (a, b) (a', b) (a', b') (φ, 𝟙 b) (𝟙 a', ψ) - z (a, b) (a, b') (a', b') (𝟙 a, ψ) (φ, 𝟙 b') := rfl

theorem shuffle_coboundary_one (w : C1 (box F)) {a a' b b' : C} (φ : a ⟶ a') (ψ : b ⟶ b') :
    shuffle F (d1 (box F) w) (⟨a, a', φ⟩, ⟨b, b', ψ⟩) =
      (TensorProduct.map LinearMap.id (mp F ψ).toLinearMap (w (a, b) (a', b) (φ, 𝟙 b)) - w (a, b') (a', b') (φ, 𝟙 b')) +
      (w (a', b) (a', b') (𝟙 a', ψ) -
        TensorProduct.map (mp F φ).toLinearMap LinearMap.id (w (a, b) (a, b') (𝟙 a, ψ))) := by
  have e : CategoryStruct.comp (X := ((a, b) : C × C)) (Y := (a', b)) (Z := (a', b')) (φ, 𝟙 b) (𝟙 a', ψ) =
      CategoryStruct.comp (X := ((a, b) : C × C)) (Y := (a, b')) (Z := (a', b')) (𝟙 a, ψ) (φ, 𝟙 b') := by
    simp
  have i1 : (mp F (𝟙 a')).toLinearMap = LinearMap.id := by ext u; exact mp_id F a' u
  have i2 : (mp F (𝟙 b')).toLinearMap = LinearMap.id := by ext u; exact mp_id F b' u
  rw [shuffle_mk, d1_apply, d1_apply, e, mp_box, mp_box, i1, i2]
  abel

theorem exists_one_one_cochain_tensor_equiv [Finite C] [Quiver.IsThin C] :
    ∃ Φ : C1 F ⊗[R] C1 F ≃ₗ[R] E F, ∀ f g x, Φ (f ⊗ₜ g) x = f _ _ x.1.2.2 ⊗ₜ g _ _ x.2.2.2 := by
  haveI := finite_ar (C := C)
  obtain ⟨Φ, h⟩ := exists_tensorPi R (Ar C) (Ar C) (fun x ↦ F.obj x.2.1) (fun x ↦ F.obj x.2.1)
  exact ⟨TensorProduct.congr (oneCochainsPiArrowsEquiv F) (oneCochainsPiArrowsEquiv F) ≪≫ₗ Φ, fun f g x ↦ h _ _ x⟩

theorem exists_one_zero_cochain_tensor_equiv [Finite C] [Quiver.IsThin C] :
    ∃ Φ : C1 F ⊗[R] C0 F ≃ₗ[R] ∀ x : Ar C × C, F.obj x.1.2.1 ⊗[R] F.obj x.2,
      ∀ f g x, Φ (f ⊗ₜ g) x = f _ _ x.1.2.2 ⊗ₜ g x.2 := by
  haveI := finite_ar (C := C)
  obtain ⟨Φ, h⟩ := exists_tensorPi R (Ar C) C (fun x ↦ F.obj x.2.1) (fun x ↦ F.obj x)
  exact ⟨TensorProduct.congr (oneCochainsPiArrowsEquiv F) (LinearEquiv.refl R _) ≪≫ₗ Φ, fun f g x ↦ h _ _ x⟩

theorem exists_zero_one_cochain_tensor_equiv [Finite C] [Quiver.IsThin C] :
    ∃ Φ : C0 F ⊗[R] C1 F ≃ₗ[R] ∀ x : C × Ar C, F.obj x.1 ⊗[R] F.obj x.2.2.1,
      ∀ f g x, Φ (f ⊗ₜ g) x = f x.1 ⊗ₜ g _ _ x.2.2.2 := by
  haveI := finite_ar (C := C)
  obtain ⟨Φ, h⟩ := exists_tensorPi R C (Ar C) (fun x ↦ F.obj x) (fun x ↦ F.obj x.2.1)
  exact ⟨TensorProduct.congr (LinearEquiv.refl R _) (oneCochainsPiArrowsEquiv F) ≪≫ₗ Φ, fun f g x ↦ h _ _ x⟩

variable {F}

theorem phi_right (Φ : C1 F ⊗[R] C1 F ≃ₗ[R] E F)
    (hΦ : ∀ f g x, Φ (f ⊗ₜ g) x = f _ _ x.1.2.2 ⊗ₜ g _ _ x.2.2.2)
    (Φ₁ : C1 F ⊗[R] C0 F ≃ₗ[R] ∀ x : Ar C × C, F.obj x.1.2.1 ⊗[R] F.obj x.2)
    (hΦ₁ : ∀ f g x, Φ₁ (f ⊗ₜ g) x = f _ _ x.1.2.2 ⊗ₜ g x.2) (u : C1 F ⊗[R] C0 F) (x y : Ar C) :
    Φ (TensorProduct.map LinearMap.id (d0 F) u) (x, y) =
      Φ₁ u (x, y.2.1) - TensorProduct.map LinearMap.id (mp F y.2.2).toLinearMap (Φ₁ u (x, y.1)) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul f g =>
    simp only [TensorProduct.map_tmul, LinearMap.id_apply, hΦ, hΦ₁, amitsur_d0_apply, TensorProduct.tmul_sub]
    rfl
  | add u v hu hv =>
    simp only [map_add, Pi.add_apply, hu, hv]
    abel

theorem phi_left (Φ : C1 F ⊗[R] C1 F ≃ₗ[R] E F)
    (hΦ : ∀ f g x, Φ (f ⊗ₜ g) x = f _ _ x.1.2.2 ⊗ₜ g _ _ x.2.2.2)
    (Φ₂ : C0 F ⊗[R] C1 F ≃ₗ[R] ∀ x : C × Ar C, F.obj x.1 ⊗[R] F.obj x.2.2.1)
    (hΦ₂ : ∀ f g x, Φ₂ (f ⊗ₜ g) x = f x.1 ⊗ₜ g _ _ x.2.2.2) (v : C0 F ⊗[R] C1 F) (x y : Ar C) :
    Φ (TensorProduct.map (d0 F) LinearMap.id v) (x, y) =
      Φ₂ v (x.2.1, y) - TensorProduct.map (mp F x.2.2).toLinearMap LinearMap.id (Φ₂ v (x.1, y)) := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul f g =>
    simp only [TensorProduct.map_tmul, LinearMap.id_apply, hΦ, hΦ₂, amitsur_d0_apply, TensorProduct.sub_tmul]
    rfl
  | add u v hu hv =>
    simp only [map_add, Pi.add_apply, hu, hv]
    abel

variable (F)

def crossZ : Z1 F ⊗[R] Z1 F →ₗ[R] Z2 (box F) :=
  TensorProduct.lift ((cupZ (box F)).compl₁₂ (boxL F).pullbackOneCocycle (boxR F).pullbackOneCocycle)

theorem crossZ_tmul (f h : Z1 F) :
    crossZ F (f ⊗ₜ h) = cupZ (box F) ((boxL F).pullbackOneCocycle f) ((boxR F).pullbackOneCocycle h) := rfl

theorem mk_crossZ (s : Z1 F ⊗[R] Z1 F) :
    H2.mk (box F) (crossZ F s) = TensorProduct.lift (crossB F) (TensorProduct.map (H1.mk F) (H1.mk F) s) := by
  induction s using TensorProduct.induction_on with
  | zero => simp
  | tmul f h => rfl
  | add u v hu hv => simp only [map_add, hu, hv]

theorem shuffle_crossZ (Φ : C1 F ⊗[R] C1 F ≃ₗ[R] E F)
    (hΦ : ∀ f g x, Φ (f ⊗ₜ g) x = f _ _ x.1.2.2 ⊗ₜ g _ _ x.2.2.2) (s : Z1 F ⊗[R] Z1 F) :
    shuffle F (crossZ F s).1 = Φ (TensorProduct.map (Z1 F).subtype (Z1 F).subtype s) := by
  induction s using TensorProduct.induction_on with
  | zero => simp
  | tmul f h =>
    funext x
    rw [crossZ_tmul, shuffle_cup, TensorProduct.map_tmul, hΦ]
    rfl
  | add u v hu hv =>
    simp only [map_add, Submodule.coe_add, hu, hv]

theorem exists_boundary [Finite C] [Quiver.IsThin C] (s : Z1 F ⊗[R] Z1 F) (w : C1 (box F))
    (hw : d1 (box F) w = (crossZ F s).1) :
    ∃ (u : C1 F ⊗[R] C0 F) (v : C0 F ⊗[R] C1 F), TensorProduct.map (Z1 F).subtype (Z1 F).subtype s =
      TensorProduct.map (d0 F) LinearMap.id v - TensorProduct.map LinearMap.id (d0 F) u := by
  obtain ⟨Φ, hΦ⟩ := exists_one_one_cochain_tensor_equiv F
  obtain ⟨Φ₁, hΦ₁⟩ := exists_one_zero_cochain_tensor_equiv F
  obtain ⟨Φ₂, hΦ₂⟩ := exists_zero_one_cochain_tensor_equiv F
  refine ⟨Φ₁.symm fun x ↦ w (x.1.1, x.2) (x.1.2.1, x.2) (x.1.2.2, 𝟙 _),
    Φ₂.symm fun x ↦ w (x.1, x.2.1) (x.1, x.2.2.1) (𝟙 _, x.2.2.2), Φ.injective ?_⟩
  rw [← shuffle_crossZ F Φ hΦ, ← hw]
  funext ⟨⟨a, a', φ⟩, ⟨b, b', ψ⟩⟩
  rw [shuffle_coboundary_one, map_sub, Pi.sub_apply, phi_right Φ hΦ Φ₁ hΦ₁, phi_left Φ hΦ Φ₂ hΦ₂]
  simp only [LinearEquiv.apply_symm_apply]
  abel

theorem map_iotaQ_eq_zero (R : Type) [CommRing R] (C : Type) [Category.{0} C] [Finite C] [Quiver.IsThin C]
    (F : C ⥤ CommAlgCat.{0} R) (t : H1 F ⊗[R] H1 F) (ht : TensorProduct.lift (crossB F) t = 0) :
    TensorProduct.map (iotaQ F) (iotaQ F) t = 0 := by
  obtain ⟨s, rfl⟩ := TensorProduct.map_surjective (H1.mk_surjective F) (H1.mk_surjective F) t
  rw [← mk_crossZ] at ht
  obtain ⟨w, hw⟩ := H2.mk_eq_zero.1 ht
  obtain ⟨u, v, huv⟩ := exists_boundary F s w hw
  let q := (LinearMap.range (d0 F)).mkQ
  have hq : ∀ g, q (d0 F g) = 0 := fun g ↦ (Submodule.Quotient.mk_eq_zero _).2 ⟨g, rfl⟩
  have h1 : ∀ s : Z1 F ⊗[R] Z1 F, TensorProduct.map (iotaQ F) (iotaQ F) (TensorProduct.map (H1.mk F) (H1.mk F) s) =
      TensorProduct.map q q (TensorProduct.map (Z1 F).subtype (Z1 F).subtype s) := fun s ↦ by
    induction s using TensorProduct.induction_on with
    | zero => simp
    | tmul f h => rfl
    | add a b ha hb => simp only [map_add, ha, hb]
  have h2 : ∀ v : C0 F ⊗[R] C1 F, TensorProduct.map q q (TensorProduct.map (d0 F) LinearMap.id v) = 0 := fun v ↦ by
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul f h => simp [hq]
    | add a b ha hb => simp only [map_add, ha, hb, add_zero]
  have h3 : ∀ u : C1 F ⊗[R] C0 F, TensorProduct.map q q (TensorProduct.map LinearMap.id (d0 F) u) = 0 := fun u ↦ by
    induction u using TensorProduct.induction_on with
    | zero => simp
    | tmul f h => simp [hq]
    | add a b ha hb => simp only [map_add, ha, hb, add_zero]
  rw [h1, huv, map_sub, h2, h3, sub_zero]

end GlobalTheory.CompanionTheory.WedgeOf.Shuffle
