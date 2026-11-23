import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

namespace FiniteFlatKilled

section Algebra

open TensorProduct WithConv Coalgebra

variable {R B C F : Type*} [CommRing R] [CommRing C] [CommRing F] [Algebra R C] [Algebra R F]

section Coalg

variable [AddCommGroup B] [Module R B] [Coalgebra R B] [IsCocomm R B]

variable (B) in

def postcomp (h : C →ₐ[R] F) : WithConv (B →ₗ[R] C) →+* WithConv (B →ₗ[R] F) where
  toFun f := toConv (h.toLinearMap ∘ₗ f.ofConv)
  map_one' := by ext c; simp
  map_mul' f g := by
    rw [LinearMap.algHom_comp_convMul_distrib]
  map_zero' := by ext c; simp
  map_add' f g := by ext c; simp

@[simp] theorem postcomp_apply (h : C →ₐ[R] F) (f : WithConv (B →ₗ[R] C)) (c : B) :
    postcomp B h f c = h (f c) := rfl

variable [Algebra C F] [IsScalarTower R C F]

theorem pow_card_eq_one {ι : Type*} [Fintype ι] (b : Module.Basis ι C F) (τ : F ≃ₐ[C] F)
    (x : WithConv (B →ₗ[R] F)) (hx : IsUnit x) (u : WithConv (B →ₗ[R] C))
    (h : postcomp B (τ.toAlgHom.restrictScalars R) x =
      x * postcomp B (IsScalarTower.toAlgHom R C F) u) :
    u ^ Fintype.card ι = 1 := by
  classical
  letI : Algebra (WithConv (B →ₗ[R] C)) (WithConv (B →ₗ[R] F)) :=
    (postcomp B (IsScalarTower.toAlgHom R C F)).toAlgebra
  have hsmul : ∀ (g : WithConv (B →ₗ[R] C)) (f : WithConv (B →ₗ[R] F)),
      g • f = postcomp B (IsScalarTower.toAlgHom R C F) g * f := fun _ _ => rfl
  let e : WithConv (B →ₗ[R] F) ≃ₗ[WithConv (B →ₗ[R] C)] (ι → WithConv (B →ₗ[R] C)) :=
    { toFun := fun f i => toConv ((b.coord i).restrictScalars R ∘ₗ f.ofConv)
      invFun := fun g => toConv (∑ i,
        (LinearMap.toSpanSingleton C F (b i)).restrictScalars R ∘ₗ (g i).ofConv)
      map_add' := fun f g => by ext i c; simp
      map_smul' := fun g f => by
        ext i c
        rw [hsmul]
        simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul]
        rw [(ℛ R c).convMul_apply]
        simp only [LinearMap.comp_apply]
        rw [(ℛ R c).convMul_apply]
        simp [← Algebra.smul_def]
      left_inv := fun f => by
        ext c
        simp
      right_inv := fun g => by
        ext i c
        simp [Finsupp.single_apply] }
  let b' := Module.Basis.ofEquivFun e
  let τ' : WithConv (B →ₗ[R] F) ≃ₐ[WithConv (B →ₗ[R] C)] WithConv (B →ₗ[R] F) :=
    AlgEquiv.ofRingEquiv (f := RingEquiv.ofRingHom (postcomp B (τ.toAlgHom.restrictScalars R))
      (postcomp B (τ.symm.toAlgHom.restrictScalars R)) (by ext f c; simp) (by ext f c; simp))
      (fun g => by
        ext c
        exact τ.commutes (g c))
  have h1 : τ' x = x * algebraMap _ _ u := h
  have h2 := Algebra.norm_eq_of_algEquiv τ' x
  rw [h1, map_mul, Algebra.norm_algebraMap_of_basis b'] at h2
  exact (hx.map (Algebra.norm (WithConv (B →ₗ[R] C)))).mul_left_cancel (by rw [h2, mul_one])

end Coalg

variable [CommRing B] [HopfAlgebra R B]

theorem mul_comp_antipode (u : B →ₐ[R] C) :
    toConv u * toConv (u.comp (HopfAlgebra.antipodeAlgHom R B)) = 1 := by
  have h : toConv (AlgHom.id R B) * toConv (HopfAlgebra.antipodeAlgHom R B) = 1 :=
    mul_inv_cancel (toConv (AlgHom.id R B))
  have h2 := AlgHom.comp_convMul_distrib u (toConv (AlgHom.id R B))
    (toConv (HopfAlgebra.antipodeAlgHom R B))
  rw [h] at h2
  apply ofConv_injective
  refine h2.symm.trans ?_
  ext c
  simp

variable [IsCocomm R B]

theorem point_pow_card {ι : Type*} [Fintype ι] (b : Module.Basis ι C (C ⊗[R] B))
    (u : B →ₐ[R] C) : toConv u ^ Fintype.card ι = 1 := by
  let x : WithConv (B →ₐ[R] C ⊗[R] B) := toConv Algebra.TensorProduct.includeRight
  let T : (B →ₐ[R] C) → (C ⊗[R] B →ₐ[C] C ⊗[R] B) := fun v =>
    Algebra.TensorProduct.lift (Algebra.ofId C _)
      (x * toConv ((IsScalarTower.toAlgHom R C (C ⊗[R] B)).comp v)).ofConv
      fun _ _ => Commute.all _ _
  have hTx : ∀ v, ((T v).restrictScalars R).comp x.ofConv =
      (x * toConv ((IsScalarTower.toAlgHom R C (C ⊗[R] B)).comp v)).ofConv := fun v => by
    ext c
    simp [T, x]
  have hTy : ∀ v w : B →ₐ[R] C, ((T v).restrictScalars R).comp
      ((IsScalarTower.toAlgHom R C (C ⊗[R] B)).comp w) =
      (IsScalarTower.toAlgHom R C (C ⊗[R] B)).comp w := fun v w => by
    ext c
    exact (T v).commutes (w c)
  have hTT : ∀ v w : B →ₐ[R] C, toConv v * toConv w = 1 → (T v).comp (T w) = AlgHom.id _ _ := by
    intro v w hvw
    refine Algebra.TensorProduct.ext (Subsingleton.elim _ _) ?_
    change ((T v).restrictScalars R).comp (((T w).restrictScalars R).comp x.ofConv) = x.ofConv
    have h3 := AlgHom.comp_convMul_distrib (IsScalarTower.toAlgHom R C (C ⊗[R] B))
      (toConv v) (toConv w)
    have h4 : (IsScalarTower.toAlgHom R C (C ⊗[R] B)).comp
        (1 : WithConv (B →ₐ[R] C)).ofConv = (1 : WithConv (B →ₐ[R] C ⊗[R] B)).ofConv := by
      ext c
      simp
    rw [hvw, h4] at h3
    rw [hTx, AlgHom.comp_convMul_distrib, hTx, ofConv_toConv, hTy, toConv_ofConv, mul_assoc,
      ← ofConv_injective h3, mul_one]
  let τ : C ⊗[R] B ≃ₐ[C] C ⊗[R] B :=
    AlgEquiv.ofAlgHom (T u) (T (u.comp (HopfAlgebra.antipodeAlgHom R B)))
      (hTT _ _ (mul_comp_antipode u)) (hTT _ _ (by rw [mul_comm]; exact mul_comp_antipode u))
  have hx : IsUnit (toConv x.ofConv.toLinearMap) := by
    refine IsUnit.of_mul_eq_one
      (toConv (x.ofConv.comp (HopfAlgebra.antipodeAlgHom R B)).toLinearMap) ?_
    exact congrArg (fun f : WithConv (B →ₐ[R] C ⊗[R] B) => toConv f.ofConv.toLinearMap)
      (mul_comp_antipode x.ofConv)
  have key := pow_card_eq_one b τ _ hx (toConv u.toLinearMap)
    (congrArg (fun f : B →ₐ[R] C ⊗[R] B => toConv f.toLinearMap) (hTx u))
  apply ofConv_injective
  apply AlgHom.toLinearMap_injective
  apply toConv_injective
  rw [AlgHom.toLinearMap_convPow, AlgHom.toLinearMap_convOne]
  exact key

theorem comp_convPow (h : C →ₐ[R] F) (f : WithConv (B →ₐ[R] C)) (n : ℕ) :
    h.comp (f ^ n).ofConv = (toConv (h.comp f.ofConv) ^ n).ofConv := by
  induction n with
  | zero => ext c; simp
  | succ n ih => rw [pow_succ, pow_succ, AlgHom.comp_convMul_distrib, ih]

theorem exists_id_pow_eq_one [Module.Finite R B] [Module.Flat R B] :
    ∃ N : ℕ, 1 ≤ N ∧ toConv (AlgHom.id R B) ^ N = 1 := by
  obtain ⟨d, s, hs⟩ := Module.Finite.exists_fin (R := R) (M := B)
  refine ⟨d.factorial, d.factorial_pos, ?_⟩
  apply ofConv_injective
  ext c
  refine Module.eq_of_localization_maximal (R := B) (fun P _ => Localization.AtPrime P)
    (fun P _ => Algebra.linearMap B (Localization.AtPrime P)) _ _ (fun m hm => ?_)
  let C := Localization.AtPrime m
  let u : B →ₐ[R] C := IsScalarTower.toAlgHom R B C
  haveI : Module.Free C (C ⊗[R] B) := Module.free_of_flat_of_isLocalRing
  have h1 := point_pow_card (Module.finBasis C (C ⊗[R] B)) u
  rw [Fintype.card_fin] at h1
  haveI : Nontrivial (C ⊗[R] B) :=
    (Algebra.TensorProduct.lift (AlgHom.id C C) u fun _ _ => Commute.all _ _).toRingHom.domain_nontrivial
  have hpos : 0 < Module.finrank C (C ⊗[R] B) :=
    (Module.finrank_pos_iff_of_free C (C ⊗[R] B)).2 inferInstance
  have hle : Module.finrank C (C ⊗[R] B) ≤ d := by
    have hsp : Submodule.span C (Set.range fun i => (1 : C) ⊗ₜ[R] s i) = ⊤ := by
      have := Submodule.baseChange_span (R := R) C (Set.range s)
      rw [hs, Submodule.baseChange_top, ← Set.range_comp] at this
      exact this.symm
    simpa using finrank_le_of_span_eq_top hsp
  obtain ⟨k, hk⟩ := Nat.dvd_factorial hpos hle
  have h2 := comp_convPow u (toConv (AlgHom.id R B)) d.factorial
  rw [ofConv_toConv, AlgHom.comp_id, hk, pow_mul (toConv u), h1, one_pow, ← hk] at h2
  have h3 := congr($h2 c)
  refine h3.trans ?_
  exact IsScalarTower.algebraMap_apply R B C _

end Algebra

section Scheme

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry TensorProduct WithConv

attribute [local instance] Over.cartesianMonoidalCategory

theorem isCocomm_of_mul_comm {R B : Type*} [CommRing R] [CommRing B] [Bialgebra R B]
    (h : ∀ f g : WithConv (B →ₐ[R] B ⊗[R] B), f * g = g * f) : Coalgebra.IsCocomm R B := by
  let l : WithConv (B →ₐ[R] B ⊗[R] B) := toConv Algebra.TensorProduct.includeLeft
  let r : WithConv (B →ₐ[R] B ⊗[R] B) := toConv Algebra.TensorProduct.includeRight
  have h1 : (Algebra.TensorProduct.lmul' R).comp (Algebra.TensorProduct.map l.ofConv r.ofConv) =
      AlgHom.id R (B ⊗[R] B) := by
    ext <;> simp [l, r, ← Algebra.TensorProduct.one_def]
  have h2 : (Algebra.TensorProduct.lmul' R).comp (Algebra.TensorProduct.map r.ofConv l.ofConv) =
      (Algebra.TensorProduct.comm R B B).toAlgHom := by
    ext <;> simp [l, r, ← Algebra.TensorProduct.one_def]
  have h3 := congrArg ofConv (h r l)
  rw [AlgHom.convMul_def, AlgHom.convMul_def, ofConv_toConv, ofConv_toConv, ← AlgHom.comp_assoc,
    ← AlgHom.comp_assoc, h1, h2] at h3
  exact ⟨LinearMap.ext fun c => congr($h3 c)⟩

theorem exists_id_pow_eq_one_of_isFinite_of_flat (R : Type) [CommRing R]
    (H : Over (Spec (CommRingCat.of R))) [GrpObj H] [IsCommMonObj H] (hf : IsFinite H.hom)
    (hfl : Flat H.hom) : ∃ N : ℕ, 1 ≤ N ∧ 𝟙 H ^ N = 1 := by
  have haff : IsAffine H.left := isAffine_of_isAffineHom H.hom
  obtain ⟨A, ⟨e⟩⟩ := (essImage_hopfSpec (G := Grp.mk H)).2 haff
  let B : Type := A.unop
  letI : HopfAlgebra R B := A.unop.hopfAlgebra
  let G : Over (Spec (CommRingCat.of R)) :=
    (Spec (CommRingCat.of B)).asOver (Spec (CommRingCat.of R))
  letI : GrpObj G := instGrpObjSpecAsOverSpec (R := CommRingCat.of R) (A := CommRingCat.of B)
  let i : G ≅ H := (Grp.forget _).mapIso e
  haveI : IsMonHom i.hom := e.hom.hom.isMonHom_hom
  obtain ⟨j, hj, hw⟩ : ∃ j : Spec (CommRingCat.of B) ⟶ H.left, IsIso j ∧
      Spec.map (CommRingCat.ofHom (algebraMap R B)) = j ≫ H.hom :=
    ⟨i.hom.left, inferInstanceAs (IsIso ((Over.forget _).map i.hom)), (Over.w i.hom).symm⟩
  haveI : Module.Finite R B := by
    have h1 : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap R B))) := by
      rw [hw]; infer_instance
    rw [IsFinite.SpecMap_iff] at h1
    exact RingHom.finite_algebraMap.1 h1
  haveI : Module.Flat R B := by
    have h1 : Flat (Spec.map (CommRingCat.ofHom (algebraMap R B))) := by
      rw [hw]; infer_instance
    rw [Flat.SpecMap_iff] at h1
    exact RingHom.flat_algebraMap_iff.1 h1
  haveI : Coalgebra.IsCocomm R B := isCocomm_of_mul_comm fun f g => by
    let φ := (Spec.mapMulEquiv (R := R) (S := B) (T := B ⊗[R] B)).trans
      (Hom.mulEquivCongrRight i _)
    apply φ.injective
    rw [map_mul, map_mul, mul_comm]
  obtain ⟨N, hN, h⟩ := exists_id_pow_eq_one (R := R) (B := B)
  refine ⟨N, hN, ?_⟩
  have h1 := congrArg (Spec.mapMulEquiv (R := R) (S := B) (T := B)) h
  rw [map_pow, map_one] at h1
  have h2 : Spec.mapMulEquiv (R := R) (S := B) (T := B) (toConv (AlgHom.id R B)) = 𝟙 G := by
    ext1
    exact Spec.map_id _
  have h3 : 𝟙 G ^ N = 1 := h2 ▸ h1
  rw [← cancel_epi i.hom, MonObj.comp_pow, MonObj.comp_one, Category.comp_id,
    ← Category.id_comp i.hom, ← MonObj.pow_comp, h3, MonObj.one_comp]

theorem main : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (H : Over (Spec (CommRingCat.of R)))
    [GrpObj H] [IsCommMonObj H], IsFinite H.hom → Flat H.hom → ∃ N : ℕ, 1 ≤ N ∧ 𝟙 H ^ N = 1 :=
  fun R _ _ H _ _ hf hfl => exists_id_pow_eq_one_of_isFinite_of_flat R H hf hfl

end Scheme

end FiniteFlatKilled

end GlobalTheory
