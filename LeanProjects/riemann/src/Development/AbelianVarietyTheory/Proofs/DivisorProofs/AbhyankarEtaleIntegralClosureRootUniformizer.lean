import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbhyankarDvrOfIsSeparableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleIntegralClosureTensorOfEtaleOfIsIntegralStatement
open IsLocalRing Polynomial
open scoped TensorProduct

theorem GlobalTheory.AbhyankarBC.nonempty_tensor_algEquiv_of_isFractionRing : ∀ (S K L F : Type) [CommRing S] [Field K] [Algebra S K] [IsFractionRing S K] [CommRing L]
    [Algebra K L] [Algebra S L] [IsScalarTower S K L] [CommRing F] [Algebra K F] [Algebra S F]
    [IsScalarTower S K F], Nonempty (F ⊗[S] L ≃ₐ[F] F ⊗[K] L) := by
  intro S K L F _ _ _ _ _ _ _ _ _ _ _ _
  have hb : IsBaseChange K (LinearMap.id : L →ₗ[S] L) :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors S) K _).mp
      (isLocalizedModule_id (nonZeroDivisors S) L K)
  let g : K ⊗[S] L →ₐ[K] L :=
    Algebra.TensorProduct.lift (Algebra.ofId K L) (AlgHom.id S L) (fun _ _ => Commute.all _ _)
  have hg : (g : K ⊗[S] L → L) = hb.equiv := by
    funext x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul k l => simp [g, IsBaseChange.equiv_tmul, Algebra.smul_def]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  let e0 : K ⊗[S] L ≃ₐ[K] L := AlgEquiv.ofBijective g (by rw [hg]; exact hb.equiv.bijective)
  exact ⟨(Algebra.TensorProduct.cancelBaseChange S K F F L).symm.trans
    (Algebra.TensorProduct.congr AlgEquiv.refl e0)⟩

theorem GlobalTheory.AbhyankarBC.tensor_map_val_bijective_of_smul_mem : ∀ (D B F : Type) [CommRing D] [CommRing B] [Algebra D B] [CommRing F] [Algebra D F]
    (N : Subalgebra D B) (M : Submonoid D), (∀ m ∈ M, IsUnit (algebraMap D F m)) →
    (∀ b : B, ∃ m ∈ M, m • b ∈ N) →
    Function.Bijective (Algebra.TensorProduct.map (AlgHom.id F F) N.val : F ⊗[D] N →ₐ[F] F ⊗[D] B) := by
  intro D B F _ _ _ _ _ N M hM hN
  let Dm := Localization M
  have hM' : ∀ y : M, IsUnit (algebraMap D F y) := fun y => hM y y.2
  letI : Algebra Dm F := (IsLocalization.lift (M := M) (S := Dm) (g := algebraMap D F) hM').toAlgebra
  haveI : IsScalarTower D Dm F :=
    IsScalarTower.of_algebraMap_eq (fun x => (IsLocalization.lift_eq (M := M) (S := Dm) hM' x).symm)
  let ι : Dm ⊗[D] N →ₐ[Dm] Dm ⊗[D] B := Algebra.TensorProduct.map (AlgHom.id Dm Dm) N.val
  have hι : Function.Bijective ι := by
    constructor
    · have := Module.Flat.lTensor_preserves_injective_linearMap (M := Dm) N.val.toLinearMap
        Subtype.val_injective
      exact this
    · intro x
      induction x using TensorProduct.induction_on with
      | zero => exact ⟨0, map_zero _⟩
      | tmul a b =>
        obtain ⟨m, hm, hmb⟩ := hN b
        let u := (IsLocalization.map_units Dm (⟨m, hm⟩ : M)).unit
        refine ⟨(a * ↑u⁻¹) ⊗ₜ[D] (⟨m • b, hmb⟩ : N), ?_⟩
        simp only [ι, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Subalgebra.coe_val]
        rw [← TensorProduct.smul_tmul, Algebra.smul_def]
        congr 1
        have hu : (u : Dm) = algebraMap D Dm m := rfl
        rw [← hu, mul_left_comm, Units.mul_inv, mul_one]
      | add x y hx hy =>
        obtain ⟨x', rfl⟩ := hx
        obtain ⟨y', rfl⟩ := hy
        exact ⟨x' + y', map_add _ _ _⟩
  let eι : Dm ⊗[D] N ≃ₐ[Dm] Dm ⊗[D] B := AlgEquiv.ofBijective ι hι
  let E : F ⊗[D] N ≃ₐ[F] F ⊗[D] B :=
    (Algebra.TensorProduct.cancelBaseChange D Dm F F N).symm.trans
      ((Algebra.TensorProduct.congr AlgEquiv.refl eι).trans
        (Algebra.TensorProduct.cancelBaseChange D Dm F F B))
  have hE : ⇑(Algebra.TensorProduct.map (AlgHom.id F F) N.val : F ⊗[D] N →ₐ[F] F ⊗[D] B) = ⇑E := by
    funext x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul f n =>
      simp [E, eι, ι, Algebra.TensorProduct.cancelBaseChange_tmul,
        Algebra.TensorProduct.cancelBaseChange_symm_tmul]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  rw [hE]
  exact E.bijective

theorem GlobalTheory.AbhyankarBC.exists_smul_mem_integralClosure_tensor : ∀ (S K L D : Type) [CommRing S] [IsDomain S] [Field K] [Algebra S K] [IsFractionRing S K]
    [Field L] [Algebra K L] [Algebra S L] [IsScalarTower S K L] [Algebra.IsAlgebraic K L]
    [CommRing D] [Algebra S D], ∀ b : D ⊗[S] L,
    ∃ m ∈ Algebra.algebraMapSubmonoid D (nonZeroDivisors S), m • b ∈ integralClosure D (D ⊗[S] L) := by
  intro S K L D _ _ _ _ _ _ _ _ _ _ _ _ b
  induction b using TensorProduct.induction_on with
  | zero => exact ⟨1, one_mem _, by simp⟩
  | tmul d l =>
    obtain ⟨s, hs0, hint⟩ := IsAlgebraic.exists_integral_multiple
      ((IsFractionRing.isAlgebraic_iff S K L).mpr (Algebra.IsAlgebraic.isAlgebraic l))
    refine ⟨algebraMap S D s, ⟨s, mem_nonZeroDivisors_of_ne_zero hs0, rfl⟩, ?_⟩
    have h1 : algebraMap S D s • (d ⊗ₜ[S] l) = algebraMap D (D ⊗[S] L) d * ((1 : D) ⊗ₜ[S] (s • l)) := by
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
        algebraMap_smul, one_mul, Algebra.algebraMap_self, RingHom.id_apply, TensorProduct.tmul_smul]
    rw [h1]
    refine Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ d) ?_
    exact (hint.map (Algebra.TensorProduct.includeRight : L →ₐ[S] D ⊗[S] L)).tower_top
  | add x y hx hy =>
    obtain ⟨m1, hm1, h1⟩ := hx
    obtain ⟨m2, hm2, h2⟩ := hy
    refine ⟨m1 * m2, mul_mem hm1 hm2, ?_⟩
    rw [smul_add]
    refine add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact Subalgebra.smul_mem _ h1 _
    · rw [mul_smul]; exact Subalgebra.smul_mem _ h2 _

theorem GlobalTheory.AbhyankarBC.etale_integralClosure_of_root_uniformizer : ∀ (S S₁ K K₁ L : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [CommRing S₁]
    [IsDomain S₁] [IsDiscreteValuationRing S₁] [Field K] [Algebra S K] [IsFractionRing S K] [Field K₁]
    [Algebra S₁ K₁] [IsFractionRing S₁ K₁] [Algebra S S₁] [Algebra K K₁] [Algebra S K₁]
    [IsScalarTower S K K₁] [IsScalarTower S S₁ K₁] [Field L] [Algebra K L] [Algebra S L]
    [IsScalarTower S K L] [FiniteDimensional K L] [Algebra.IsSeparable K L],
    Function.Injective (algebraMap S S₁) → ∀ (q : ℕ), 0 < q → IsUnit (q : S) →
    ∀ π : S, Irreducible π → ∀ y : S₁, y ^ q = algebraMap S S₁ π →
    (∀ P : Ideal (integralClosure S L), P.IsMaximal → P.ramificationIdx S ∣ q) →
    (∀ P : Ideal (integralClosure S L), P.IsMaximal → ∀ [P.LiesOver (maximalIdeal S)],
      Algebra.IsSeparable (S ⧸ maximalIdeal S) (integralClosure S L ⧸ P)) →
    Algebra.Etale S₁ (integralClosure S₁ (K₁ ⊗[K] L)) := by
  intro S S₁ K K₁ L _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hinj q hq hqu π hπ y hy hram hsep
  let f : S[X] := X ^ q - C π
  let D := AdjoinRoot f
  have hD : Algebra.Etale D (integralClosure D (D ⊗[S] L)) :=
    GlobalTheory.T.abhyankar_dvr_of_isSeparable_alt S K L π q D ⟨AlgEquiv.refl⟩ hπ hqu hram hsep
  let φ : D →ₐ[S] S₁ := AdjoinRoot.liftAlgHom f (Algebra.ofId S S₁) y (by simp [f, hy])
  letI : Algebra D S₁ := φ.toRingHom.toAlgebra
  letI : Algebra D K₁ := ((algebraMap S₁ K₁).comp φ.toRingHom).toAlgebra
  haveI : IsScalarTower D S₁ K₁ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower S D S₁ := IsScalarTower.of_algebraMap_eq (fun x => (φ.commutes x).symm)
  haveI : IsScalarTower S D K₁ := IsScalarTower.of_algebraMap_eq (fun x => by
    rw [IsScalarTower.algebraMap_apply S S₁ K₁, IsScalarTower.algebraMap_apply S D S₁]; rfl)
  let N := integralClosure D (D ⊗[S] L)
  let T := S₁ ⊗[D] N
  haveI : Algebra.Etale S₁ T := Algebra.Etale.baseChange D N S₁
  haveI : Algebra.IsIntegral S₁ T := Algebra.IsIntegral.tensorProduct D S₁ N
  haveI hT := GlobalTheory.T.etale_integralClosure_tensor S₁ K₁ T inferInstance inferInstance
  have hunit : ∀ m ∈ Algebra.algebraMapSubmonoid D (nonZeroDivisors S), IsUnit (algebraMap D K₁ m) := by
    rintro _ ⟨s, hs, rfl⟩
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply S S₁ K₁]
    refine IsUnit.mk0 _ ?_
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective S₁ K₁), map_eq_zero_iff _ hinj]
    exact nonZeroDivisors.ne_zero hs
  let e1 : K₁ ⊗[S₁] T ≃ₐ[K₁] K₁ ⊗[D] N := Algebra.TensorProduct.cancelBaseChange D S₁ K₁ K₁ N
  let e2 : K₁ ⊗[D] N ≃ₐ[K₁] K₁ ⊗[D] (D ⊗[S] L) :=
    AlgEquiv.ofBijective _ (GlobalTheory.AbhyankarBC.tensor_map_val_bijective_of_smul_mem D (D ⊗[S] L) K₁ N _ hunit (GlobalTheory.AbhyankarBC.exists_smul_mem_integralClosure_tensor S K L D))
  let e3 : K₁ ⊗[D] (D ⊗[S] L) ≃ₐ[K₁] K₁ ⊗[S] L := Algebra.TensorProduct.cancelBaseChange S D K₁ K₁ L
  obtain ⟨e4⟩ := GlobalTheory.AbhyankarBC.nonempty_tensor_algEquiv_of_isFractionRing S K L K₁
  let e : K₁ ⊗[S₁] T ≃ₐ[S₁] K₁ ⊗[K] L := (((e1.trans e2).trans e3).trans e4).restrictScalars S₁
  exact Algebra.Etale.of_equiv e.mapIntegralClosure
