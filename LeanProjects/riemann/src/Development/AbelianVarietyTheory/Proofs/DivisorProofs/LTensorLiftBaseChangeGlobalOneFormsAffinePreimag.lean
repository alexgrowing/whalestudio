import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBaseChangeCompatibleGlobalOneForms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveLiftSemiOfSemilinearHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveLiftSemiSecPull
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.DeRham

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AbCoh

theorem lTensor_liftSemi_bijective_of_isBaseChange {R R' B B' W W' Ω Ω' : Type} [CommRing R]
    [CommRing R'] [Algebra R R'] [CommRing B] [Algebra R B] [CommRing B'] [Algebra R' B']
    [AddCommGroup W] [Module R W] [AddCommGroup W'] [Module R' W']
    [AddCommGroup Ω] [Module R Ω] [Module B Ω] [IsScalarTower R B Ω]
    [AddCommGroup Ω'] [Module R' Ω'] [Module B' Ω'] [IsScalarTower R' B' Ω']
    (α : B →+* B') (f : B →ₛₗ[algebraMap R R'] B') (hf : ∀ b, f b = α b)
    (h1 : Function.Surjective (liftSemi f))
    (m : Ω →ₛₗ[algebraMap R R'] Ω') (hm : ∀ (b : B) (ω : Ω), m (b • ω) = α b • m ω)
    (h2 : Function.Bijective (liftSemi m))
    (e : W →ₗ[R] Ω) (he : IsBaseChange B e) (e' : W' →ₗ[R'] Ω') (he' : IsBaseChange B' e')
    (p : W →ₛₗ[algebraMap R R'] W') (hp : ∀ w, e' (p w) = m (e w)) :
    Function.Bijective (LinearMap.lTensor B' (liftSemi p)) := by
  letI : Module R (B' ⊗[R'] (R' ⊗[R] W)) := Module.compHom _ (algebraMap R R')
  have hsm : ∀ (c : R) (z : B' ⊗[R'] (R' ⊗[R] W)), c • z = algebraMap R R' c • z := fun _ _ ↦ rfl
  have hR : ∀ (c : R) (x : R' ⊗[R] B), c • x = algebraMap R R' c • x := fun c x ↦
    (algebraMap_smul R' c x).symm
  have hW : ∀ (c : R) (w : W), (1 : R') ⊗ₜ[R] (c • w) = algebraMap R R' c • ((1 : R') ⊗ₜ[R] w) := by
    intro c w
    rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one,
      Algebra.algebraMap_eq_smul_one]

  let bil : R' ⊗[R] B →ₗ[R] W →ₗ[R] B' ⊗[R'] (R' ⊗[R] W) :=
    LinearMap.mk₂ R (fun x w ↦ liftSemi f x ⊗ₜ[R'] ((1 : R') ⊗ₜ[R] w))
      (fun x y w ↦ by rw [map_add, TensorProduct.add_tmul])
      (fun c x w ↦ by rw [hR, map_smul, hsm, TensorProduct.smul_tmul'])
      (fun x w w' ↦ by rw [TensorProduct.tmul_add, TensorProduct.tmul_add])
      (fun c x w ↦ by rw [hW, TensorProduct.tmul_smul, hsm])
  let Ψ : R' ⊗[R] (B ⊗[R] W) →ₗ[R] B' ⊗[R'] (R' ⊗[R] W) :=
    TensorProduct.lift bil ∘ₗ (TensorProduct.assoc R R' B W).symm.toLinearMap
  have hΨ : Function.Surjective Ψ := by
    suffices hall : ∀ z, z ∈ LinearMap.range Ψ from
      LinearMap.range_eq_top.1 (eq_top_iff.2 fun z _ ↦ hall z)
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact zero_mem _
    | add x y hx hy => exact add_mem hx hy
    | tmul b t =>
      induction t using TensorProduct.induction_on with
      | zero => rw [TensorProduct.tmul_zero]; exact zero_mem _
      | add x y hx hy => rw [TensorProduct.tmul_add]; exact add_mem hx hy
      | tmul r w =>
        obtain ⟨x, hx⟩ := h1 (r • b)
        refine ⟨TensorProduct.assoc R R' B W (x ⊗ₜ w), ?_⟩
        have e1 : r ⊗ₜ[R] w = r • ((1 : R') ⊗ₜ[R] w) := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
        simp only [Ψ, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
          TensorProduct.lift.tmul, bil, LinearMap.mk₂_apply, hx, e1, ← TensorProduct.smul_tmul]
  let Θ : R' ⊗[R] (B ⊗[R] W) ≃ₗ[R] R' ⊗[R] Ω := (he.equiv.restrictScalars R).lTensor R'
  have hΘ : Function.Bijective (fun z ↦ liftSemi m (Θ z)) := h2.comp Θ.bijective
  have key : ∀ z, he'.equiv (LinearMap.lTensor B' (liftSemi p) (Ψ z)) = liftSemi m (Θ z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add, map_add, map_add, hx, hy, map_add, map_add]
    | tmul r t =>
      induction t using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy =>
        rw [TensorProduct.tmul_add, map_add, map_add, map_add, hx, hy, map_add, map_add]
      | tmul b w =>
        simp only [Ψ, Θ, bil, LinearMap.comp_apply, LinearEquiv.coe_coe,
          TensorProduct.assoc_symm_tmul, TensorProduct.lift.tmul, LinearMap.mk₂_apply,
          liftSemi_tmul, LinearMap.lTensor_tmul, LinearEquiv.lTensor_tmul,
          LinearEquiv.restrictScalars_apply, IsBaseChange.equiv_tmul, one_smul, hf, hp, hm,
          map_smul, smul_assoc]
  refine ⟨fun x y hxy ↦ ?_, fun q ↦ ?_⟩
  · obtain ⟨x0, rfl⟩ := hΨ x
    obtain ⟨y0, rfl⟩ := hΨ y
    have := hΘ.1 (show liftSemi m (Θ x0) = liftSemi m (Θ y0) by rw [← key, ← key, hxy])
    rw [this]
  · obtain ⟨z, hz⟩ := hΘ.2 (he'.equiv q)
    refine ⟨Ψ z, he'.equiv.injective ?_⟩
    rw [key]; exact hz

end GlobalTheory.AbCoh

namespace GlobalTheory.AbCoh

theorem lTensor_liftSemi_pullForm_bijective : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (X X' : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (φ : X' ⟶ X) (h : IsPullback φ s' s (spMap (algebraMap R R'))), HasFrame (OAff s) → CohomZeroIsConstants (OAff s) → HasFrame (OAff s') → CohomZeroIsConstants (OAff s') → ∀ U : X.affineOpens, IsAffineOpen (φ ⁻¹ᵁ U.1) → Function.Bijective (LinearMap.lTensor (Sec s' (φ ⁻¹ᵁ U.1)) (liftSemi (pullForm h.w))) := by
  intro R R' _ _ _ X X' s s' φ h hF hH hF' hH' U hU
  let U' : X'.affineOpens := ⟨φ ⁻¹ᵁ U.1, hU⟩
  let pr : Pair φ := ⟨(U', U), le_rfl⟩
  have hsemi : SemiHom (algebraMap R R') (GlobalTheory.CechDR.secPull s s' pr) := GlobalTheory.CechDR.semiHom_secPull h.w pr
  let f : Sec s U.1 →ₛₗ[algebraMap R R'] Sec s' (φ ⁻¹ᵁ U.1) :=
    { toFun := GlobalTheory.CechDR.secPull s s' pr, map_add' := map_add _, map_smul' := hsemi }
  have h1 : Function.Bijective (liftSemi f) :=
    GlobalTheory.CechDR.bijective_liftSemi_secPull R R' X X' s s' φ h pr rfl f (fun _ ↦ rfl)
  have h2 : Function.Bijective (liftSemi hsemi.m1) :=
    GlobalTheory.kaehler_liftSemi_bijective R R' _ _ (GlobalTheory.CechDR.secPull s s' pr) hsemi f (fun _ ↦ rfl) h1
  let e : GlobForm s →ₗ[R] Ω[Sec s U.1⁄R] :=
    { toFun := fun w ↦ w.1 (Opposite.op U), map_add' := fun _ _ ↦ rfl, map_smul' := fun _ _ ↦ rfl }
  have he : IsBaseChange (Sec s U.1) e :=
    isBaseChange_glob1 R (AffOp X) (OAff s) hF hH (Opposite.op U) e (fun _ ↦ rfl)
  let e' : GlobForm s' →ₗ[R'] Ω[Sec s' (φ ⁻¹ᵁ U.1)⁄R'] :=
    { toFun := fun w ↦ w.1 (Opposite.op U'), map_add' := fun _ _ ↦ rfl, map_smul' := fun _ _ ↦ rfl }
  have he' : IsBaseChange (Sec s' (φ ⁻¹ᵁ U.1)) e' :=
    isBaseChange_glob1 R' (AffOp X') (OAff s') hF' hH' (Opposite.op U') e' (fun _ ↦ rfl)
  exact lTensor_liftSemi_bijective_of_isBaseChange (GlobalTheory.CechDR.secPull s s' pr) f (fun _ ↦ rfl) h1.2 hsemi.m1
    (fun b ω ↦ hsemi.oneFormMap_smul_semilinear b ω) h2 e he e' he' (pullForm h.w)
    (fun w ↦ ((isPullForm_iff.1 (isPullForm_pullForm h.w w)) pr).symm)

end GlobalTheory.AbCoh
