import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.IsLocalHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.ClFin

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.CA ReciprocityTheory.CA

private theorem base_change_residue_surjective (O' R T : Type) [CommRing O'] [IsLocalRing O'] [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [CommRing T] [Algebra O' T] [Algebra R T]
    [Module.Finite R T] (φ : T →+* ResidueField O') (hφ : ∀ a, φ (algebraMap O' T a) = residue O' a)
    (hm : ∀ r ∈ maximalIdeal R, φ (algebraMap R T r) = 0)
    (hs : ∀ x : T, ∃ a : O', x - algebraMap O' T a ∈ (maximalIdeal R).map (algebraMap R T)) :
    IsCO O' T := by
  have hJ : (maximalIdeal R).map (algebraMap R T) ≤ Ideal.jacobson ⊥ := by
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    rw [Ideal.mem_comap, Ideal.jacobson, Submodule.mem_sInf]
    rintro P ⟨-, hP⟩
    have h1 : Ideal.comap (algebraMap R T) P = maximalIdeal R :=
      IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := R) P)
    rw [← Ideal.mem_comap, h1]
    exact hr
  haveI : Nontrivial T := by
    refine ⟨⟨0, 1, fun h => ?_⟩⟩
    have h2 := congrArg φ h
    rw [map_zero, map_one] at h2
    exact zero_ne_one h2
  have key : ∀ (u y : T), IsUnit u → y ∈ Ideal.jacobson (⊥ : Ideal T) → IsUnit (u + y) := by
    intro u y hu hy
    obtain ⟨v, rfl⟩ := hu
    have h3 := (Ideal.mem_jacobson_bot.mp hy) ↑v⁻¹
    have e : (v : T) + y = v * (y * ↑v⁻¹ + 1) := by
      rw [mul_add, mul_one, mul_comm y, ← mul_assoc, Units.mul_inv, one_mul, add_comm]
    rw [e]
    exact v.isUnit.mul h3
  haveI : IsLocalRing T := by
    refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => ?_
    obtain ⟨a, ha⟩ := hs x
    rcases IsLocalRing.isUnit_or_isUnit_one_sub_self a with h | h
    · left
      have h4 := key _ _ (h.map (algebraMap O' T)) (hJ ha)
      rwa [add_sub_cancel] at h4
    · right
      have h4 := key _ _ (h.map (algebraMap O' T)) (hJ (neg_mem ha))
      convert h4 using 1
      rw [map_sub, map_one]
      ring
  have hR : IsCL R R := by
    refine ⟨inferInstance, inferInstance, ?_, ?_⟩
    · rw [Algebra.algebraMap_self]
      infer_instance
    · infer_instance
  have hT : IsCL R T := cl_fin R R T hR
  haveI : IsNoetherianRing T := hT.noeth
  refine ⟨hT.complete, ?_, ?_⟩
  · refine ⟨fun a ha => ?_⟩
    have h5 := ha.map φ
    rw [hφ] at h5
    exact (IsLocalRing.residue_ne_zero_iff_isUnit a).mp h5.ne_zero
  · intro x
    obtain ⟨a, ha⟩ := hs x
    refine ⟨a, ?_⟩
    have h6 : (maximalIdeal R).map (algebraMap R T) ≤ maximalIdeal T := by
      rw [Ideal.map_le_iff_le_comap]
      intro r hr
      rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      have h7 := hu.map φ
      rw [hm r hr] at h7
      exact not_isUnit_zero h7
    exact h6 ha

theorem UpperTheory.V.CA.cl_bc :
    ∀ (O O' R : Type) [CommRing O] [IsLocalRing O] [CommRing O'] [IsLocalRing O'] [Algebra O O'] [Module.Finite O O'] [IsLocalHom (algebraMap O O')] [CommRing R] [Algebra O R] [IsCO O R], IsCO O' (TensorProduct O O' R) := by
  intro O O' R _ _ _ _ _ _ _ _ _ _
  letI : Algebra R (TensorProduct O O' R) := Algebra.TensorProduct.rightAlgebra
  have hR : ∀ r : R, algebraMap R (TensorProduct O O' R) r = 1 ⊗ₜ r := fun r => rfl
  have hL : ∀ x : O', algebraMap O' (TensorProduct O O' R) x = x ⊗ₜ 1 := fun x => rfl
  haveI : Module.Finite R (TensorProduct O O' R) := by
    let c := Algebra.TensorProduct.comm O R O'
    let e : TensorProduct O R O' →ₗ[R] TensorProduct O O' R :=
      { toFun := c
        map_add' := map_add c
        map_smul' := fun r y => by
          rw [Algebra.smul_def, Algebra.smul_def, map_mul]
          congr 1 }
    exact Module.Finite.of_surjective e c.surjective
  haveI : IsNoetherianRing R := inferInstance
  haveI : IsAdicComplete (maximalIdeal R) R := IsCO.complete (O := O)
  let f : O' →ₐ[O] ResidueField O' := IsScalarTower.toAlgHom O O' (ResidueField O')
  let g : R →ₐ[O] ResidueField O' :=
    (IsScalarTower.toAlgHom O (ResidueField O) (ResidueField O')).comp (res O R)
  let φ : TensorProduct O O' R →+* ResidueField O' := (Algebra.TensorProduct.productMap f g).toRingHom
  refine base_change_residue_surjective O' R (TensorProduct O O' R) φ ?_ ?_ ?_
  · intro a
    simp [φ, f, g]
  · intro r hr
    have h1 : res O R r = 0 := (res_eq_zero_iff O R r).mpr hr
    show Algebra.TensorProduct.productMap f g (algebraMap R (TensorProduct O O' R) r) = 0
    rw [hR, Algebra.TensorProduct.productMap_apply_tmul]
    simp [g, h1]
  · intro x
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul o r =>
      obtain ⟨c, hc⟩ := IsCO.res_surj (O := O) r
      refine ⟨algebraMap O O' c * o, ?_⟩
      have e2 : o ⊗ₜ[O] r - algebraMap O' (TensorProduct O O' R) (algebraMap O O' c * o) =
          algebraMap O' (TensorProduct O O' R) o * algebraMap R (TensorProduct O O' R) (r - algebraMap O R c) := by
        rw [hR, hL, hL, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, TensorProduct.tmul_sub,
          ← Algebra.smul_def, TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one]
      rw [e2]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hc)
    | add x y hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      refine ⟨a + b, ?_⟩
      have e3 : x + y - algebraMap O' (TensorProduct O O' R) (a + b) =
          (x - algebraMap O' (TensorProduct O O' R) a) + (y - algebraMap O' (TensorProduct O O' R) b) := by
        rw [map_add]
        ring
      rw [e3]
      exact add_mem ha hb
