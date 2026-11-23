import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TupleActions.InstMulActionTup
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConvexNerveComplexes.SimpSmul

open NumberField UpperTheory.V UpperTheory.V.KT UpperTheory.V.Af.BA

set_option maxHeartbeats 1000000 in
theorem UpperTheory.real_structure_action_of_real_involution :
    UpperTheory.V.Af.BA.ReInv → UpperTheory.V.Af.BA.ActRe := by
  intro hR L _ _ N σ hσ
  have hHR : ∀ (g : Fix N σ) (h : HR L N), (g : Gm L N) • (h : HS L N) ∈ HR L N :=
    fun g h => ((hR L N σ hσ).2 h h.2).2 g g.2
  have hinv : ∀ (g : Fix N σ) (h : HS L N), ((g⁻¹ : Fix N σ) : Gm L N) • (g : Gm L N) • h = h := by
    intro g h
    rw [← mul_smul, Subgroup.coe_inv, inv_mul_cancel, one_smul]
  have hinv' : ∀ (g : Fix N σ) (h : HS L N), (g : Gm L N) • ((g⁻¹ : Fix N σ) : Gm L N) • h = h := by
    intro g h
    rw [← mul_smul, Subgroup.coe_inv, mul_inv_cancel, one_smul]
  let E : Fix N σ → (HR L N ≃L[ℝ] HR L N) := fun g =>
    LinearEquiv.toContinuousLinearEquiv
      { toFun := fun h => ⟨(g : Gm L N) • (h : HS L N), hHR g h⟩
        invFun := fun h => ⟨((g⁻¹ : Fix N σ) : Gm L N) • (h : HS L N), hHR g⁻¹ h⟩
        map_add' := by
          intro a b
          apply Subtype.ext
          simp only [Submodule.coe_add]
          rw [← actL_apply, ← actL_apply, ← actL_apply, map_add]
        map_smul' := by
          intro c a
          apply Subtype.ext
          simp only [Submodule.coe_smul, RingHom.id_apply]
          rw [← actL_apply, ← actL_apply, map_smul]
        left_inv := by
          intro h
          apply Subtype.ext
          exact hinv g h
        right_inv := by
          intro h
          apply Subtype.ext
          exact hinv' g h }
  have hE : ∀ (g : Fix N σ) (h : HR L N), ((E g h : HR L N) : HS L N) = (g : Gm L N) • (h : HS L N) :=
    fun g h => rfl
  let π : Fix N σ → (NZ L N ≃ NZ L N) := fun g =>
    { toFun := fun y => ⟨(g : Gm L N) • (y : Lat L N), smul_ne_zero_lat _ y.2⟩
      invFun := fun y => ⟨((g⁻¹ : Fix N σ) : Gm L N) • (y : Lat L N), smul_ne_zero_lat _ y.2⟩
      left_inv := by
        intro y
        apply Subtype.ext
        show ((g⁻¹ : Fix N σ) : Gm L N) • (g : Gm L N) • (y : Lat L N) = y
        rw [← mul_smul, Subgroup.coe_inv, inv_mul_cancel, one_smul]
      right_inv := by
        intro y
        apply Subtype.ext
        show (g : Gm L N) • ((g⁻¹ : Fix N σ) : Gm L N) • (y : Lat L N) = y
        rw [← mul_smul, Subgroup.coe_inv, mul_inv_cancel, one_smul] }
  have hq : ∀ (g : Fix N σ) (y : NZ L N) (h : HR L N), (qr L N (π g y)) (E g h) = (qr L N y) h := by
    intro g y h
    rw [qr_apply, qr_apply, hE]
    show q ((g : Gm L N) • (h : HS L N)) ((g : Gm L N) • (y : Lat L N)) = q (h : HS L N) (y : Lat L N)
    rw [q_smul, ← mul_smul, inv_mul_cancel, one_smul]
  have hT : ∀ (g : Fix N σ) (k : HR L N), E g k ∈ Tr L N ↔ k ∈ Tr L N := by
    intro g k
    constructor
    · intro hk
      change ((E g k : HR L N) : HS L N) ∈ Psd L N at hk
      rw [hE] at hk
      have h1 := smul_mem_Psd ((g : Gm L N))⁻¹ hk
      rw [← mul_smul, inv_mul_cancel, one_smul] at h1
      exact h1
    · intro hk
      show ((E g k : HR L N) : HS L N) ∈ Psd L N
      rw [hE]
      exact smul_mem_Psd _ hk
  have key := fun g => ConeExtensionAcyclic.simp_smul (E g) (π g) (hq g) (hT g)
  let inst : MulAction (Fix N σ) (ConeExtensionAcyclic.Vert (qr L N)) :=
    { smul := fun g v => ⟨E g v.1, (key g).1 v.1 v.2⟩
      one_smul := by
        intro v
        apply Subtype.ext
        apply Subtype.ext
        show ((1 : Fix N σ) : Gm L N) • ((v.1 : HR L N) : HS L N) = _
        rw [OneMemClass.coe_one, one_smul]
      mul_smul := by
        intro g g' v
        apply Subtype.ext
        apply Subtype.ext
        show ((g * g' : Fix N σ) : Gm L N) • ((v.1 : HR L N) : HS L N) =
          (g : Gm L N) • (g' : Gm L N) • ((v.1 : HR L N) : HS L N)
        rw [Subgroup.coe_mul, mul_smul] }
  refine ⟨inst, fun g v => rfl, ?_⟩
  intro n g t ht
  exact (key g).2 n t _ (fun j => rfl) ht
