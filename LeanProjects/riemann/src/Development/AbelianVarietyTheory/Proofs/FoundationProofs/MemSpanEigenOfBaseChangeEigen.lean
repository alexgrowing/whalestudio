import Mathlib

open scoped TensorProduct

namespace GlobalTheory

theorem mem_span_eigen_of_baseChange_eigen (l : ℕ) [Fact l.Prime] (M S : Type) [AddCommGroup M]
    [Module ℤ_[l] M] (B : Submodule ℤ_[l] M) [Module.Free ℤ_[l] B]
    (g : S → Module.End ℤ_[l] M) (χ : S → ℤ_[l]) (hB : ∀ s, ∀ b ∈ B, g s b ∈ B)
    (x : PadicAlgCl l ⊗[ℤ_[l]] M)
    (hx : x ∈ LinearMap.range (LinearMap.baseChange (PadicAlgCl l) B.subtype))
    (he : ∀ s, LinearMap.baseChange (PadicAlgCl l) (g s) x
      = algebraMap ℤ_[l] (PadicAlgCl l) (χ s) • x) :
    x ∈ Submodule.span (PadicAlgCl l)
      {y | ∃ b ∈ B, (∀ s, g s b = χ s • b) ∧ y = (1 : PadicAlgCl l) ⊗ₜ[ℤ_[l]] b} := by
  classical
  obtain ⟨x', rfl⟩ := hx
  have hinj0 : Function.Injective (algebraMap ℤ_[l] (PadicAlgCl l)) := by
    rw [IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] (PadicAlgCl l), RingHom.coe_comp]
    exact (algebraMap ℚ_[l] (PadicAlgCl l)).injective.comp (IsFractionRing.injective ℤ_[l] ℚ_[l])
  haveI : FaithfulSMul ℤ_[l] (PadicAlgCl l) := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj0
  haveI : Module.IsTorsionFree ℤ_[l] (PadicAlgCl l) := inferInstance
  haveI : Module.Flat ℤ_[l] (PadicAlgCl l) := inferInstance
  obtain ⟨P, hP, z, rfl⟩ := Submodule.exists_fg_le_eq_rTensor_subtype x'
  haveI : Module.Finite ℤ_[l] P := Module.Finite.iff_fg.2 hP
  haveI : Module.Free ℤ_[l] P := inferInstance
  let ω := Module.Free.chooseBasis ℤ_[l] P
  let Φ : P ⊗[ℤ_[l]] B →ₗ[ℤ_[l]] PadicAlgCl l ⊗[ℤ_[l]] M :=
    (B.subtype.lTensor (PadicAlgCl l)) ∘ₗ (P.subtype.rTensor B)
  have hΦ : Function.Injective Φ :=
    (Module.Flat.lTensor_preserves_injective_linearMap _ B.injective_subtype).comp
      (Module.Flat.rTensor_preserves_injective_linearMap _ P.injective_subtype)
  have hΦz : ∀ w, LinearMap.baseChange (PadicAlgCl l) B.subtype (P.subtype.rTensor B w) = Φ w :=
    fun w => rfl
  have hΦt : ∀ (a : P) (b : B), Φ (a ⊗ₜ b) = (a : PadicAlgCl l) ⊗ₜ (b : M) := fun a b => rfl
  rw [hΦz] at he ⊢
  let h : S → Module.End ℤ_[l] B := fun s => (g s).restrict (hB s) - χ s • LinearMap.id
  have hcomm : ∀ s w, Φ ((h s).lTensor P w)
      = LinearMap.baseChange (PadicAlgCl l) (g s) (Φ w) - χ s • Φ w := by
    intro s w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      rw [LinearMap.lTensor_tmul, hΦt, hΦt, LinearMap.baseChange_tmul, ← TensorProduct.tmul_smul,
        ← TensorProduct.tmul_sub]
      rfl
    | add u v hu hv => simp only [map_add, hu, hv, smul_add]; abel
  have hz : ∀ s, (h s).lTensor P z = 0 := by
    intro s
    apply hΦ
    rw [hcomm, he s, algebraMap_smul, sub_self, map_zero]
  obtain ⟨c, rfl⟩ := (TensorProduct.equivFinsuppOfBasisLeft (N := B) ω).symm.surjective z
  have hc : ∀ s i, h s (c i) = 0 := by
    intro s i
    have e : (h s).lTensor P ((TensorProduct.equivFinsuppOfBasisLeft (N := B) ω).symm c)
        = (TensorProduct.equivFinsuppOfBasisLeft (N := B) ω).symm
          (c.mapRange (h s) (map_zero _)) := by
      rw [TensorProduct.equivFinsuppOfBasisLeft_symm_apply,
        TensorProduct.equivFinsuppOfBasisLeft_symm_apply,
        Finsupp.sum_mapRange_index (fun _ => TensorProduct.tmul_zero _ _), map_finsuppSum]
      rfl
    have e2 := hz s
    rw [e, LinearEquiv.map_eq_zero_iff] at e2
    simpa using DFunLike.congr_fun e2 i
  rw [TensorProduct.equivFinsuppOfBasisLeft_symm_apply, map_finsuppSum]
  refine Submodule.sum_mem _ fun i _ => ?_
  have e : Φ (ω i ⊗ₜ c i) = (ω i : PadicAlgCl l) • ((1 : PadicAlgCl l) ⊗ₜ[ℤ_[l]] (c i : M)) := by
    rw [hΦt, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  change Φ (ω i ⊗ₜ c i) ∈ _
  rw [e]
  refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨c i, (c i).2, fun s => ?_, rfl⟩)
  have := congrArg Subtype.val (hc s i)
  exact sub_eq_zero.1 this

end GlobalTheory
