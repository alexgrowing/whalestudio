import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.LowFockB
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.DSymmHypsInhabited
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.CFPrimeB

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ} {N : Type*} [AddCommGroup N] [Module ℂ N]

theorem lf_sgE_tensor (ε : Fin n → Bool) (a b : Fin n) :
    sgE ε (cpT (N := N) (n := n)) cmT a b = TensorProduct.map LinearMap.id (sgE ε cpFock cmFock a b) := by
  have hcp : ∀ i c : Fin n, cpT (N := N) i c = LinearMap.lTensor N (cpFock i c) := fun _ _ => rfl
  have hcm : ∀ i c : Fin n, cmT (N := N) i c = LinearMap.lTensor N (cmFock i c) := fun _ _ => rfl
  have hsum : ∀ (s : Finset (Fin n)) (F : Fin n → Module.End ℂ (Fock n)),
      LinearMap.lTensor N (∑ x ∈ s, F x) = ∑ x ∈ s, LinearMap.lTensor N (F x) :=
    fun s F => map_sum (LinearMap.lTensorHom N) F s
  rw [show TensorProduct.map LinearMap.id (sgE ε cpFock cmFock a b) =
    LinearMap.lTensor N (sgE ε cpFock cmFock a b) from rfl]
  unfold sgE
  split_ifs
  · rw [hsum]
    simp only [hcp, hcm, LinearMap.lTensor_mul]
  · rw [LinearMap.lTensor_neg, hsum]
    simp only [hcp, hcm, LinearMap.lTensor_mul]
  · rw [LinearMap.lTensor_zero]

theorem lf_diagE_tensor (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ N) (a b : Fin n) :
    diagE ε (eT E) cpT cmT a b =
      TensorProduct.map (E a b) LinearMap.id + TensorProduct.map LinearMap.id (sgE ε cpFock cmFock a b) := by
  unfold diagE
  rw [lf_sgE_tensor]
  rfl

def lfLift (ε : Fin n → Bool) (x : LfIdx ε → N) : TensorProduct ℂ N (Fock n) :=
  ∑ S, x S ⊗ₜ[ℂ] fockBasis n S.1

theorem lfLift_mem_tensFock (ε : Fin n → Bool) {V : Submodule ℂ N} {x : LfIdx ε → N} (hx : ∀ S, x S ∈ V) :
    lfLift ε x ∈ tensFock (n := n) V := by
  unfold lfLift tensFock
  refine Submodule.sum_mem _ fun S _ => ⟨⟨x S, hx S⟩ ⊗ₜ fockBasis n S.1, ?_⟩
  simp [TensorProduct.map_tmul]

theorem lfLift_mem_physSub (ε : Fin n → Bool) (x : LfIdx ε → N) : lfLift ε x ∈ physicalSubspace (N := N) ε := by
  simp only [physicalSubspace, Submodule.mem_iInf, LinearMap.mem_ker]
  intro i a hia
  simp only [lfLift, map_sum, cmT, TensorProduct.map_tmul, LinearMap.id_apply]
  refine Finset.sum_eq_zero fun S _ => ?_
  have hS : finProdFinEquiv (i, a) ∉ S.1 := by
    intro h
    have := S.2 h
    simp only [lfPhysModes, Finset.mem_filter, Equiv.symm_apply_apply] at this
    exact hia this.2
  rw [lf_cm_basis_of_not_mem (x := (i, a)) hS, TensorProduct.tmul_zero]

theorem lfLift_tcoef (ε : Fin n → Bool) (x : LfIdx ε → N) (S : LfIdx ε) :
    tcoef ((fockBasis n).coord S.1) (lfLift ε x) = x S := by
  simp only [lfLift, map_sum, tcoef, LinearMap.coe_comp, Function.comp_apply, TensorProduct.map_tmul,
    LinearMap.id_apply, LinearEquiv.coe_coe, TensorProduct.rid_tmul, Module.Basis.coord_apply, Module.Basis.repr_self]
  rw [Finset.sum_eq_single S (fun T _ hT => by
    rw [Finsupp.single_apply, if_neg (fun h => hT (Subtype.ext h)), zero_smul]) (by simp)]
  simp

theorem lfLift_ne_zero (ε : Fin n → Bool) {x : LfIdx ε → N} (hx : x ≠ 0) : lfLift ε x ≠ 0 := by
  intro h0
  apply hx
  funext S
  have h1 := lfLift_tcoef ε x S
  rw [h0, map_zero] at h1
  exact h1.symm

theorem lfLift_diagE (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ N) (a b : Fin n)
    (x : LfIdx ε → N) :
    diagE ε (eT E) cpT cmT a b (lfLift ε x) =
      lfLift ε (fun T => E a b (x T) + ∑ S, lfMat ε a b T S • x S) := by
  rw [lf_diagE_tensor, LinearMap.add_apply]
  unfold lfLift
  rw [map_sum, map_sum]
  simp only [TensorProduct.map_tmul, LinearMap.id_apply]
  simp only [lfMat_basis, TensorProduct.tmul_sum, TensorProduct.tmul_smul]
  simp only [TensorProduct.add_tmul, Finset.sum_add_distrib, TensorProduct.sum_tmul,
    ← TensorProduct.smul_tmul']
  rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ) (f := fun S T => lfMat ε a b T S • (x S ⊗ₜ[ℂ] fockBasis n T.1))]

theorem lfLift_smul (ε : Fin n → Bool) (c : ℂ) (x : LfIdx ε → N) :
    lfLift ε (fun T => c • x T) = c • lfLift ε x := by
  simp only [lfLift, Finset.smul_sum, TensorProduct.smul_tmul']

theorem lfLift_isKHWVec (ε : Fin n → Bool) {E : Fin n → Fin n → Module.End ℂ N} {μ : Fin n → ℝ}
    {x : LfIdx ε → N}
    (hw : ∀ a S, E a a (x S) + ∑ T, lfMat ε a a S T • x T = ((μ a : ℝ) : ℂ) • x S)
    (hh : ∀ a b, a < b → ε a = ε b → ∀ S, E a b (x S) + ∑ T, lfMat ε a b S T • x T = 0) :
    IsKHWVec ε (diagE ε (eT E) cpT cmT) μ (lfLift ε x) := by
  refine ⟨fun a => ?_, fun a b hab hε => ?_⟩
  · rw [lfLift_diagE]
    have h1 : (fun T => E a a (x T) + ∑ S, lfMat ε a a T S • x S) = fun T => ((μ a : ℝ) : ℂ) • x T :=
      funext fun T => hw a T
    rw [h1, lfLift_smul]
  · rw [lfLift_diagE]
    have h1 : (fun T => E a b (x T) + ∑ S, lfMat ε a b T S • x S) = fun _ => 0 :=
      funext fun T => hh a b hab hε T
    rw [h1]
    simp [lfLift]

end ReciprocityTheory.ChartRestriction.DS
