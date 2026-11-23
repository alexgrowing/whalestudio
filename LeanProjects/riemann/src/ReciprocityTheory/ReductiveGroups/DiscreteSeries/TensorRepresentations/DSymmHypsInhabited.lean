import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.InhabCAR
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.CARUnit
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.FockTA

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ} {N : Type*} [AddCommGroup N] [Module ℂ N]

def eT (E : Fin n → Fin n → Module.End ℂ N) (a b : Fin n) : Module.End ℂ (TensorProduct ℂ N (Fock n)) :=
  TensorProduct.map (E a b) LinearMap.id

def cpT (i a : Fin n) : Module.End ℂ (TensorProduct ℂ N (Fock n)) := TensorProduct.map LinearMap.id (cpFock i a)

def cmT (i a : Fin n) : Module.End ℂ (TensorProduct ℂ N (Fock n)) := TensorProduct.map LinearMap.id (cmFock i a)

def gradT : Module.End ℂ (TensorProduct ℂ N (Fock n)) :=
  TensorProduct.map LinearMap.id (CliffordAlgebra.involute : Fock n →ₐ[ℂ] Fock n).toLinearMap

def physicalSubspace (ε : Fin n → Bool) : Submodule ℂ (TensorProduct ℂ N (Fock n)) :=
  ⨅ i : Fin n, ⨅ a : Fin n, ⨅ (_ : ¬ (ε i = true ∧ ε a = false)), LinearMap.ker (cmT (N := N) i a)

def tensFock (V : Submodule ℂ N) : Submodule ℂ (TensorProduct ℂ N (Fock n)) :=
  LinearMap.range (TensorProduct.map V.subtype (LinearMap.id : Fock n →ₗ[ℂ] Fock n))

theorem gradT_eq : gradT (N := N) (n := n) =
    Module.End.lTensorAlgHom ℂ (Fock n) N (CliffordAlgebra.involute : Fock n →ₐ[ℂ] Fock n).toLinearMap := rfl

theorem mem_physicalSubspace_iff (ε : Fin n → Bool) (x : TensorProduct ℂ N (Fock n)) :
    x ∈ physicalSubspace (N := N) ε ↔ ∀ j b, ¬(ε j = true ∧ ε b = false) → cmT j b x = 0 := by
  simp only [physicalSubspace, Submodule.mem_iInf, LinearMap.mem_ker]

theorem gradT_cpT (i a : Fin n) : gradT (N := N) * cpT i a = -(cpT i a * gradT) := by
  have h := congrArg (Module.End.lTensorAlgHom ℂ (Fock n) N) (fock_inv_cp (n := n) i a)
  simp only [map_neg, map_mul] at h
  exact h

theorem gradT_cmT (i a : Fin n) : gradT (N := N) * cmT i a = -(cmT i a * gradT) := by
  have h := congrArg (Module.End.lTensorAlgHom ℂ (Fock n) N) (fock_inv_cm (n := n) i a)
  simp only [map_neg, map_mul] at h
  exact h

theorem eT_gradT (E : Fin n → Fin n → Module.End ℂ N) (a b : Fin n) : eT E a b * gradT = gradT * eT E a b :=
  TensorProduct.ext' fun x y => by simp [eT, gradT, TensorProduct.map_tmul]

theorem eT_isGlRep {E : Fin n → Fin n → Module.End ℂ N} (hE : IsGlRep E) : IsGlRep (eT (n := n) E) := by
  intro a b c d
  have h := congrArg (Module.End.rTensorAlgHom ℂ N (Fock n)) (hE a b c d)
  rw [map_sub, map_sub, map_mul, map_mul] at h
  refine h.trans ?_
  congr 1 <;> split_ifs <;> first | rfl | simp

theorem cpT_cmT_isCAR : IsCAR (cpT (N := N) (n := n)) cmT := by
  intro i a j b
  obtain ⟨h1, h2, h3⟩ := isCAR_fock (n := n) i a j b
  refine ⟨?_, ?_, ?_⟩
  · have h := congrArg (Module.End.lTensorAlgHom ℂ (Fock n) N) h1
    simp only [map_add, map_mul, map_zero] at h
    exact h
  · have h := congrArg (Module.End.lTensorAlgHom ℂ (Fock n) N) h2
    simp only [map_add, map_mul, map_zero] at h
    exact h
  · have h := congrArg (Module.End.lTensorAlgHom ℂ (Fock n) N) h3
    rw [map_add, map_mul, map_mul] at h
    refine h.trans ?_
    split_ifs <;> simp

theorem eT_commutesCAR (E : Fin n → Fin n → Module.End ℂ N) : CommutesCAR (eT E) cpT cmT := by
  intro a b i j
  refine ⟨TensorProduct.ext' fun x y => ?_, TensorProduct.ext' fun x y => ?_⟩ <;>
    simp [eT, cpT, cmT, TensorProduct.map_tmul]

theorem physSub_stable (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ N) :
    (∀ a b, ∀ x ∈ physicalSubspace (N := N) ε, eT E a b x ∈ physicalSubspace ε) ∧
      (∀ a b, ∀ x ∈ physicalSubspace (N := N) ε, diagE ε (eT E) cpT cmT a b x ∈ physicalSubspace ε) ∧
      (∀ x ∈ physicalSubspace (N := N) ε, dOp ε (eT E) cpT x ∈ physicalSubspace ε) ∧
      (∀ x ∈ physicalSubspace (N := N) ε, dOp' ε (eT E) cmT x ∈ physicalSubspace ε) ∧
      ∀ x ∈ physicalSubspace (N := N) ε, gradT x ∈ physicalSubspace ε := by
  have hC := cpT_cmT_isCAR (N := N) (n := n)
  have hK := eT_commutesCAR (N := N) E
  refine ⟨fun a c x hx => ?_, fun a c x hx => ?_, fun x hx => ?_, fun x hx => ?_, fun x hx => ?_⟩ <;>
    rw [mem_physicalSubspace_iff] at hx ⊢ <;> intro j b hjb
  · exact (fockT_stable_gen hC hK ε hjb hx).1 a c
  · exact (fockT_stable_gen hC hK ε hjb hx).2.1 a c
  · exact (fockT_stable_gen hC hK ε hjb hx).2.2.1
  · exact (fockT_stable_gen hC hK ε hjb hx).2.2.2
  · have h := LinearMap.congr_fun (gradT_cmT (N := N) j b) x
    simp only [Module.End.mul_apply, LinearMap.neg_apply] at h
    rw [← neg_neg (cmT j b (gradT x)), ← h, hx j b hjb, map_zero, neg_zero]

theorem gradT_props (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ N) :
    gradT (N := N) (n := n) * gradT = 1 ∧ gradT * dOp ε (eT E) cpT = -(dOp ε (eT E) cpT * gradT) ∧
      gradT * dOp' ε (eT E) cmT = -(dOp' ε (eT E) cmT * gradT) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [gradT_eq, ← map_mul, fock_inv_sq, map_one]
  · exact fockT_anti_sum _ _ _ (fun i a => eT E a i) (fun i a => cpT i a) (fun i a => (eT_gradT E a i).symm)
      (fun i a => gradT_cpT i a)
  · simp only [dOp', mul_neg, neg_mul]
    rw [fockT_anti_sum _ _ _ (fun i a => eT E i a) (fun i a => cmT i a) (fun i a => (eT_gradT E i a).symm)
      (fun i a => gradT_cmT i a)]

end ReciprocityTheory.ChartRestriction.DS
