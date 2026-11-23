import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSplitFinMulSplitInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteLeftOfFiniteTensorProductComplex
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicMapPhiInjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VectorFormTensorRangeLeUnitaryAutFormsWeightLeveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAutFormsWeightLevelLeTensorRangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryHeckeOperatorVectorMemLevelFunctionsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryHeckeOperatorCommuteWeightVectorFunctionEStatement

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.TrKer

theorem trace_map_id {M W : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] (A : M →ₗ[ℂ] M) :
    LinearMap.trace ℂ (M ⊗[ℂ] W) (TensorProduct.map A LinearMap.id) =
      LinearMap.trace ℂ M A * Module.finrank ℂ W := by
  rw [GlobalTheory.trace_tensorProduct_map_complex, LinearMap.trace_id]

theorem trOn_forms_eq_finrank_mul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ f : ∀ w : Pl E, UL n w → ℂ, IsTest (KL n) K' f → trOn (forms S lam K') (hop S K' f) = (Module.finrank ℂ (GlobalTheory.BCT.TrKer.Wsp lam) : ℂ) * trOn (GlobalTheory.BCT.TrKer.vecM S lam K') (GlobalTheory.BCT.TrKer.hopM S lam K' f) := by
  intro E _ _ _ hE n hn S hS lam K' hK f hf
  have hinj := GlobalTheory.T.automorphic_map_phi_injective E hE n hn S hS lam K' hK
  have hrange : LinearMap.range (Phi S lam K') = forms S lam K' :=
    le_antisymm (GlobalTheory.T.vectorFormTensor_range_le_unitaryAutFormsWeightLevel E hE n hn S hS lam K' hK) (GlobalTheory.T.unitaryAutForms_weight_level_le_tensor_range E hE n hn S hS lam K' hK)
  have hM := GlobalTheory.T.unitaryHeckeOperatorVector_mem_levelFunctions E n S lam K' hK f hf
  let A := (hopM S lam K' f).restrict hM
  have hcomm : ∀ x, hop S K' f (Phi S lam K' x) = Phi S lam K' (TensorProduct.map A LinearMap.id x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul F w =>
      rw [TensorProduct.map_tmul, Phi_tmul, Phi_tmul, GlobalTheory.T.unitaryHeckeOperator_commute_weightVectorFunction_explicit]
      rfl
    | add x y hx hy => rw [map_add, map_add, map_add, hx, hy, map_add]
  have hF : ∀ v ∈ forms S lam K', hop S K' f v ∈ forms S lam K' := by
    intro v hv
    rw [← hrange] at hv ⊢
    obtain ⟨x, rfl⟩ := hv
    exact ⟨_, (hcomm x).symm⟩
  obtain ⟨e, hev⟩ : ∃ e : (vecM S lam K' ⊗[ℂ] Wsp lam) ≃ₗ[ℂ] forms S lam K',
      ∀ y, ((e y : forms S lam K') : UA E n → ℂ) = Phi S lam K' y :=
    ⟨(LinearEquiv.ofInjective _ hinj).trans (LinearEquiv.ofEq _ _ hrange), fun y => rfl⟩
  have he : (hop S K' f).restrict hF = e.conj (TensorProduct.map A LinearMap.id) := by
    refine LinearMap.ext fun v => Subtype.ext ?_
    have hv : (v : UA E n → ℂ) = Phi S lam K' (e.symm v) :=
      (congrArg (fun u : forms S lam K' => (u : UA E n → ℂ)) (e.apply_symm_apply v)).symm.trans (hev _)
    calc (((hop S K' f).restrict hF v : forms S lam K') : UA E n → ℂ) = hop S K' f v :=
          LinearMap.restrict_coe_apply _ _ v
      _ = hop S K' f (Phi S lam K' (e.symm v)) := congrArg _ hv
      _ = Phi S lam K' (TensorProduct.map A LinearMap.id (e.symm v)) := hcomm _
      _ = ((e (TensorProduct.map A LinearMap.id (e.symm v)) : forms S lam K') : UA E n → ℂ) := (hev _).symm
      _ = ((e.conj (TensorProduct.map A LinearMap.id) v : forms S lam K') : UA E n → ℂ) :=
          congrArg (fun u : forms S lam K' => (u : UA E n → ℂ)) (LinearEquiv.conj_apply_apply _ _ _).symm
  have h1 : trOn (forms S lam K') (hop S K' f) = LinearMap.trace ℂ _ ((hop S K' f).restrict hF) := dif_pos hF
  have h2 : trOn (vecM S lam K') (hopM S lam K' f) = LinearMap.trace ℂ _ A := dif_pos hM
  rw [h1, h2]
  exact (congrArg (LinearMap.trace ℂ _) he).trans
    ((LinearMap.trace_conj' _ e).trans ((trace_map_id A).trans (mul_comm _ _)))

end GlobalTheory.BCT.TrKer
