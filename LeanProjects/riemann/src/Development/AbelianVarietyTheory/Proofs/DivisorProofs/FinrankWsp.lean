import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernSum

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.TrKer

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

abbrev Wsp (lam : InfinitePlace E → DomWeight n) : Type :=
  PiTensorProduct ℂ fun v : InfinitePlace E => nablaSq ℂ n (lam v)

def wAt (lam : InfinitePlace E → DomWeight n) (γ : UE E n) : Wsp lam →ₗ[ℂ] Wsp lam :=
  PiTensorProduct.map fun v => GlobalTheory.Branching.sqRep ℂ n (lam v) (GeneralLinearGroup.map v.embedding γ.1)

def vecM (S : Set (Pl E)) (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w)) :
    Submodule ℂ (finU E n → Module.Dual ℂ (Wsp lam)) where
  carrier := {F | (∀ (γ : UE E n) x, F (finPt γ * x) = (wAt lam γ⁻¹).dualMap (F x)) ∧
    ∀ k ∈ globLev S K', ∀ x, F (x * k) = F x}
  add_mem' := by
    intro a b ha hb
    refine ⟨fun γ x => ?_, fun k hk x => ?_⟩
    · simp only [Pi.add_apply, ha.1 γ x, hb.1 γ x, map_add]
    · simp only [Pi.add_apply, ha.2 k hk x, hb.2 k hk x]
  zero_mem' := ⟨fun _ _ => by simp, fun _ _ _ => rfl⟩
  smul_mem' := by
    intro c a ha
    refine ⟨fun γ x => ?_, fun k hk x => ?_⟩
    · simp only [Pi.smul_apply, ha.1 γ x, map_smul]
    · simp only [Pi.smul_apply, ha.2 k hk x]

def hopM (S : Set (Pl E)) (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w))
    (f : ∀ w : Pl E, UL n w → ℂ) :
    (finU E n → Module.Dual ℂ (Wsp lam)) →ₗ[ℂ] (finU E n → Module.Dual ℂ (Wsp lam)) :=
  levOp (rightReg ℂ (finU E n) (Module.Dual ℂ (Wsp lam))) (globLev S (KL n)) (globLev S K') (globFn S f)
    LinearMap.id

end GlobalTheory.BCT.TrKer

namespace GlobalTheory.BCT.TrKer

theorem trace_piMap {ι : Type} [Fintype ι] {M : ι → Type} [∀ c, AddCommGroup (M c)] [∀ c, Module ℂ (M c)]
    [∀ c, Module.Finite ℂ (M c)] (f : ∀ c, M c →ₗ[ℂ] M c) :
    LinearMap.trace ℂ (PiTensorProduct ℂ M) (PiTensorProduct.map f) =
      ∏ c, LinearMap.trace ℂ (M c) (f c) := by
  classical
  let bc := fun c => Module.Free.chooseBasis ℂ (M c)
  let B := Basis.piTensorProduct bc
  rw [LinearMap.trace_eq_matrix_trace ℂ B]
  have hc : ∀ c, LinearMap.trace ℂ (M c) (f c) = ∑ j, (bc c).repr (f c (bc c j)) j := by
    intro c
    rw [LinearMap.trace_eq_matrix_trace ℂ (bc c), Matrix.trace]
    simp only [Matrix.diag, LinearMap.toMatrix_apply]
  simp only [hc]
  rw [Fintype.prod_sum, Matrix.trace]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.diag, LinearMap.toMatrix_apply, Basis.piTensorProduct_apply, PiTensorProduct.map_tprod,
    Basis.piTensorProduct_repr_tprod_apply]

theorem finrank_wsp {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (lam : InfinitePlace E → DomWeight n) :
    (Module.finrank ℂ (Wsp lam) : ℂ) = dimW lam := by
  rw [← LinearMap.trace_id, ← PiTensorProduct.map_id, trace_piMap]
  unfold dimW
  simp

end GlobalTheory.BCT.TrKer
