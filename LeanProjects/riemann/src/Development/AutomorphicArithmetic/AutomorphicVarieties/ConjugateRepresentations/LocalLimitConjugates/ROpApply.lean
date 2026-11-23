import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasimirResolventProjection
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.ArchimedeanCompact.OneTmulMemCenter
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.DualIff
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

private theorem mapQ {A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] (f : A →ₐ[ℂ] B) {n : ℕ}
    (X : Fin n → Fin n → A) (u : ℂ) : f (Formalism.REAL.qdet X u) = Formalism.REAL.qdet (fun i j => f (X i j)) u := by
  simp only [Formalism.REAL.qdet, Formalism.REAL.qminor, Formalism.REAL.Tm, map_sum, map_mul, map_intCast, map_list_prod, List.map_ofFn,
    Function.comp_def, map_add, apply_ite f, AlgHom.commutes, map_zero]

private noncomputable def rAlg (V : Type) [AddCommGroup V] [Module ℂ V] (d : ℕ) :
    Matrix (Fin d) (Fin d) ℂ →ₐ[ℂ] Module.End ℂ (V ⊗[ℂ] (Fin d → ℂ)) :=
  (Module.End.lTensorAlgHom ℂ (Fin d → ℂ) V).comp
    (Matrix.toLinAlgEquiv' : Matrix (Fin d) (Fin d) ℂ ≃ₐ[ℂ] Module.End ℂ (Fin d → ℂ)).toAlgHom

private noncomputable def rOp (V : Type) [AddCommGroup V] [Module ℂ V] (d : ℕ) :
    Matrix (Fin d) (Fin d) ℂ →ₐ[ℂ] (Module.End ℂ (V ⊗[ℂ] (Fin d → ℂ)))ᵐᵒᵖ where
  toFun N := MulOpposite.op (rAlg V d Nᵀ)
  map_one' := by simp
  map_mul' x y := by simp [Matrix.transpose_mul]
  map_zero' := by simp
  map_add' x y := by simp [Matrix.transpose_add]
  commutes' c := by simp [Algebra.algebraMap_eq_smul_one]

private theorem rOp_apply (V : Type) [AddCommGroup V] [Module ℂ V] (d : ℕ) (N : Matrix (Fin d) (Fin d) ℂ) :
    rOp V d N = MulOpposite.op (rAlg V d Nᵀ) := rfl

private theorem qdet_stab {M : Type} [AddCommGroup M] [Module ℂ M] (N : Submodule ℂ M) {n : ℕ}
    (X : Fin n → Fin n → Module.End ℂ M) (h : ∀ i j, ∀ m ∈ N, X i j m ∈ N) (u : ℂ) :
    ∀ m ∈ N, Formalism.REAL.qdet X u m ∈ N := by
  let S : Subalgebra ℂ (Module.End ℂ M) :=
    { carrier := {z | ∀ m ∈ N, z m ∈ N}
      mul_mem' := fun hx hy m hm => hx _ (hy m hm)
      add_mem' := fun hx hy m hm => N.add_mem (hx m hm) (hy m hm)
      algebraMap_mem' := fun c m hm => N.smul_mem c hm }
  let Z : Fin n → Fin n → S := fun i j => ⟨X i j, h i j⟩
  have e : ((Formalism.REAL.qdet Z u : S) : Module.End ℂ M) = Formalism.REAL.qdet X u := mapQ S.val Z u
  rw [← e]
  exact (Formalism.REAL.qdet Z u).2

theorem UpperTheory.V.Cj.H.capSm :
    UpperTheory.V.Cj.H.CapSm := by
  intro E _ _ _ a Ξ τ u
  have hE : ∀ i j : Fin a, Eop (a := a) τ i j = eL (N := Module.End ℂ (Sm E a)) (lie E a) τ i j := fun _ _ => rfl
  have hc : cap (a := a) τ u = Formalism.REAL.qdet (Eop (a := a) τ) (u + ((a : ℂ) - 1) / 2) := rfl
  refine ⟨?_, fun m hm => ?_, fun X => ?_, fun N hN => ?_⟩
  · let f : Module.End ℂ (Sm E a) →ₐ[ℂ] Module.End ℂ (Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ)) :=
      Module.End.rTensorAlgHom ℂ (Sm E a) (Fin Ξ.d → ℂ)
    have hf : ∀ X, smA Ξ X = f (lie E a X) := fun _ => rfl
    have e : eL (smA Ξ) τ = fun i j => f (Eop (a := a) τ i j) := by
      funext i j
      simp only [hE, eL, hf, map_smul, map_sub]
    rw [e, ← mapQ, ← hc]
    rfl
  · have hd := (dualIff E a Ξ τ m).1 hm
    have hB : ∀ X, smB Ξ X = rAlg (Sm E a) Ξ.d (Ξ.dmat X) := fun X => smB_apply Ξ X
    have h := (mapQ (rOp (Sm E a) Ξ.d) (GlobalTheory.WignerGL.dualE Ξ τ) (u + ((a : ℂ) - 1) / 2)).symm.trans
      (congrArg (rOp (Sm E a) Ξ.d) (hd.2 u))
    rw [map_smul, map_one] at h
    have e : ∀ i j, rOp (Sm E a) Ξ.d (GlobalTheory.WignerGL.dualE Ξ τ i j) = -MulOpposite.op (eL (smB Ξ) τ i j) := fun i j => by
      rw [dualE_eq, map_neg, rOp_apply, Matrix.transpose_transpose]
      simp only [eL, hB, map_smul, map_sub]
    simp only [e] at h
    rw [h, MulOpposite.unop_smul, MulOpposite.unop_one]
  · rw [← UpperTheory.V.Cm.uC_capC, ← UpperTheory.V.Cm.uC_ιC]
    exact Commute.map (Subalgebra.mem_center_iff.1 (UpperTheory.V.Cm.capC_mem_center τ u) _) (UpperTheory.V.Cm.uC E a)
  · rw [hc]
    refine qdet_stab N _ (fun i j φ hφ => ?_) _
    rw [hE]
    exact N.smul_mem _ (N.sub_mem (hN _ φ hφ) (N.smul_mem _ (hN _ φ hφ)))
