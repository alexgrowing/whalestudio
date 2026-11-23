import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdMinorsMemInv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockPolynomialActionOneMulAdjoint
open Classical MeasureTheory

noncomputable section

open MvPolynomial Matrix

namespace GlobalTheory.MinorFrame

variable {ι : Type} [Fintype ι]

def colMat {d a : ℕ} (g : ι → Matrix (Fin a) (Fin a) ℂ) : Matrix (Var ι d a) (Var ι d a) ℂ :=
  fun w v => if w.1 = v.1 ∧ w.2.1 = v.2.1 then g v.1 w.2.2 v.2.2 else 0

theorem colSub_eq_lsub {d a : ℕ} (g : ι → Matrix (Fin a) (Fin a) ℂ) :
    (colSub g : Pol ι d a →ₐ[ℂ] Pol ι d a) = GlobalTheory.JointHarm.FMul.lsub (colMat g) := by
  refine algHom_ext fun v => ?_
  rw [GlobalTheory.JointHarm.FMul.lsub_X, colSub, aeval_X]
  obtain ⟨τ, r, c⟩ := v
  simp only [colMat, Fintype.sum_prod_type, ite_and, apply_ite C, map_zero, ite_mul, zero_mul]
  simp

theorem colMat_conjTranspose {d a : ℕ} (g : ι → Matrix (Fin a) (Fin a) ℂ) :
    (colMat (d := d) g)ᴴ = colMat fun τ => (g τ)ᴴ := by
  ext w v
  simp only [colMat, conjTranspose_apply]
  by_cases h : v.1 = w.1 ∧ v.2.1 = w.2.1
  · rw [if_pos h, if_pos ⟨h.1.symm, h.2.symm⟩, h.1]
  · rw [if_neg h, if_neg fun h' => h ⟨h'.1.symm, h'.2.symm⟩, star_zero]

theorem colSub_comp {d a : ℕ} (h g : ι → Matrix (Fin a) (Fin a) ℂ) :
    (colSub h : Pol ι d a →ₐ[ℂ] Pol ι d a).comp (colSub g) = colSub fun τ => h τ * g τ := by
  refine algHom_ext fun v => ?_
  rw [AlgHom.comp_apply]
  unfold colSub
  rw [aeval_X, aeval_X, map_sum]
  simp only [map_mul, aeval_C, aeval_X, algebraMap_eq, Matrix.mul_apply, map_sum, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  ring

theorem colSub_one {d a : ℕ} : (colSub (fun _ => (1 : Matrix (Fin a) (Fin a) ℂ)) : Pol ι d a →ₐ[ℂ] Pol ι d a) =
    AlgHom.id ℂ _ := by
  refine algHom_ext fun v => ?_
  rw [colSub, aeval_X, Finset.sum_eq_single v.2.2]
  · simp
  · intro b _ hb
    rw [Matrix.one_apply_ne hb]
    simp
  · simp

theorem fockS_colSub_unitary : ∀ {ι : Type} [Fintype ι] (a d : ℕ) (u : ι → Matrix.unitaryGroup (Fin a) ℂ)
    (P Q : GlobalTheory.MinorFrame.Pol ι d a),
    Formalism.L2.DIV.fockS (GlobalTheory.MinorFrame.colSub (fun τ => (u τ : Matrix (Fin a) (Fin a) ℂ)) P)
      (GlobalTheory.MinorFrame.colSub (fun τ => (u τ : Matrix (Fin a) (Fin a) ℂ)) Q) = Formalism.L2.DIV.fockS P Q := by
  intro ι _ a d u P Q
  rw [← Formalism.L2.DIV.fockL_apply, ← Formalism.L2.DIV.fockL_apply, colSub_eq_lsub, GlobalTheory.JointHarm.FMul.fockL_lsub_adj,
    ← colSub_eq_lsub, colMat_conjTranspose, ← colSub_eq_lsub, ← AlgHom.comp_apply, colSub_comp]
  have hu : (fun τ => (u τ : Matrix (Fin a) (Fin a) ℂ)ᴴ * (u τ : Matrix (Fin a) (Fin a) ℂ)) = fun _ => 1 := by
    funext τ
    exact Matrix.mem_unitaryGroup_iff'.1 (u τ).2
  rw [hu, colSub_one, AlgHom.id_apply]

end GlobalTheory.MinorFrame
