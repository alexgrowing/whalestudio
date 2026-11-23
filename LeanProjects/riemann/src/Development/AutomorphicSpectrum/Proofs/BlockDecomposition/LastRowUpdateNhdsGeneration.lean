import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsBump
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCIndValue

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG GlobalTheory.CompanionTheory.BZPhiPG.OntoO Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep

variable {k : Type} [Field k] {n : ℕ}

def lastRowMat (r : Fin (n + 1) → k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k :=
  (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k).updateRow (Fin.last n) r

def rowInv (r : Fin (n + 1) → k) : Fin (n + 1) → k :=
  fun j => if j = Fin.last n then (r (Fin.last n))⁻¹ else -r j * (r (Fin.last n))⁻¹

theorem lastRowMat_mul_last (r s : Fin (n + 1) → k) (j : Fin (n + 1)) :
    (lastRowMat r * lastRowMat s) (Fin.last n) j =
      (if j = Fin.last n then 0 else r j) + r (Fin.last n) * s j := by
  rw [Matrix.mul_apply, Fin.sum_univ_castSucc]
  simp only [GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.lastRowMat, Matrix.updateRow_self,
    Matrix.updateRow_ne (Fin.castSucc_ne_last _), Matrix.one_apply]
  congr 1
  first
  | refine Fin.lastCases ?_ (fun j => ?_) j
    · simp [Fin.castSucc_ne_last]
    · simp [Fin.castSucc_ne_last]
  | induction j using Fin.lastCases with
    | last => simp [Fin.castSucc_ne_last]
    | cast j => simp [Fin.castSucc_ne_last]

theorem lastRowMat_mul_rowInv {r : Fin (n + 1) → k} (hr : r (Fin.last n) ≠ 0) :
    lastRowMat r * lastRowMat (rowInv r) = 1 := by
  ext i j
  by_cases hi : i = Fin.last n
  · subst hi
    rw [GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.lastRowMat_mul_last]
    by_cases hj : j = Fin.last n
    · subst hj
      first
      | simp [GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.rowInv, hr]
      | (simp only [GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.rowInv, if_true, ite_true, zero_add, Matrix.one_apply_eq]
         exact mul_inv_cancel₀ hr)
    · rw [Matrix.one_apply_ne (Ne.symm hj), if_neg hj]
      simp only [GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.rowInv, if_neg hj]
      linear_combination (-r j) * mul_inv_cancel₀ hr
  · first
    | (rw [Matrix.mul_apply]
       simp only [GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.lastRowMat, Matrix.updateRow_ne hi]
       rw [← Matrix.mul_apply, Matrix.one_mul, Matrix.updateRow_ne hi])
    | simp [Matrix.mul_apply, GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.lastRowMat, Matrix.updateRow_ne hi, Matrix.one_apply,
        Matrix.updateRow_apply, hi]

def lastRowGL (r : Fin (n + 1) → k) (hr : r (Fin.last n) ≠ 0) : GL (Fin (n + 1)) k where
  val := lastRowMat r
  inv := lastRowMat (rowInv r)
  val_inv := lastRowMat_mul_rowInv hr
  inv_val := mul_eq_one_comm.1 (lastRowMat_mul_rowInv hr)

def invRow (x : GL (Fin (n + 1)) k) : Fin (n + 1) → k :=
  fun j => ((x⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) j

theorem invRow_one : invRow (1 : GL (Fin (n + 1)) k) (Fin.last n) = 1 := by
  simp [GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.invRow]

theorem vecMul_eLast (x : GL (Fin (n + 1)) k) :
    vecMul (eLast k n) (lastRowMat (invRow x) * (x : Matrix (Fin (n + 1)) (Fin (n + 1)) k)) = eLast k n := by
  have h : vecMul (GlobalTheory.BZMir.eLast k n) (GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.lastRowMat (GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.invRow x)) =
      vecMul (GlobalTheory.BZMir.eLast k n)
        ((x⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) := by
    ext j
    first
    | simp [GlobalTheory.BZMir.eLast, Matrix.single_vecMul, GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.lastRowMat, GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.invRow]
    | simp [GlobalTheory.BZMir.eLast, Matrix.vecMul, dotProduct, Pi.single_apply,
        GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.lastRowMat, GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.invRow, Matrix.updateRow_apply]
  rw [← Matrix.vecMul_vecMul, h, Matrix.vecMul_vecMul, Units.inv_mul, Matrix.vecMul_one]

section Top

variable [TopologicalSpace k] [IsTopologicalDivisionRing k] [T1Space k]

theorem continuous_invRow : Continuous (invRow : GL (Fin (n + 1)) k → _) := by
  have hc : Continuous fun x : GL (Fin (n + 1)) k =>
      ((x⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) :=
    Units.continuous_coe_inv (M := Matrix (Fin (n + 1)) (Fin (n + 1)) k)
  unfold GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.invRow
  first
  | exact continuous_pi fun j => hc.matrix_elem (Fin.last n) j
  | exact continuous_pi fun j => (continuous_apply j).comp ((continuous_apply (Fin.last n)).comp hc)

theorem continuous_lastRowMat : Continuous (lastRowMat : (Fin (n + 1) → k) → _) := by
  unfold GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.lastRowMat
  exact continuous_const.matrix_updateRow (Fin.last n) continuous_id

theorem continuousAt_rowInv : ContinuousAt (fun x : GL (Fin (n + 1)) k => rowInv (invRow x)) 1 := by
  have hv : Continuous (GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.invRow : GL (Fin (n + 1)) k → _) := GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.continuous_invRow
  have hl : ContinuousAt (fun x : GL (Fin (n + 1)) k => (GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.invRow x (Fin.last n))⁻¹) 1 :=
    ((continuous_apply (Fin.last n)).comp hv).continuousAt.inv₀
      (show GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.invRow (1 : GL (Fin (n + 1)) k) (Fin.last n) ≠ 0 by
        rw [GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.invRow_one]; exact one_ne_zero)
  refine continuousAt_pi.2 fun j => ?_
  by_cases hj : j = Fin.last n
  · simp only [GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.rowInv, if_pos hj]
    exact hl
  · simp only [GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.rowInv, if_neg hj]
    exact (((continuous_apply j).comp hv).continuousAt.neg).mul hl

theorem exists_nhd {V : Set (GL (Fin (n + 1)) k)} (hV : V ∈ 𝓝 (1 : GL (Fin (n + 1)) k)) :
    ∃ N ∈ 𝓝 (1 : GL (Fin (n + 1)) k), ∀ x ∈ N, ∃ hr : invRow x (Fin.last n) ≠ 0,
      lastRowGL (invRow x) hr * x ∈ V := by
  have h1 : GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.invRow (1 : GL (Fin (n + 1)) k) (Fin.last n) ≠ 0 := by
    rw [GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.invRow_one]; exact one_ne_zero
  have hv1 : GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.invRow (1 : GL (Fin (n + 1)) k) =
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) := by
    funext j; simp [GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.invRow]
  have hg1 : GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.lastRowGL (GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.invRow (1 : GL (Fin (n + 1)) k)) h1 = 1 := by
    apply Units.ext
    show GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.lastRowMat (GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.invRow (1 : GL (Fin (n + 1)) k)) = 1
    rw [hv1]
    exact Matrix.updateRow_eq_self _ _
  let ψ : GL (Fin (n + 1)) k →
      Matrix (Fin (n + 1)) (Fin (n + 1)) k × (Matrix (Fin (n + 1)) (Fin (n + 1)) k)ᵐᵒᵖ :=
    fun x => (GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.lastRowMat (GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.invRow x) * (x : Matrix (Fin (n + 1)) (Fin (n + 1)) k),
      MulOpposite.op (((x⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *
        GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.lastRowMat (GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.rowInv (GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.invRow x))))
  have hψ : ∀ x (hr : GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.invRow x (Fin.last n) ≠ 0),
      Units.embedProduct (Matrix (Fin (n + 1)) (Fin (n + 1)) k)
        (GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.lastRowGL (GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.invRow x) hr * x) = ψ x := fun x hr => by
    first
    | rfl
    | (rw [Units.embedProduct_apply]; rfl)
  have hfst : ContinuousAt (fun x : GL (Fin (n + 1)) k =>
      GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.lastRowMat (GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.invRow x) * (x : Matrix (Fin (n + 1)) (Fin (n + 1)) k)) 1 := by
    first
    | exact ((GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.continuous_lastRowMat.comp GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.continuous_invRow).mul
        Units.continuous_val).continuousAt
    | exact ((GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.continuous_lastRowMat.comp GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.continuous_invRow).matrix_mul
        Units.continuous_val).continuousAt
  have hsnd : ContinuousAt (fun x : GL (Fin (n + 1)) k =>
      MulOpposite.op (((x⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *
        GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.lastRowMat (GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.rowInv (GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.invRow x)))) 1 :=
    MulOpposite.continuous_op.continuousAt.comp
      ((Units.continuous_coe_inv (M := Matrix (Fin (n + 1)) (Fin (n + 1)) k)).continuousAt.mul
        (GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.continuous_lastRowMat.continuousAt.comp
          GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.continuousAt_rowInv))
  have hψc : ContinuousAt ψ 1 := hfst.prodMk hsnd
  have hψ1 : ψ 1 = Units.embedProduct (Matrix (Fin (n + 1)) (Fin (n + 1)) k) 1 := by
    rw [← hψ 1 h1, hg1, mul_one]
  obtain ⟨U, hU, hUV⟩ : ∃ U ∈ 𝓝 (Units.embedProduct (Matrix (Fin (n + 1)) (Fin (n + 1)) k) 1),
      Units.embedProduct (Matrix (Fin (n + 1)) (Fin (n + 1)) k) ⁻¹' U ⊆ V := by
    rw [Units.isEmbedding_embedProduct.toIsInducing.nhds_eq_comap] at hV
    exact Filter.mem_comap.1 hV
  have hne : ∀ᶠ x in 𝓝 (1 : GL (Fin (n + 1)) k), GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.invRow x (Fin.last n) ≠ 0 :=
    ((continuous_apply (Fin.last n)).comp GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.continuous_invRow).continuousAt.eventually_ne h1
  refine ⟨ψ ⁻¹' U ∩ {x | GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.invRow x (Fin.last n) ≠ 0},
    Filter.inter_mem (hψc.preimage_mem_nhds (by rw [hψ1]; exact hU)) hne, ?_⟩
  rintro x ⟨hxU, hx⟩
  refine ⟨hx, hUV ?_⟩
  show Units.embedProduct (Matrix (Fin (n + 1)) (Fin (n + 1)) k)
    (GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.lastRowGL (GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.invRow x) hx * x) ∈ U
  rw [hψ x hx]
  exact hxU

end Top

theorem row_replacement (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ)
    (S : Subgroup (GL (Fin (n + 1)) k))
    (hS : ∀ (r : Fin (n + 1) → k), r (Fin.last n) ≠ 0 → ∀ g : GL (Fin (n + 1)) k,
      (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) = (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k).updateRow (Fin.last n) r → g ∈ S)
    (O : Set (Mir k n)) (hO : O ∈ 𝓝 (1 : Mir k n)) :
    ∃ N ∈ 𝓝 (1 : GL (Fin (n + 1)) k), ∀ p ∈ S, ∀ x ∈ N, ∀ m : Mir k n, (m : GL (Fin (n + 1)) k) = p * x →
      ∃ a : Mir k n, (a : GL (Fin (n + 1)) k) ∈ S ∧ ∃ x' ∈ O, m = a * x' := by
  obtain ⟨V, hV, hVO⟩ := (mem_nhds_subtype _ _ _).1 hO
  obtain ⟨N, hN, hNV⟩ := GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.exists_nhd (k := k) (n := n) hV
  refine ⟨N, hN, fun p hp x hx m hm => ?_⟩
  obtain ⟨hr, hgx⟩ := hNV x hx
  have hgS : GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.lastRowGL (GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.invRow x) hr ∈ S := hS _ hr _ rfl
  have hmir : GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.lastRowGL (GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.invRow x) hr * x ∈ GlobalTheory.BZMir.Mir k n :=
    GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.vecMul_eLast x
  refine ⟨m * ⟨GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.lastRowGL (GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.invRow x) hr * x, hmir⟩⁻¹, ?_,
    ⟨GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.lastRowGL (GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.invRow x) hr * x, hmir⟩, hVO hgx, (inv_mul_cancel_right _ _).symm⟩
  show (m : GL (Fin (n + 1)) k) * (GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.lastRowGL (GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.invRow x) hr * x)⁻¹ ∈ S
  rw [hm, _root_.mul_inv_rev, ← mul_assoc, mul_inv_cancel_right]
  exact S.mul_mem hp (S.inv_mem hgS)

end GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep

end
