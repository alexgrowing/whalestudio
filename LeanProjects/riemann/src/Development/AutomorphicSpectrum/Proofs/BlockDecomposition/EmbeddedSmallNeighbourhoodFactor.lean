import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCIndValue
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemHGPIffParabolic
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MvecLeviMulUv
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RowQMulOfMemQ

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.LeibPhi.Emb

open GlobalTheory.CompanionTheory.BZPhiPhi

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem mirProj_iotaM (n : ℕ) (y : Mir k n) :
    mirabolicProjection k (n + 1) (embedding₂ k n y) = (y : GL (Fin (n + 1)) k) :=
  GlobalTheory.CompanionTheory.MirLevi.mirProj_levi _ _

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem iotaM_mem_Q (n : ℕ) (y : Mir k n) : embedding₂ k n y ∈ Q k n := by
  show mirabolicProjection k (n + 1) (embedding₂ k n y) ∈ Mir k n
  rw [mirProj_iotaM]
  exact y.2

theorem mem_mirabolicParabolic_of_iotaM_mem (m j : ℕ) (p : Mir k (m + j))
    (h : embedding₂ k (m + j) p ∈ MirabolicParabolic k m (j + 1)) : p ∈ MirabolicParabolic k m j := by
  have h1 := (GlobalTheory.CompanionTheory.GPMem.mem_mirabolicParabolic_iff_mirabolicProj_mem_parabolic k m (j + 1) (embedding₂ k (m + j) p)).1 h
  have e : mirabolicProjection k (m + (j + 1)) (embedding₂ k (m + j) p) = (p : GL (Fin (m + j + 1)) k) :=
    mirProj_iotaM (m + j) p
  rw [e] at h1
  exact h1

theorem mem_mirabolicParabolic_of_mirabolicProj_eq_one (m j : ℕ) (w : Mir k (m + j)) (h : mirabolicProjection k (m + j) w = 1) :
    w ∈ MirabolicParabolic k m j := by
  rw [GlobalTheory.CompanionTheory.GPMem.mem_mirabolicParabolic_iff_mirabolicProj_mem_parabolic, h]
  exact one_mem _

theorem rowQ_eq_zero_of_mem_HGP (m j : ℕ) (h : Mir k (m + (j + 1))) (hh : h ∈ MirabolicParabolic k m (j + 1))
    (i : Fin (m + j + 1)) (hi : (i : ℕ) < m) : rowQ k (m + j) h i = 0 := by
  have h1 := (mem_mirabolicParabolic_iff k m (j + 1) h).1 hh ⟨j, by omega⟩ ⟨i, hi⟩
  have e1 : eGP m (j + 1) ⟨true, ⟨j, by omega⟩⟩ = Fin.castSucc (Fin.last (m + j)) :=
    Fin.ext (by rw [blockIndex_true_val]; simp)
  have e2 : eGP m (j + 1) ⟨false, ⟨i, hi⟩⟩ = Fin.castSucc i :=
    Fin.ext (by rw [blockIndex_false_val]; simp)
  rw [e1, e2] at h1
  exact h1

theorem rowEl_mem_HGP (m j : ℕ) (r : Fin (m + j + 1) → k) (hr : (rowMat (m + j) r).det ≠ 0)
    (h0 : ∀ i : Fin (m + j + 1), (i : ℕ) < m → r i = 0) :
    (rowEl (m + j) r hr : Mir k (m + (j + 1))) ∈ MirabolicParabolic k m (j + 1) := by
  rw [mem_mirabolicParabolic_iff]
  intro b a
  have hb := blockIndex_true_val m (j + 1) b
  have ha := blockIndex_false_val m (j + 1) a
  have hval : (((rowEl (m + j) r hr : Mir k (m + j + 1)) : GL (Fin (m + j + 2)) k) :
      Matrix (Fin (m + j + 2)) (Fin (m + j + 2)) k) = rowMat (m + j) r := rfl
  generalize eGP m (j + 1) ⟨true, b⟩ = p at hb ⊢
  generalize eGP m (j + 1) ⟨false, a⟩ = q at ha ⊢
  show (((rowEl (m + j) r hr : Mir k (m + j + 1)) : GL (Fin (m + j + 2)) k) :
      Matrix (Fin (m + j + 2)) (Fin (m + j + 2)) k) p q = 0
  rw [hval, rowMat]
  by_cases hp : p = Fin.castSucc (Fin.last (m + j))
  · subst hp
    rw [updateRow_self]
    have ham := a.2
    have hq : q = Fin.castSucc (⟨a, by omega⟩ : Fin (m + j + 1)) := Fin.ext (by simpa using ha)
    rw [hq, Fin.lastCases_castSucc]
    exact h0 _ a.2
  · rw [updateRow_ne hp, one_apply_ne]
    intro c
    have := congrArg Fin.val c
    have ham := a.2
    omega

theorem mul_inv_qProj_mem (m j : ℕ) (x : Mir k (m + j)) (h d κ : Mir k (m + (j + 1)))
    (hh : h ∈ MirabolicParabolic k m (j + 1)) (hd : d ∈ MirabolicParabolic k m (j + 1)) (hq : d * κ ∈ Q k (m + j))
    (e : embedding₂ k (m + j) x = h * κ) :
    x * (qProj k (m + j) ⟨d * κ, hq⟩)⁻¹ ∈ MirabolicParabolic k m j := by
  apply mem_mirabolicParabolic_of_iotaM_mem
  set y := qProj k (m + j) ⟨d * κ, hq⟩ with hy
  have e1 : embedding₂ k (m + j) (x * y⁻¹) = (h * d⁻¹) * ((d * κ) * (embedding₂ k (m + j) y)⁻¹) := by
    rw [map_mul, map_inv, e]
    group
  rw [e1]
  refine mul_mem (mul_mem hh (inv_mem hd)) (mem_mirabolicParabolic_of_mirabolicProj_eq_one m (j + 1) _ ?_)
  have e2 : mirabolicProjection k (m + (j + 1)) (embedding₂ k (m + j) y) = (y : GL (Fin (m + j + 1)) k) :=
    mirProj_iotaM (m + j) y
  have e3 : (y : GL (Fin (m + j + 1)) k) = mirabolicProjection k (m + (j + 1)) (d * κ) := rfl
  rw [map_mul, map_inv, e2, e3, mul_inv_cancel]

theorem iotaM_descent (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (m j : ℕ) :
    ∀ K' ∈ 𝓝 (1 : Mir k (m + j)), ∃ K ∈ 𝓝 (1 : Mir k (m + (j + 1))),
      ∀ x : Mir k (m + j), ∀ h ∈ MirabolicParabolic k m (j + 1), ∀ κ ∈ K, embedding₂ k (m + j) x = h * κ →
        ∃ h' ∈ MirabolicParabolic k m j, ∃ κ' ∈ K', x = h' * κ' := by
  have : T2Space k := by
    let := IsTopologicalAddGroup.rightUniformSpace k
    have := isUniformAddGroup_of_addCommGroup (G := k)
    infer_instance
  intro K' hK'
  let r : Mir k (m + j + 1) → Fin (m + j + 1) → k := fun κ => rowQ k (m + j) κ⁻¹
  have hcr : Continuous r := (continuous_rowQ (m + j)).comp continuous_inv
  let O : Set (Mir k (m + j + 1)) := {κ | (rowMat (m + j) (r κ)).det ≠ 0}
  have hO : IsOpen O :=
    isOpen_compl_singleton.preimage ((continuous_rowMat (m + j)).comp hcr).matrix_det
  have hr1 : r 1 = Pi.single (Fin.last (m + j)) 1 := by
    show rowQ k (m + j) 1⁻¹ = _
    rw [inv_one, rowQ_one]
  have hm1 : rowMat (m + j) (r 1) = 1 := by rw [hr1, rowMat_single]
  have h1O : (1 : Mir k (m + j + 1)) ∈ O := by
    show (rowMat (m + j) (r 1)).det ≠ 0
    rw [hm1, det_one]
    exact one_ne_zero
  let d : O → Mir k (m + j + 1) := fun κ => rowEl (m + j) (r κ.1) κ.2
  have hdc : Continuous d :=
    (continuous_rowEl (k := k) (m + j)).comp
      (Continuous.subtype_mk (hcr.comp continuous_subtype_val) fun κ => κ.2)
  have hQ : ∀ κ : O, d κ * κ.1 ∈ Q k (m + j) := fun κ => by
    have := mul_inv_mem_Q_of_rowQ_eq (m + j) (d κ) (κ.1)⁻¹ (rowQ_rowEl (m + j) (r κ.1) κ.2)
    rwa [inv_inv] at this
  let φ : O → Q k (m + j) := fun κ => ⟨d κ * κ.1, hQ κ⟩
  have hφc : Continuous φ := Continuous.subtype_mk (hdc.mul continuous_subtype_val) _
  let ψ : O → Mir k (m + j) := fun κ => qProj k (m + j) (φ κ)
  have hψc : Continuous ψ := (GlobalTheory.CompanionTheory.BZMirOnto.continuous_qProj k (m + j)).comp hφc
  have hd1 : d ⟨1, h1O⟩ = 1 := Subtype.ext (Units.ext hm1)
  have hψ1 : ψ ⟨1, h1O⟩ = 1 := by
    have : φ ⟨1, h1O⟩ = 1 := Subtype.ext (by
      show d ⟨1, h1O⟩ * 1 = 1
      rw [hd1, one_mul])
    show qProj k (m + j) (φ ⟨1, h1O⟩) = 1
    rw [this, map_one]
  have hpre : ψ ⁻¹' K' ∈ 𝓝 (⟨1, h1O⟩ : O) :=
    hψc.continuousAt.preimage_mem_nhds (by rw [hψ1]; exact hK')
  refine ⟨Subtype.val '' (ψ ⁻¹' K'), hO.isOpenMap_subtype_val.image_mem_nhds hpre, ?_⟩
  rintro x h hh _ ⟨κ, hκ, rfl⟩ e
  have hκinv : (κ.1)⁻¹ = embedding₂ k (m + j) x⁻¹ * h := by
    rw [map_inv, e]
    group
  have hrow : r κ.1 = rowQ k (m + j) h := by
    show rowQ k (m + j) (κ.1)⁻¹ = _
    rw [hκinv]
    exact rowQ_mul_of_mem_Q k (m + j) _ h (iotaM_mem_Q (m + j) x⁻¹)
  have hdH : d κ ∈ MirabolicParabolic k m (j + 1) :=
    rowEl_mem_HGP m j (r κ.1) κ.2 fun i hi => by
      rw [hrow]
      exact rowQ_eq_zero_of_mem_HGP m j h hh i hi
  exact ⟨x * (ψ κ)⁻¹, mul_inv_qProj_mem m j x h (d κ) κ.1 hh hdH (hQ κ) e, ψ κ, hκ, by group⟩

end GlobalTheory.CompanionTheory.LeibPhi.Emb

end
