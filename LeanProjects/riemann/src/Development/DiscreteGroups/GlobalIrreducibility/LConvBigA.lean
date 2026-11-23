import Development.DiscreteGroups.GlobalIrreducibility.LConvCut
import GroundTheory.LocalFields.Uniqueness

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.LocLanglands GlobalTheory.Whittaker Filter Topology

namespace DiscreteGroups.sglob.LConv

section Matrices

variable {k : Type} [Field k] {m : ℕ}

def tv {n : ℕ} (i j : Fin n) (h : i ≠ j) (c : k) : GL (Fin n) k :=
  ⟨Matrix.transvection i j c, Matrix.transvection i j (-c),
    by rw [Matrix.transvection_mul_transvection_same _ _ h, add_neg_cancel, Matrix.transvection_zero],
    by rw [Matrix.transvection_mul_transvection_same _ _ h, neg_add_cancel, Matrix.transvection_zero]⟩

theorem val_tv {n : ℕ} (i j : Fin n) (h : i ≠ j) (c : k) :
    ((tv i j h c : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = Matrix.transvection i j c := rfl

theorem val_tv_inv {n : ℕ} (i j : Fin n) (h : i ≠ j) (c : k) :
    (((tv i j h c)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = Matrix.transvection i j (-c) := rfl

theorem tv_zero {n : ℕ} (i j : Fin n) (h : i ≠ j) : tv i j h (0 : k) = 1 :=
  Units.ext (by rw [val_tv, Matrix.transvection_zero, Units.val_one])

theorem continuous_tv [TopologicalSpace k] [IsTopologicalAddGroup k] {n : ℕ} (i j : Fin n) (h : i ≠ j) :
    Continuous fun c : k => tv i j h c := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · show Continuous fun c : k => Matrix.transvection i j c
    refine continuous_pi fun a => continuous_pi fun b => ?_
    simp only [Matrix.transvection, Matrix.add_apply, Matrix.single_apply]
    split_ifs <;> fun_prop
  · show Continuous fun c : k => Matrix.transvection i j (-c)
    refine continuous_pi fun a => continuous_pi fun b => ?_
    simp only [Matrix.transvection, Matrix.add_apply, Matrix.single_apply]
    split_ifs <;> fun_prop

theorem stdSum_symm_castSucc (i : Fin m) : (stdSum (rfl : m + 1 = m + 1)).symm i.castSucc = Sum.inl i := by
  rw [Equiv.symm_apply_eq]
  exact Fin.ext (by simp)

theorem stdSum_symm_last : (stdSum (rfl : m + 1 = m + 1)).symm (Fin.last m) = Sum.inr 0 := by
  rw [Equiv.symm_apply_eq]
  exact Fin.ext (by simp)

theorem corner_cs_cs (g : GL (Fin m) k) (i j : Fin m) :
    (corner g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) i.castSucc j.castSucc = (g : Matrix (Fin m) (Fin m) k) i j := by
  simp [corner, val_emb₂, Matrix.reindex_apply, stdSum_symm_castSucc]

theorem corner_cs_last (g : GL (Fin m) k) (i : Fin m) :
    (corner g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) i.castSucc (Fin.last m) = 0 := by
  simp [corner, val_emb₂, Matrix.reindex_apply, stdSum_symm_castSucc, stdSum_symm_last]

theorem corner_last (g : GL (Fin m) k) (j : Fin (m + 1)) :
    (corner g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) j =
      (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) j := by
  refine Fin.lastCases ?_ (fun j => ?_) j
  · simp [corner, val_emb₂, Matrix.reindex_apply, stdSum_symm_last]
  · simp [corner, val_emb₂, Matrix.reindex_apply, stdSum_symm_castSucc, stdSum_symm_last,
      (Fin.castSucc_lt_last j).ne']

theorem corner_one : corner (1 : GL (Fin m) k) = 1 :=
  map_one (emb₂ k (stdSum (rfl : m + 1 = m + 1)))

theorem longElt_inv (n : ℕ) : (longElt n k)⁻¹ = longElt n k := Units.ext rfl

theorem longElt_last (j : Fin (m + 1)) :
    (longElt (m + 1) k : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) j = if j = 0 then 1 else 0 := by
  simp [longElt]

end Matrices

section Small

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_small {U : Set k} (hU : U ∈ 𝓝 (0 : k)) (a : k) : ∃ t : k, t ≠ 0 ∧ t ∈ U ∧ a * t ∈ U := by
  let := GroundTheory.LocalField.nontriviallyNormedField k
  have hU' : U ∩ (fun t => a * t) ⁻¹' U ∈ 𝓝 (0 : k) :=
    inter_mem hU ((continuous_const.mul continuous_id).continuousAt.preimage_mem_nhds (by simpa using hU))
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hU'
  obtain ⟨t, ht0, htε⟩ := NormedField.exists_norm_lt k hε
  have ht : t ∈ U ∩ (fun t => a * t) ⁻¹' U := hball (by simpa using htε)
  exact ⟨t, norm_pos_iff.1 ht0, ht.1, ht.2⟩

end Small

end DiscreteGroups.sglob.LConv

end
