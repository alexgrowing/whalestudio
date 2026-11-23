import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.QuadraticSplitting.QuadSplit

open Polynomial Matrix

namespace UpperTheory.V.Sd.S2.symmetric_square_mixed_charpoly

variable {k : Type} [Field k]

private def blk (A B : Matrix (Fin 2) (Fin 2) k) : Matrix (Fin 4) (Fin 4) k :=
  !![A 0 0, A 0 1, 0, 0; A 1 0, A 1 1, 0, 0; 0, 0, B 0 0, B 0 1; 0, 0, B 1 0, B 1 1]

private def ant (A B : Matrix (Fin 2) (Fin 2) k) : Matrix (Fin 4) (Fin 4) k :=
  !![0, 0, A 0 0, A 0 1; 0, 0, A 1 0, A 1 1; B 0 0, B 0 1, 0, 0; B 1 0, B 1 1, 0, 0]

private def Pm (α β : k) : Matrix (Fin 4) (Fin 4) k :=
  !![0, α, 0, α; β, 0, -β, 0; 0, -1, 0, 1; 1, 0, 1, 0]

private def Qm (α β : k) : Matrix (Fin 4) (Fin 4) k :=
  (2 : k)⁻¹ • !![0, β⁻¹, 0, 1; α⁻¹, 0, -1, 0; 0, -β⁻¹, 0, 1; α⁻¹, 0, 1, 0]

private lemma PQ (h2 : (2 : k) ≠ 0) {α β : k} (ha : α ≠ 0) (hb : β ≠ 0) : Pm α β * Qm α β = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Pm, Qm, Matrix.mul_apply, Fin.sum_univ_four] <;> field_simp <;> ring

private lemma cp_conj (h2 : (2 : k) ≠ 0) {α β : k} (ha : α ≠ 0) (hb : β ≠ 0) (M N : Matrix (Fin 4) (Fin 4) k)
    (h : Pm α β * M = N * Pm α β) : M.charpoly = N.charpoly := by
  have h1 := PQ h2 ha hb
  have h3 : Qm α β * Pm α β = 1 := mul_eq_one_comm.mp h1
  have : M = Qm α β * (N * Pm α β) := by rw [← h, ← Matrix.mul_assoc, h3, Matrix.one_mul]
  rw [this, Matrix.charpoly_mul_comm, Matrix.mul_assoc, h1, Matrix.mul_one]

private lemma P_mix (h2 : (2 : k) ≠ 0) (α β : kˣ) (A B : Matrix (Fin 2) (Fin 2) k) :
    Pm (α : k) β * mix (β / α) A B = blk A B * Pm (α : k) β := by
  have ha := α.ne_zero
  have hb := β.ne_zero
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Pm, mix, blk, Matrix.mul_apply, Fin.sum_univ_four] <;> field_simp <;> ring

private lemma blk_P (α β : k) (A B : Matrix (Fin 2) (Fin 2) k) :
    blk A B * Pm α β * Matrix.diagonal ![β, -α, -β, α] =
      ant (A * Matrix.diagonal ![α ^ 2, β ^ 2]) B * Pm α β := by
  ext i j
  rw [Matrix.mul_diagonal]
  fin_cases i <;> fin_cases j <;> simp [Pm, ant, blk, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

private lemma cp_blk (A B : Matrix (Fin 2) (Fin 2) k) : (blk A B).charpoly = A.charpoly * B.charpoly := by
  simp [Matrix.charpoly, Matrix.det_succ_row_zero, Fin.sum_univ_succ, blk, Matrix.charmatrix_apply, Fin.succAbove,
    Matrix.diagonal_apply]
  ring

private lemma cp_ant (A B : Matrix (Fin 2) (Fin 2) k) : (ant A B).charpoly = (A * B).charpoly.comp (X ^ 2) := by
  simp [Matrix.charpoly, Matrix.det_succ_row_zero, Fin.sum_univ_succ, ant, Matrix.charmatrix_apply, Fin.succAbove,
    Matrix.diagonal_apply, Matrix.mul_apply]
  ring

end UpperTheory.V.Sd.S2.symmetric_square_mixed_charpoly

open UpperTheory.V.Sd.S2 UpperTheory.V.Sd.S2.symmetric_square_mixed_charpoly in
theorem UpperTheory.symmetric_square_mixed_charpoly :
    UpperTheory.V.Sd.S2.MixCp := by
  intro k Γ₀ Γ _ _ _ j t α β ρ R H s hs
  have hN : j.range.Normal := Subgroup.normal_of_index_eq_two H.index
  have hc : ∀ h : Γ₀, ∃ h', j h' = t⁻¹ * j h * t := fun h => by
    have := hN.conj_mem' (j h) ⟨h, rfl⟩ t
    exact this
  have hm : ∀ a b : Γ, a ∉ j.range → b ∉ j.range → a * b ∈ j.range := fun a b ha hb =>
    (Subgroup.mul_mem_iff_of_index_two H.index).mpr (by simp [ha, hb])
  have ht' : t⁻¹ ∉ j.range := fun h => H.nmem (inv_mem_iff.mp h)
  refine ⟨fun g g' hg => ?_, fun g hg => ?_⟩
  · obtain ⟨h, hh⟩ := hm _ _ ht' hs
    obtain ⟨g'', hg''⟩ := hc g
    have e : g' = h⁻¹ * g'' * h := H.inj (by
      rw [map_mul, map_mul, map_inv, hh, hg'', hg]; group)
    rw [H.on g g'' hg'', cp_conj H.two α.ne_zero β.ne_zero _ _ (P_mix H.two α β _ _), cp_blk, e]
    congr 1
    rw [map_mul, Units.val_mul, Matrix.charpoly_mul_comm, ← Units.val_mul, ← map_mul, mul_inv_cancel_left]
  · obtain ⟨h, hh⟩ := hm _ _ hs ht'
    obtain ⟨h', hh'⟩ := hc h
    obtain ⟨u, hu⟩ := hm _ _ H.nmem H.nmem
    have e : g = h * u * h' := H.inj (by
      rw [map_mul, map_mul, hh', hu, hh, hg]; group)
    have es : s = j h * t := by rw [hh]; group
    have key : Pm (α : k) β * (R s : Matrix (Fin 4) (Fin 4) k) =
        ant ((ρ h : Matrix (Fin 2) (Fin 2) k) * Matrix.diagonal ![(α : k) ^ 2, (β : k) ^ 2]) (ρ h') * Pm (α : k) β := by
      rw [es, map_mul, Units.val_mul, H.on h h' hh', H.off, ← Matrix.mul_assoc, P_mix H.two, blk_P]
    rw [cp_conj H.two α.ne_zero β.ne_zero _ _ key, cp_ant, e, map_mul, map_mul, Units.val_mul, Units.val_mul, H.sq u hu]
