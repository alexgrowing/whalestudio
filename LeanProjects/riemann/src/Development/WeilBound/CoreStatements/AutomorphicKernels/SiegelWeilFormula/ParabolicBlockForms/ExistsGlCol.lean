import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ParabolicBlockForms.QE

noncomputable section

open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

set_option linter.unusedSimpArgs false

namespace PositivityTheory.SiegelWeilFormula.Act.C4

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

variable {d : SD σ} (L : LD d)

namespace Bq

open Matrix

theorem gl_col_of_ne {K : Type} [Field K] {m : ℕ} (i₀ : Fin m) (w : Fin m → K) (hw : w i₀ ≠ 0) :
    ∃ a : GL (Fin m) K, ∀ k, a.1 k i₀ = w k := by
  set e : Fin m → K := Pi.single i₀ 1 with he
  set A : Matrix (Fin m) (Fin m) K := 1 + replicateCol Unit (w - e) * replicateRow Unit e with hA
  have hdet : A.det = w i₀ := by
    rw [hA, det_one_add_replicateCol_mul_replicateRow]
    simp [he, dotProduct, Pi.single_apply]
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero A (by rw [hdet]; exact hw), fun k => ?_⟩
  simp only [Matrix.GeneralLinearGroup.val_mkOfDetNeZero, hA, Matrix.add_apply, Matrix.mul_apply, replicateCol_apply,
    replicateRow_apply, Finset.univ_unique, Finset.sum_singleton, he, Pi.sub_apply, Pi.single_eq_same, mul_one,
    Matrix.one_apply, Pi.single_apply]
  split_ifs <;> ring

theorem exists_gl_col {K : Type} [Field K] {m : ℕ} (i₀ : Fin m) (v : Fin m → K) (hv : v ≠ 0) :
    ∃ a : GL (Fin m) K, ∀ k, a.1 k i₀ = v k := by
  by_cases h0 : v i₀ ≠ 0
  · exact gl_col_of_ne i₀ v h0
  push_neg at h0
  obtain ⟨k, hk⟩ := Function.ne_iff.1 hv
  have hki : k ≠ i₀ := fun h => hk (by rw [h, h0]; rfl)
  set w : Fin m → K := v + Pi.single i₀ (v k) with hw
  have hwi : w i₀ = v k := by simp [hw, h0]
  have hwk : w k = v k := by simp [hw, Pi.single_apply, hki]
  obtain ⟨a, ha⟩ := gl_col_of_ne i₀ w (by rw [hwi]; exact hk)
  set T : Matrix (Fin m) (Fin m) K := 1 + replicateCol Unit (-(Pi.single i₀ (1 : K))) * replicateRow Unit (Pi.single k (1 : K))
    with hT
  have hTd : T.det = 1 := by
    rw [hT, det_one_add_replicateCol_mul_replicateRow]
    simp [dotProduct, Pi.single_apply, hki, Ne.symm hki]
  have hdet : (T * a.1).det ≠ 0 := by
    rw [Matrix.det_mul, hTd, one_mul]
    exact (Matrix.GeneralLinearGroup.det a).ne_zero
  have hTe : ∀ k' m', T k' m' = (1 : Matrix (Fin m) (Fin m) K) k' m' - (Pi.single i₀ (1 : K) : Fin m → K) k' * (Pi.single k (1 : K) : Fin m → K) m' := by
    intro k' m'
    simp [hT, Matrix.add_apply, Matrix.mul_apply, replicateCol_apply, replicateRow_apply, sub_eq_add_neg]
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (T * a.1) hdet, fun k' => ?_⟩
  rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero, Matrix.mul_apply]
  simp_rw [hTe, sub_mul, Finset.sum_sub_distrib, ha, mul_assoc, ← Finset.mul_sum]
  have h1 : ∑ x, (1 : Matrix (Fin m) (Fin m) K) k' x * w x = w k' := by
    simp [Matrix.one_apply]
  have h2 : ∑ x, (Pi.single k (1 : K) : Fin m → K) x * w x = w k := by
    simp [Pi.single_apply]
  rw [h1, h2, hwk, hw, Pi.add_apply]
  by_cases hk' : k' = i₀
  · subst hk'; simp
  · simp [Pi.single_apply, hk']

theorem padE_emS (N : Matrix (Fin L.n ⊕ Fin L.n) (Fin L.n ⊕ Fin L.n) E) (a a' : Fin L.n ⊕ Fin L.n) :
    padE L N (emS L a) (emS L a') = N a a' := by
  have h : (∃ x, emS L x = emS L a) ∧ ∃ x, emS L x = emS L a' := ⟨⟨a, rfl⟩, ⟨a', rfl⟩⟩
  simp only [padE]
  rw [dif_pos h, emS_inj L h.1.choose_spec, emS_inj L h.2.choose_spec]

theorem padE_out_row (N : Matrix (Fin L.n ⊕ Fin L.n) (Fin L.n ⊕ Fin L.n) E) {r : Fin d.n ⊕ Fin d.n}
    (hr : ¬ ∃ a, emS L a = r) (c : Fin d.n ⊕ Fin d.n) : padE L N r c = (1 : Matrix _ _ E) r c := by
  simp only [padE]
  rw [dif_neg (fun h => hr h.1)]

theorem padE_out_col (N : Matrix (Fin L.n ⊕ Fin L.n) (Fin L.n ⊕ Fin L.n) E) (r : Fin d.n ⊕ Fin d.n)
    {c : Fin d.n ⊕ Fin d.n} (hc : ¬ ∃ a, emS L a = c) : padE L N r c = (1 : Matrix _ _ E) r c := by
  simp only [padE]
  rw [dif_neg (fun h => hc h.2)]

theorem nq_E {M : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E}
    (hx : ∀ r, M r (Sum.inl L.i₀) = (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E) r (Sum.inl L.i₀))
    (hy : ∀ c, c ≠ Sum.inr L.i₀ → M (Sum.inr L.i₀) c = 0)
    {H' : Matrix (Fin L.n ⊕ Fin L.n) (Fin L.n ⊕ Fin L.n) E} (hH : M.submatrix (emS L) (emS L) * H' = 1) :
    NQ (Sum.inl L.i₀) (Sum.inr L.i₀) (M * padE L H') := by
  have hxo : ¬ ∃ a, emS L a = Sum.inl L.i₀ := not_inl L L.i₀ rfl
  have hyo : ¬ ∃ a, emS L a = Sum.inr L.i₀ := not_inr L L.i₀ rfl
  refine ⟨fun k => ?_, fun k l hlx hly hkx => ?_⟩
  · have : (M * padE L H') k (Sum.inl L.i₀) = (M * (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E)) k (Sum.inl L.i₀) := by
      simp only [Matrix.mul_apply, padE_out_col L H' _ hxo]
    rw [Matrix.sub_apply, this, Matrix.mul_one, hx k, sub_self]
  · have hl : ∃ c', emS L c' = l := by
      by_contra hc
      rcases mem_out L hc with h | h
      · exact hlx h
      · exact hly h
    obtain ⟨c', rfl⟩ := hl
    have hsum : (M * padE L H') k (emS L c') = ∑ a', M k (emS L a') * H' a' c' := by
      rw [Matrix.mul_apply, sum_emb (emS L) (emS_inj L)]
      · simp only [padE_emS]
      · intro m hm
        rw [padE_out_row L H' (fun h => hm (by obtain ⟨a, ha⟩ := h; exact ⟨a, ha⟩)), Matrix.one_apply_ne, mul_zero]
        rintro rfl
        exact hm ⟨c', rfl⟩
    rw [Matrix.sub_apply, hsum]
    by_cases hk : ∃ a, emS L a = k
    · obtain ⟨a, rfl⟩ := hk
      have := congrFun (congrFun hH a) c'
      rw [Matrix.mul_apply] at this
      simp only [Matrix.submatrix_apply] at this
      rw [this, Matrix.one_apply, Matrix.one_apply]
      simp [(emS_inj L).eq_iff]
    · rcases mem_out L hk with h | h
      · exact (hkx h).elim
      · have h' : k = Sum.inr L.i₀ := h
        subst h'
        rw [Finset.sum_eq_zero fun a' _ => by rw [hy _ (fun he => hyo ⟨a', he⟩), zero_mul], Matrix.one_apply_ne, sub_self]
        intro he
        exact hyo ⟨c', he.symm⟩

end Bq

end PositivityTheory.SiegelWeilFormula.Act.C4

end
