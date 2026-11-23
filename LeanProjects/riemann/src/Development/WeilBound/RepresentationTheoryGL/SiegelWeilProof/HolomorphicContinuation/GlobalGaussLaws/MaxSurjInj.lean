import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.BlockLowerRightMulBlockMatrix

noncomputable section

open Matrix GlobalTheory.StdUnn

namespace PositivityTheory.Rg.Sw.Glob.Gen3H

variable {k : Type} [Field k] {n : ℕ}

theorem max_surj_inj (V : Submodule k (Fin n → k)) (X : Matrix (Fin n) (Fin n) k) (I : Finset (Fin n))
    (hS : ∀ t : Fin n → k, ∃ u ∈ V, ∀ i ∈ I, (u ᵥ* X) i = t i)
    (hmax : ∀ I' : Finset (Fin n), (∀ t : Fin n → k, ∃ u ∈ V, ∀ i ∈ I', (u ᵥ* X) i = t i) → I'.card ≤ I.card)
    (u : Fin n → k) (hu : u ∈ V) (h0 : ∀ i ∈ I, (u ᵥ* X) i = 0) : u ᵥ* X = 0 := by
  classical
  by_contra hne
  obtain ⟨j, hj⟩ : ∃ j, (u ᵥ* X) j ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (funext h)
  have hjI : j ∉ I := fun h => hj (h0 j h)
  have hS' : ∀ t : Fin n → k, ∃ u' ∈ V, ∀ i ∈ insert j I, (u' ᵥ* X) i = t i := by
    intro t
    obtain ⟨u', hu', ht⟩ := hS t
    refine ⟨u' + ((t j - (u' ᵥ* X) j) / (u ᵥ* X) j) • u, V.add_mem hu' (V.smul_mem _ hu), ?_⟩
    intro i hi
    rw [add_vecMul, smul_vecMul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rcases Finset.mem_insert.1 hi with rfl | hi
    · field_simp
      ring
    · rw [ht i hi, h0 i hi, mul_zero, add_zero]
  have := hmax _ hS'
  rw [Finset.card_insert_of_notMem hjI] at this
  omega

end PositivityTheory.Rg.Sw.Glob.Gen3H

namespace PositivityTheory.Rg.Sw.Glob

open Gen2H Gen3H

theorem locRedSplit : LocRedSplit := by
  intro k _ n g
  classical
  set Gs := (g : Matrix (Fin (n + n)) (Fin (n + n)) k).submatrix finSumFinEquiv finSumFinEquiv with hGs
  set C := Gs.toBlocks₂₁ with hC
  set D := Gs.toBlocks₂₂ with hD

  let V1 : Submodule k (Fin n → k) := LinearMap.ker ((Matrix.toLin' Cᵀ))
  have hV1 : ∀ u, u ∈ V1 ↔ u ᵥ* C = 0 := by
    intro u
    simp only [V1, LinearMap.mem_ker, Matrix.toLin'_apply]
    rw [← Matrix.vecMul_transpose, Matrix.transpose_transpose]

  let SC : Finset (Fin n) → Prop := fun I => ∀ t : Fin n → k, ∃ u ∈ (⊤ : Submodule k (Fin n → k)), ∀ i ∈ I, (u ᵥ* C) i = t i
  obtain ⟨I, hI, hmaxI⟩ := Finset.exists_max_image ((Finset.univ : Finset (Finset (Fin n))).filter SC) Finset.card
    ⟨∅, Finset.mem_filter.2 ⟨Finset.mem_univ _, fun t => ⟨0, Submodule.mem_top, by simp⟩⟩⟩
  have hSI : SC I := (Finset.mem_filter.1 hI).2
  have hInjC : ∀ u : Fin n → k, (∀ i ∈ I, (u ᵥ* C) i = 0) → u ᵥ* C = 0 := fun u h0 =>
    max_surj_inj ⊤ C I hSI (fun I' h => hmaxI I' (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)) u Submodule.mem_top h0

  let SD : Finset (Fin n) → Prop := fun J => ∀ t : Fin n → k, ∃ u ∈ V1, ∀ j ∈ J, (u ᵥ* D) j = t j
  obtain ⟨J, hJ, hmaxJ⟩ := Finset.exists_max_image ((Finset.univ : Finset (Finset (Fin n))).filter SD) Finset.card
    ⟨∅, Finset.mem_filter.2 ⟨Finset.mem_univ _, fun t => ⟨0, V1.zero_mem, by simp⟩⟩⟩
  have hSJ : SD J := (Finset.mem_filter.1 hJ).2
  have hInjD : ∀ u : Fin n → k, u ᵥ* C = 0 → (∀ j ∈ J, (u ᵥ* D) j = 0) → u ᵥ* D = 0 := fun u hu h0 =>
    max_surj_inj V1 D J hSJ (fun J' h => hmaxJ J' (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)) u ((hV1 u).2 hu) h0

  have hcard : I.card + J.card ≤ n := by
    let Φ : (Fin n → k) →ₗ[k] ({x // x ∈ I} ⊕ {x // x ∈ J} → k) :=
      { toFun := fun u => Sum.elim (fun i => (u ᵥ* C) i.1) (fun j => (u ᵥ* D) j.1)
        map_add' := fun u v => by funext x; rcases x with x | x <;> simp [add_vecMul]
        map_smul' := fun c u => by funext x; rcases x with x | x <;> simp [smul_vecMul] }
    have hsurj : Function.Surjective Φ := by
      intro t
      obtain ⟨u1, -, hu1⟩ := hSI (fun i => if h : i ∈ I then t (Sum.inl ⟨i, h⟩) else 0)
      obtain ⟨u2, hu2V, hu2⟩ := hSJ (fun j => (if h : j ∈ J then t (Sum.inr ⟨j, h⟩) else 0) - (u1 ᵥ* D) j)
      have hu2C : u2 ᵥ* C = 0 := (hV1 u2).1 hu2V
      refine ⟨u1 + u2, ?_⟩
      funext x
      rcases x with ⟨i, hi⟩ | ⟨j, hj⟩
      · simp only [Φ, LinearMap.coe_mk, AddHom.coe_mk, Sum.elim_inl, add_vecMul, hu2C, add_zero]
        rw [hu1 i hi, dif_pos hi]
      · simp only [Φ, LinearMap.coe_mk, AddHom.coe_mk, Sum.elim_inr, add_vecMul, Pi.add_apply]
        rw [hu2 j hj, dif_pos hj]
        ring
    have := LinearMap.finrank_range_le Φ
    rw [LinearMap.range_eq_top.2 hsurj, finrank_top, Module.finrank_fintype_fun_eq_card,
      Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_coe, Fintype.card_coe, Fintype.card_fin] at this
    exact this

  have hJle : J.card ≤ Iᶜ.card := by rw [Finset.card_compl, Fintype.card_fin]; omega
  obtain ⟨T, hJT, -, hTcard⟩ := Finset.exists_subsuperset_card_eq (Finset.subset_univ J) hJle
    (by rw [Finset.card_univ, Fintype.card_fin, Finset.card_compl, Fintype.card_fin]; omega)
  have hce : Fintype.card {x // x ∈ Iᶜ} = Fintype.card {x // x ∈ T} := by
    rw [Fintype.card_coe, Fintype.card_coe, hTcard]
  let e : {x // x ∈ Iᶜ} ≃ {x // x ∈ T} := Fintype.equivOfCardEq hce
  let π : Equiv.Perm (Fin n) := e.extendSubtype
  have hπ : ∀ i, i ∉ I → π i ∈ T := fun i hi => e.extendSubtype_mem i (Finset.mem_compl.2 hi)
  have hπs : ∀ j ∈ T, ∃ i, i ∉ I ∧ π i = j := by
    intro j hj
    obtain ⟨⟨i, hi⟩, hie⟩ := e.surjective ⟨j, hj⟩
    refine ⟨i, Finset.mem_compl.1 hi, ?_⟩
    rw [show π i = (e ⟨i, hi⟩ : Fin n) from e.extendSubtype_apply_of_mem i hi, hie]

  let P : Matrix (Fin n) (Fin n) k := Equiv.Perm.permMatrix k π⁻¹
  have hPdet : IsUnit P.det := by
    rw [Matrix.det_permutation, isUnit_iff_ne_zero]
    rcases Int.units_eq_one_or (Equiv.Perm.sign π⁻¹) with h | h <;> simp [h]
  have hPent : ∀ l i, P l i = if l = π i then 1 else 0 := by
    intro l i
    simp only [P, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq]
    congr 1
    exact propext ⟨fun h => by rw [← h]; simp, fun h => by rw [h]; simp⟩
  have hvP : ∀ (w : Fin n → k) (i : Fin n), (w ᵥ* P) i = w (π i) := by
    intro w i
    simp [vecMul, dotProduct, hPent]
  refine ⟨1, Matrix.nonsingInvUnit P hPdet, I, ?_⟩
  have hPv : ((Matrix.nonsingInvUnit P hPdet : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = P := rfl
  rw [Matrix.mul_assoc, wIm, block_matrix_mul, block_lower_right_mul_block_matrix, ← hGs, ← hC, ← hD, isUnit_iff_ne_zero, hPv]
  simp only [Units.val_one, Matrix.zero_mul, add_zero, zero_add, Matrix.one_mul]
  rw [← Matrix.mul_assoc D]
  intro hdet
  obtain ⟨u, hu0, hu⟩ := Matrix.exists_vecMul_eq_zero_iff.2 hdet
  have hmix : ∀ j, (j ∈ I → (u ᵥ* C) j = 0) ∧ (j ∉ I → (u ᵥ* (D * P)) j = 0) := by
    intro j
    have := congrFun hu j
    rw [vecMul_mix] at this
    by_cases h : j ∈ I
    · rw [if_pos h] at this
      exact ⟨fun _ => this, fun h' => absurd h h'⟩
    · rw [if_neg h] at this
      exact ⟨fun h' => absurd h' h, fun _ => this⟩
  have hC0 : u ᵥ* C = 0 := hInjC u (fun i hi => (hmix i).1 hi)
  have hD0 : u ᵥ* D = 0 := by
    refine hInjD u hC0 (fun j hj => ?_)
    obtain ⟨i, hi, hij⟩ := hπs j (hJT hj)
    have := (hmix i).2 hi
    rw [← Matrix.vecMul_vecMul, hvP, hij] at this
    exact this
  exact hu0 (lower_inj g u hC0 hD0)

end PositivityTheory.Rg.Sw.Glob
