import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FullToGlIsSelfAdjoint
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralUnitaryGroupTransitiveNormOneVectorsStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.Step

section Blocks
variable {r : ℕ} {E : Type} [Field E]

theorem embHom_castSucc_castSucc (M : Matrix (Fin r) (Fin r) E) (a b : Fin r) :
    embHom r E M (Fin.castSucc a) (Fin.castSucc b) = M a b := by
  have ha : finSumFinEquiv.symm (Fin.castSucc a) = (Sum.inl a : Fin r ⊕ Fin 1) :=
    finSumFinEquiv_symm_apply_castSucc a
  have hb : finSumFinEquiv.symm (Fin.castSucc b) = (Sum.inl b : Fin r ⊕ Fin 1) :=
    finSumFinEquiv_symm_apply_castSucc b
  simp [embHom, Matrix.reindex_apply, Matrix.submatrix_apply, ha, hb]

theorem embHom_castSucc_last (M : Matrix (Fin r) (Fin r) E) (a : Fin r) :
    embHom r E M (Fin.castSucc a) (Fin.last r) = 0 := by
  have ha : finSumFinEquiv.symm (Fin.castSucc a) = (Sum.inl a : Fin r ⊕ Fin 1) :=
    finSumFinEquiv_symm_apply_castSucc a
  have hb : finSumFinEquiv.symm (Fin.last r) = (Sum.inr 0 : Fin r ⊕ Fin 1) := finSumFinEquiv_symm_last
  simp [embHom, Matrix.reindex_apply, Matrix.submatrix_apply, ha, hb]

theorem embHom_last_castSucc (M : Matrix (Fin r) (Fin r) E) (b : Fin r) :
    embHom r E M (Fin.last r) (Fin.castSucc b) = 0 := by
  have ha : finSumFinEquiv.symm (Fin.castSucc b) = (Sum.inl b : Fin r ⊕ Fin 1) :=
    finSumFinEquiv_symm_apply_castSucc b
  have hb : finSumFinEquiv.symm (Fin.last r) = (Sum.inr 0 : Fin r ⊕ Fin 1) := finSumFinEquiv_symm_last
  simp [embHom, Matrix.reindex_apply, Matrix.submatrix_apply, ha, hb]

theorem embHom_last_last (M : Matrix (Fin r) (Fin r) E) :
    embHom r E M (Fin.last r) (Fin.last r) = 1 := by
  have hb : finSumFinEquiv.symm (Fin.last r) = (Sum.inr 0 : Fin r ⊕ Fin 1) := finSumFinEquiv_symm_last
  simp [embHom, Matrix.reindex_apply, Matrix.submatrix_apply, hb]

theorem eq_embHom_of_last (h : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (hc : ∀ i, h i (Fin.last r) = if i = Fin.last r then 1 else 0)
    (hr : ∀ j, h (Fin.last r) j = if j = Fin.last r then 1 else 0) :
    h = embHom r E (h.submatrix Fin.castSucc Fin.castSucc) := by
  ext i j
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => rw [embHom_last_last, hr]; simp
    | cast b => rw [embHom_last_castSucc, hr]; simp [Fin.castSucc_ne_last]
  | cast a =>
    induction j using Fin.lastCases with
    | last => rw [embHom_castSucc_last, hc]; simp [Fin.castSucc_ne_last]
    | cast b => rw [embHom_castSucc_castSucc]; rfl

end Blocks

end GlobalTheory.JR.Step

namespace GlobalTheory.JR.Step

section Main
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
  [StarRing E] [Unram F E]

theorem actU_liftH_support {r : ℕ} (X : Hn r F E) (ν : E) (l : F) (hν : ‖ν‖ = 1)
    (g : Matrix.unitaryGroup (Fin (r + 1)) E)
    (hg : unitU (r + 1) F E (actU g (liftH X ν l)) ≠ 0) :
    ∃ k ∈ uO (r + 1) E, ∃ s, g = k * uEmb r E s := by
  have hmem := Set.mem_of_indicator_ne_zero hg
  have hv : ∀ i, ‖(g.1 *ᵥ (ν • eL r E)) i‖ ≤ 1 := hmem.2.1
  set v : Fin (r + 1) → E := fun i => g.1 i (Fin.last r) with hvdef
  have hgv : g.1 *ᵥ eL r E = v := by
    funext i; simp [eL, Matrix.mulVec_single_one, v]
  have hint : ∀ i, ‖v i‖ ≤ 1 := by
    intro i
    have := hv i
    rw [Matrix.mulVec_smul, hgv, Pi.smul_apply, smul_eq_mul, norm_mul, hν, one_mul] at this
    exact this
  have hunit : star v ⬝ᵥ v = 1 := by
    have h1 : (star g.1 * g.1) (Fin.last r) (Fin.last r) = 1 := by
      rw [Matrix.mem_unitaryGroup_iff'.mp g.2]; simp
    rw [← h1]
    simp [dotProduct, Matrix.mul_apply, v, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply]
  obtain ⟨k, hk, hke⟩ := GlobalTheory.T.integralUnitaryGroup_transitive_norm_one_vectors F E r v hint hunit
  set h := k⁻¹ * g with hh
  have he : h.1 *ᵥ eL r E = eL r E := by
    have hgk : g.1 *ᵥ eL r E = k.1 *ᵥ eL r E := by rw [hgv]; exact hke.symm
    have hk1 : (k⁻¹).1 = star k.1 := rfl
    calc h.1 *ᵥ eL r E = star k.1 *ᵥ (g.1 *ᵥ eL r E) := by
          rw [Matrix.mulVec_mulVec, ← hk1]; rfl
      _ = star k.1 *ᵥ (k.1 *ᵥ eL r E) := by rw [hgk]
      _ = eL r E := by rw [Matrix.mulVec_mulVec, Matrix.mem_unitaryGroup_iff'.mp k.2, Matrix.one_mulVec]
  have hse : star h.1 *ᵥ eL r E = eL r E := by
    conv_lhs => rw [← he]
    rw [Matrix.mulVec_mulVec, Matrix.mem_unitaryGroup_iff'.mp h.2, Matrix.one_mulVec]
  have hc : ∀ i, h.1 i (Fin.last r) = if i = Fin.last r then 1 else 0 := by
    intro i
    have := congrFun he i
    simpa [eL, Matrix.mulVec_single_one, Pi.single_apply] using this
  have hr : ∀ j, h.1 (Fin.last r) j = if j = Fin.last r then 1 else 0 := by
    intro j
    have h0 := congrArg star (congrFun hse j)
    simp only [eL, Matrix.mulVec_single_one, Pi.single_apply, Matrix.star_eq_conjTranspose] at h0
    have h3 : star ((h.1)ᴴ.col (Fin.last r) j) = h.1 (Fin.last r) j := by
      simp [Matrix.col, Matrix.conjTranspose_apply]
    rw [← h3, h0]
    split_ifs <;> simp
  set S := h.1.submatrix Fin.castSucc Fin.castSucc with hSdef
  have hS : h.1 = embHom r E S := eq_embHom_of_last h.1 hc hr
  have hstar : star (embHom r E S) = embHom r E (star S) := by
    simp only [embHom, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.star_eq_conjTranspose, Matrix.reindex_apply,
      Matrix.conjTranspose_submatrix, Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero,
      Matrix.conjTranspose_one]
  have h1 : embHom r E (S * star S) = 1 := by
    rw [map_mul, ← hstar, ← hS]; exact Matrix.mem_unitaryGroup_iff.mp h.2
  have hSu : S ∈ Matrix.unitaryGroup (Fin r) E := by
    rw [Matrix.mem_unitaryGroup_iff]
    ext a b
    have h2 := congrFun (congrFun h1 (Fin.castSucc a)) (Fin.castSucc b)
    rw [embHom_castSucc_castSucc] at h2
    rw [h2]
    simp [Matrix.one_apply, Fin.castSucc_inj]
  refine ⟨k, hk, ⟨S, hSu⟩, ?_⟩
  have hu : uEmb r E ⟨S, hSu⟩ = h := Subtype.ext hS.symm
  rw [hu, hh, mul_inv_cancel_left]

end Main

end GlobalTheory.JR.Step

theorem GlobalTheory.JR.Step.actU_liftH_mem_uO_mul_uEmb : ∀ {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] {r : ℕ} (X : Hn r F E) (ν : E) (l : F), ‖ν‖ = 1 → ∀ g : Matrix.unitaryGroup (Fin (r + 1)) E, unitU (r + 1) F E (actU g (GlobalTheory.JR.Step.liftH X ν l)) ≠ 0 → ∃ k ∈ uO (r + 1) E, ∃ s, g = k * GlobalTheory.JR.Step.uEmb r E s :=
  fun X ν l hν g hg => GlobalTheory.JR.Step.actU_liftH_support X ν l hν g hg
