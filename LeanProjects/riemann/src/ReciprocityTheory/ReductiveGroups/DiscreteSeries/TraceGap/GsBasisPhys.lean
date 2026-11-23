import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.FockWeights

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.TRGap

variable {n : ℕ}

def sModes (ε : Fin n → Bool) : Finset (Fin n × Fin n) :=
  univ.filter fun x : Fin n × Fin n => ε x.1 = true ∧ ε x.2 = false ∧ x.2 < x.1

def sDeg (ε : Fin n → Bool) : ℕ := (sModes ε).card

def sIdx (ε : Fin n → Bool) : Finset (Fin (n * n)) := (sModes ε).map finProdFinEquiv.toEmbedding

theorem gs_perm_prod {l1 l2 : List (Fin n × Fin n)} (h : l1.Perm l2) :
    ∃ σ : ℂ, (σ = 1 ∨ σ = -1) ∧ (l1.map fun x => ExteriorAlgebra.ι ℂ (Pi.single x (1 : ℂ))).prod =
      σ • (l2.map fun x => ExteriorAlgebra.ι ℂ (Pi.single x (1 : ℂ))).prod := by
  induction h with
  | nil => exact ⟨1, Or.inl rfl, by simp⟩
  | cons x _ ih =>
    obtain ⟨σ, hσ, e⟩ := ih
    exact ⟨σ, hσ, by simp only [List.map_cons, List.prod_cons, e, mul_smul_comm]⟩
  | swap x y l =>
    refine ⟨-1, Or.inr rfl, ?_⟩
    simp only [List.map_cons, List.prod_cons, ← mul_assoc]
    rw [eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap _ _), neg_mul, neg_one_smul]
  | trans _ _ ih1 ih2 =>
    obtain ⟨σ1, h1, e1⟩ := ih1
    obtain ⟨σ2, h2, e2⟩ := ih2
    refine ⟨σ1 * σ2, ?_, by rw [e1, e2, smul_smul]⟩
    rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl <;> norm_num

theorem sIdx_eq (ε : Fin n → Bool) : sIdx ε = (lowerWedgeAlt ε).1 := by
  ext m
  obtain ⟨x, rfl⟩ := finProdFinEquiv.surjective m
  rw [mem_lowerWedge_iff]
  simp [sIdx, sModes]

theorem gs_basis_phys {ε : Fin n → Bool} {S : Finset (Fin (n * n))} (hS : S ⊆ lfPhysModes ε) :
    fockBasis n S ∈ physFock ε := by
  simp only [physFock, Submodule.mem_iInf, LinearMap.mem_ker]
  intro i a hia
  exact lf_cm_basis_of_not_mem (x := (i, a)) fun h => hia ((lf_mem_phys ε i a).1 (hS h))

theorem gs_basis_deg (S : Finset (Fin (n * n))) : fockBasis n S ∈ ⋀[ℂ]^S.card (Fin n × Fin n → ℂ) := by
  have hb : fockBasis n S = ExteriorAlgebra.ιMulti ℂ S.card
      (((Pi.basisFun ℂ (Fin n × Fin n)).reindex finProdFinEquiv) ∘ S.orderEmbOfFin rfl) := by
    rw [fockBasis, ExteriorAlgebra.basis_apply]
    rfl
  rw [hb]
  exact ExteriorAlgebra.ιMulti_range ℂ S.card ⟨_, rfl⟩

theorem sVec_eq_basis (ε : Fin n → Bool) : ∃ c : ℂ, c ≠ 0 ∧ sVec ε = c • fockBasis n (sIdx ε) := by
  have hp : (sModes ε).toList.Perm
      (List.ofFn fun i => finProdFinEquiv.symm ((sIdx ε).orderEmbOfFin rfl i)) := by
    apply List.perm_of_nodup_nodup_toFinset_eq (Finset.nodup_toList _)
    · rw [List.nodup_ofFn]
      intro i j h
      exact ((sIdx ε).orderEmbOfFin rfl).injective (finProdFinEquiv.symm.injective h)
    · ext y
      rw [List.mem_toFinset, List.mem_toFinset, Finset.mem_toList, List.mem_ofFn]
      constructor
      · intro hy
        have hm : finProdFinEquiv y ∈ sIdx ε := Finset.mem_map_of_mem _ hy
        have hr : finProdFinEquiv y ∈ Set.range ((sIdx ε).orderEmbOfFin rfl) := by
          rw [Finset.range_orderEmbOfFin]
          exact hm
        obtain ⟨i, hi⟩ := hr
        exact ⟨i, by rw [hi]; simp⟩
      · rintro ⟨i, rfl⟩
        have hm := (sIdx ε).orderEmbOfFin_mem rfl i
        obtain ⟨a, ha, hae⟩ := Finset.mem_map.1 hm
        rw [← hae]
        simpa using ha
  obtain ⟨σ, hσ, e⟩ := gs_perm_prod hp
  refine ⟨σ, by rcases hσ with rfl | rfl <;> norm_num, ?_⟩
  rw [lfa_basis_list]
  exact e

theorem tr_sVec_props (ε : Fin n → Bool) :
    sVec ε ∈ physFock ε ∧ sVec ε ≠ 0 ∧
      (∀ a, sgE ε cpFock cmFock a a (sVec ε) = (((rhoHol ε - rhoN ε) a : ℝ) : ℂ) • sVec ε) ∧
      ∀ a b, b < a → ε a = ε b → sgE ε cpFock cmFock a b (sVec ε) = 0 := by
  obtain ⟨c, hc, e⟩ := sVec_eq_basis ε
  rw [e, sIdx_eq]
  refine ⟨Submodule.smul_mem _ _ (gs_basis_phys (lowerWedgeAlt ε).2),
    smul_ne_zero hc ((fockBasis n).ne_zero _), fun a => ?_, fun a b hba he => ?_⟩
  · rw [map_smul, lowerWedge_weight, smul_comm]
  · rw [map_smul, lowerWedge_killed_by_lowering ε hba he, smul_zero]

theorem sVec_deg (ε : Fin n → Bool) : sVec ε ∈ ⋀[ℂ]^(sDeg ε) (Fin n × Fin n → ℂ) := by
  obtain ⟨c, -, e⟩ := sVec_eq_basis ε
  rw [e]
  have h := gs_basis_deg (sIdx ε)
  rw [sIdx, Finset.card_map] at h
  exact Submodule.smul_mem _ _ h

theorem sDeg_eq_sum (ε : Fin n → Bool) :
    (sDeg ε : ℝ) = ∑ a ∈ plusIdx ε, (rhoHol ε - rhoN ε) a := by
  have h1 : ∀ a ∈ plusIdx ε, (rhoHol ε - rhoN ε) a =
      ((univ.filter fun b => ε b = false ∧ b < a).card : ℝ) := by
    intro a ha
    rw [lf_rhoHol_sub_rhoN, if_pos (by simpa [plusIdx] using ha)]
  rw [Finset.sum_congr rfl h1]
  unfold sDeg sModes
  simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, plusIdx,
    Finset.sum_filter]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : ε i = true <;> simp [hi]

end ReciprocityTheory.ChartRestriction.DS.TRGap
