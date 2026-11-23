import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.SatPowNonvan
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsStrictDom
open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct
open scoped Pointwise

noncomputable section

namespace GlobalTheory.CompanionTheory.SatPow

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n : ℕ}

theorem latK_mulVec {M : Matrix (Fin n) (Fin n) L} (h1 : ∀ i j, Valued.v (M i j) ≤ 1)
    (h2 : ∀ i j, j < i → Valued.v (M i j) < 1) (k : ℕ) {x : Fin n → L} (hx : x ∈ latK L n k) :
    M.mulVec x ∈ latK L n k := by
  have hx1 : ∀ j, Valued.v (x j) ≤ 1 := fun j => by
    have := hx j
    split_ifs at this with h
    · exact this
    · exact this.le
  intro i
  show if i.val < k then Valued.v ((M.mulVec x) i) ≤ 1 else Valued.v ((M.mulVec x) i) < 1
  have e : (M.mulVec x) i = ∑ j, M i j * x j := rfl
  rw [e]
  split_ifs with hik
  · refine Valuation.map_sum_le _ fun j _ => ?_
    rw [map_mul]
    exact (mul_le_of_le_one_right' (hx1 j)).trans (h1 i j)
  · refine Valuation.map_sum_lt _ one_ne_zero fun j _ => ?_
    rw [map_mul]
    by_cases hjk : j.val < k
    · have hji : j < i := by
        rw [Fin.lt_def]; omega
      exact (mul_le_of_le_one_right' (hx1 j)).trans_lt (h2 i j hji)
    · have := hx j
      rw [if_neg hjk] at this
      exact (mul_le_of_le_one_left' (h1 i j)).trans_lt this

theorem mem_iwU_iff (hσv : ∀ x, Valued.v (σ x) = Valued.v x) (g : GU σ n) :
    g ∈ IwU σ n ↔ (∀ i j, Valued.v (((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j) ≤ 1) ∧
      ∀ i j, j < i → Valued.v (((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j) < 1 := by
  constructor
  · intro hg
    have hg' : (g : GL (Fin n) L) ∈ IwGL L n := hg
    refine ⟨fun i j => GlobalTheory.CompanionTheory.KUFactsU.iwGL_entries hg' i j, fun i j hji => ?_⟩
    have h := (Subgroup.mem_iInf.1 hg') ⟨i.val, by omega⟩
    have hs : (Matrix.GeneralLinearGroup.toLin (g : GL (Fin n) L)) • latK L n i.val = latK L n i.val := h
    have he : (Pi.single j (1 : L) : Fin n → L) ∈ latK L n i.val := by
      intro k
      by_cases hk : k = j
      · subst hk
        have : k.val < i.val := hji
        simp [this]
      · have : (Pi.single j (1 : L) : Fin n → L) k = 0 := Pi.single_eq_of_ne hk _
        rw [this]
        split_ifs <;> simp
    have hm := Set.smul_mem_smul_set (a := Matrix.GeneralLinearGroup.toLin (g : GL (Fin n) L)) he
    rw [hs] at hm
    have hi := hm i
    rw [if_neg (lt_irrefl _)] at hi
    have e : ((Matrix.GeneralLinearGroup.toLin (g : GL (Fin n) L)) • (Pi.single j (1 : L) : Fin n → L)) i =
        ((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j := by
      show (Matrix.mulVec ((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (Pi.single j (1 : L) : Fin n → L)) i = _
      simp
    rwa [e] at hi
  · rintro ⟨h1, h2⟩
    have hinv := (GlobalTheory.LGrp.mem_GU_iff σ n (g : GL (Fin n) L)).1 g.2
    have h1' : ∀ i j, Valued.v (((g : GL (Fin n) L)⁻¹).val i j) ≤ 1 := fun i j => by
      rw [hinv, hσv]; exact h1 _ _
    have h2' : ∀ i j, j < i → Valued.v (((g : GL (Fin n) L)⁻¹).val i j) < 1 := fun i j hji => by
      rw [hinv, hσv]; exact h2 _ _ (Fin.rev_lt_rev.2 hji)
    show (g : GL (Fin n) L) ∈ IwGL L n
    refine Subgroup.mem_iInf.2 fun k => ?_
    show (Matrix.GeneralLinearGroup.toLin (g : GL (Fin n) L)) • latK L n k = latK L n k
    refine Set.Subset.antisymm ?_ fun x hx => ?_
    · rintro _ ⟨y, hy, rfl⟩
      exact latK_mulVec h1 h2 k hy
    · refine ⟨((g : GL (Fin n) L)⁻¹).val.mulVec x, latK_mulVec h1' h2' k hx, ?_⟩
      show ((g : GL (Fin n) L)).val.mulVec (((g : GL (Fin n) L)⁻¹).val.mulVec x) = x
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

theorem iwU_diag (hσv : ∀ x, Valued.v (σ x) = Valued.v x) {g : GU σ n} (hg : g ∈ IwU σ n) (i : Fin n) :
    Valued.v (((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i) = 1 := by
  classical
  obtain ⟨h1, h2⟩ := (mem_iwU_iff hσv g).1 hg
  obtain ⟨k1, k2⟩ := (mem_iwU_iff hσv g⁻¹).1 (inv_mem hg)
  have hprod : (((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
      (((g⁻¹ : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) i i = 1 := by
    rw [← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel]; simp
  rw [Matrix.mul_apply, ← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at hprod
  have hrest : Valued.v (∑ j ∈ Finset.univ.erase i, ((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j *
      (((g⁻¹ : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) j i) < 1 := by
    refine Valuation.map_sum_lt _ one_ne_zero fun j hj => ?_
    rw [map_mul]
    rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase hj) with hji | hji
    · exact (mul_le_of_le_one_right' (k1 j i)).trans_lt (h2 i j hji)
    · exact (mul_le_of_le_one_left' (h1 i j)).trans_lt (k2 j i hji)
  have hmain : Valued.v (((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i *
      (((g⁻¹ : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i) = 1 := by
    have e : ((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i *
        (((g⁻¹ : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i =
        1 - ∑ j ∈ Finset.univ.erase i, ((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j *
          (((g⁻¹ : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) j i := by
      rw [← hprod]; ring
    rw [e, Valuation.map_sub_eq_of_lt_left _ (by simpa using hrest), map_one]
  rw [map_mul] at hmain
  refine le_antisymm (h1 i i) ?_
  calc (1 : WithZero (Multiplicative ℤ)) = _ := hmain.symm
    _ ≤ _ := mul_le_of_le_one_right' (k1 i i)

end GlobalTheory.CompanionTheory.SatPow

end
