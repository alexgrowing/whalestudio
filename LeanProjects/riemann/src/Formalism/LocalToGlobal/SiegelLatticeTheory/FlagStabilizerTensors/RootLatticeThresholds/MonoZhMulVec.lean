import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RowLast

noncomputable section

open Matrix

namespace Formalism.L2.S.L6.UnitaryStandardVectors

open Formalism.L2.SG.HidaSetting

variable {N r : ℕ} (ε : Fin N → Bool) (F G : Fin (r + 1) → Fin N → ℂ) (T T' : ℝ) (π : Fin (r + 1) → Fin (r + 1))
  (blk : Fin (r + 1) → ℕ)
  (hFF : ∀ a b, hJ ε (F a) (F b) = lastDiag (-(T : ℂ)) a b)
  (hGG : ∀ a b, hJ ε (G a) (G b) = lastDiag (-(T' : ℂ)) a b)
  (hπ : ∀ a, π (π a) = a) (hblk : ∀ a, blk (π a) = blk a) (hanti : ∀ a b, blk a = blk b → a < b → π b < π a)
  (hZ : ∀ c b, Zm ε F G c b ≠ 0 ↔ c = π b)
  (hgap : 1 - (T : ℂ) * T' * ((Zm ε F G)⁻¹ (Fin.last r) (Fin.last r) *
    starRingEnd ℂ ((Zm ε F G)⁻¹ (Fin.last r) (Fin.last r))) ≠ 0)

def kap (x : Fin N → ℂ) : Fin (r + 1) ⊕ Fin (r + 1) → ℂ :=
  ((Wfg F G)ᴴ * Formalism.REAL.Jm ε * Wfg F G)⁻¹ *ᵥ (((Wfg F G)ᴴ * Formalism.REAL.Jm ε) *ᵥ x)

include hFF hGG hπ hZ hgap in
theorem kap_eq (x : Fin N → ℂ) :
    Matrix.fromBlocks (lastDiag (-(T : ℂ))) (Zm ε F G) (Zm ε F G)ᴴ (lastDiag (-(T' : ℂ))) *ᵥ kap ε F G x =
      Sum.elim (fun a => hJ ε (F a) x) (fun b => hJ ε (G b) x) := by
  rw [← gram_eq ε F G T T' π hFF hGG hπ hZ, kap, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ (gram_unit ε F G T T' π hFF hGG hπ hZ hgap), Matrix.one_mulVec, wjx]

theorem Yc_sub (C : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (x : Fin N → ℂ) :
    Yc ε F G C *ᵥ x - x = ∑ a, ((Am ε F G C - 1) *ᵥ (kap ε F G x ∘ Sum.inl)) a • F a +
      ∑ b, ((C - 1) *ᵥ (kap ε F G x ∘ Sum.inr)) b • G b := by
  unfold Yc
  rw [Ymat_sub, Wfg_mulVec]
  unfold Mm
  rw [Matrix.fromBlocks_mulVec]
  simp [kap]

include hπ hZ in
theorem monoZ_mulVec (v : Fin (r + 1) → ℂ) (a : Fin (r + 1)) : (Zm ε F G *ᵥ v) a = Zm ε F G a (π a) * v (π a) := by
  rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single (π a)]
  · intro j _ hj
    have : Zm ε F G a j = 0 := by by_contra h; exact hj (by rw [(hZ a j).1 h, hπ])
    rw [this, zero_mul]
  · simp

include hπ hZ in
theorem monoZh_mulVec (v : Fin (r + 1) → ℂ) (b : Fin (r + 1)) :
    ((Zm ε F G)ᴴ *ᵥ v) b = starRingEnd ℂ (Zm ε F G (π b) b) * v (π b) := by
  rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single (π b)]
  · simp [Matrix.conjTranspose_apply]
  · intro j _ hj
    have : Zm ε F G j b = 0 := by by_contra h; exact hj ((hZ j b).1 h)
    simp [Matrix.conjTranspose_apply, this]
  · simp

include hFF hGG hπ hblk hanti hZ hgap in
theorem Yc_perpF {C : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (hC : IsUB blk C) (x : Fin N → ℂ)
    (hx : ∀ a, a ≠ Fin.last r → hJ ε (F a) x = 0) :
    Yc ε F G C *ᵥ x - x ∈ Submodule.span ℂ (F '' {a | a ≠ Fin.last r}) := by
  have hk := kap_eq ε F G T T' π hFF hGG hπ hZ hgap x
  rw [Matrix.fromBlocks_mulVec] at hk
  set κ := kap ε F G x
  have hG0 : ∀ j, j ≠ π (Fin.last r) → κ (Sum.inr j) = 0 := by
    intro j hj
    have ha : π j ≠ Fin.last r := fun h => hj (by rw [← h, hπ])
    have h1 := congrFun hk (Sum.inl (π j))
    simp only [Sum.elim_inl, Pi.add_apply] at h1
    rw [hx _ ha, lastDiag_mulVec, Pi.single_apply, if_neg ha, zero_add, monoZ_mulVec ε F G π hπ hZ, hπ] at h1
    have hz : Zm ε F G (π j) j ≠ 0 := (hZ _ _).2 rfl
    exact (mul_eq_zero.1 h1).resolve_left hz
  rw [Yc_sub]
  have h2 : ∑ b, ((C - 1) *ᵥ (κ ∘ Sum.inr)) b • G b = 0 := by
    refine Finset.sum_eq_zero fun b _ => ?_
    have : ((C - 1) *ᵥ (κ ∘ Sum.inr)) b = 0 := by
      rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single (π (Fin.last r))]
      · rw [Matrix.sub_apply, colMin π blk hπ hblk hanti hC, Matrix.one_apply]
        split_ifs <;> simp
      · intro j _ hj; simp [hG0 j hj]
      · simp
    rw [this, zero_smul]
  rw [h2, add_zero]
  refine Submodule.sum_mem _ fun a _ => ?_
  by_cases ha : a = Fin.last r
  · subst ha
    have : ((Am ε F G C - 1) *ᵥ (κ ∘ Sum.inl)) (Fin.last r) = 0 := by
      rw [Matrix.mulVec, dotProduct]
      refine Finset.sum_eq_zero fun k _ => ?_
      have hA : IsUB blk (Am ε F G C) := isUB_A π hπ hblk hanti _ hZ hC
      rw [Matrix.sub_apply, rowLast blk hA, Matrix.one_apply]
      by_cases hk : k = Fin.last r
      · subst hk; simp
      · simp [hk, Ne.symm hk]
    rw [this, zero_smul]; exact Submodule.zero_mem _
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, ha, rfl⟩)

include hFF hGG hπ hblk hanti hZ hgap in
theorem Yc_perpG {C : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (hC : IsUB blk C) (x : Fin N → ℂ)
    (hx : ∀ b, b ≠ Fin.last r → hJ ε (G b) x = 0) :
    Yc ε F G C *ᵥ x - x ∈ Submodule.span ℂ (G '' {b | b ≠ Fin.last r}) := by
  have hk := kap_eq ε F G T T' π hFF hGG hπ hZ hgap x
  rw [Matrix.fromBlocks_mulVec] at hk
  set κ := kap ε F G x
  have hF0 : ∀ i, i ≠ π (Fin.last r) → κ (Sum.inl i) = 0 := by
    intro i hi
    have hb : π i ≠ Fin.last r := fun h => hi (by rw [← h, hπ])
    have h1 := congrFun hk (Sum.inr (π i))
    simp only [Sum.elim_inr, Pi.add_apply] at h1
    rw [hx _ hb, lastDiag_mulVec, Pi.single_apply, if_neg hb, add_zero, monoZh_mulVec ε F G π hπ hZ, hπ] at h1
    have hz : starRingEnd ℂ (Zm ε F G i (π i)) ≠ 0 := by
      rw [map_ne_zero]; exact (hZ _ _).2 (hπ i).symm
    exact (mul_eq_zero.1 h1).resolve_left hz
  rw [Yc_sub]
  have hA : IsUB blk (Am ε F G C) := isUB_A π hπ hblk hanti _ hZ hC
  have h2 : ∑ a, ((Am ε F G C - 1) *ᵥ (κ ∘ Sum.inl)) a • F a = 0 := by
    refine Finset.sum_eq_zero fun a _ => ?_
    have : ((Am ε F G C - 1) *ᵥ (κ ∘ Sum.inl)) a = 0 := by
      rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single (π (Fin.last r))]
      · rw [Matrix.sub_apply, colMin π blk hπ hblk hanti hA, Matrix.one_apply]
        split_ifs <;> simp
      · intro j _ hj; simp [hF0 j hj]
      · simp
    rw [this, zero_smul]
  rw [h2, zero_add]
  refine Submodule.sum_mem _ fun b _ => ?_
  by_cases hb : b = Fin.last r
  · subst hb
    have : ((C - 1) *ᵥ (κ ∘ Sum.inr)) (Fin.last r) = 0 := by
      rw [Matrix.mulVec, dotProduct]
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [Matrix.sub_apply, rowLast blk hC, Matrix.one_apply]
      by_cases hk : k = Fin.last r
      · subst hk; simp
      · simp [hk, Ne.symm hk]
    rw [this, zero_smul]; exact Submodule.zero_mem _
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, hb, rfl⟩)

end Formalism.L2.S.L6.UnitaryStandardVectors
