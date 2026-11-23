import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.TopCompB
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.TopCompC
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.TCCalc
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.TCBlock

noncomputable section

open Matrix
open scoped ContDiff Topology

namespace PositivityTheory.Rg.Sw.LVs.TC

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem detD_affine (hA : IterAffine) {F : M2 n → ℂ} {Ω : Set (M2 n)} (hΩ : IsOpen Ω) (hF : ContDiffOn ℂ ∞ F Ω)
    {g : M2 n} (hg : g ∈ Ω) (L : Matrix (Fin n) (Fin n) ℂ →L[ℂ] M2 n) :
    detD (fun t => F (g + L t)) = ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℂ) *
      iteratedFDeriv ℂ (Fintype.card (Fin n)) F g (fun i => L (single ((Fintype.equivFin (Fin n)).symm i)
        (σ ((Fintype.equivFin (Fin n)).symm i)) 1)) := by
  unfold detD
  refine Finset.sum_congr rfl fun σ _ => ?_
  erw [hA (M2 n) (Matrix (Fin n) (Fin n) ℂ) F Ω hΩ hF g hg L]
  rfl

theorem top_zero (hA : IterAffine) {j : ℕ} {F : M2 n → ℂ} {Ω : Set (M2 n)} (hΩ : IsOpen Ω) (hG : GSet n ⊆ Ω)
    (hF : ContDiffOn ℂ ∞ F Ω) (hhyp : ∀ a b, InG a → InG b → detD (fun H => F (a * nU H * b)) = 0)
    {g : M2 n} (hg : InG g) : detD (fun t => F (g + topL g j t)) = 0 := by
  have hgΩ : g ∈ Ω := hG hg
  have key : ∀ θ : ℝ, ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℂ) *
      iteratedFDeriv ℂ (Fintype.card (Fin n)) F g (fun i => rotL g j θ
        (single ((Fintype.equivFin (Fin n)).symm i) (σ ((Fintype.equivFin (Fin n)).symm i)) 1)) = 0 := by
    intro θ
    have h0 := hhyp (g * rot j θ) (rot j θ)⁻¹ (TC.inG_mul hg (rot_inG j θ)) (inG_inv (rot_inG j θ))
    simp only [rot_nU] at h0
    rwa [detD_affine hA hΩ hF hgΩ] at h0
  rw [detD_affine hA hΩ hF hgΩ]
  simp only [topL_single]
  have hv := top_vanish (iteratedFDeriv ℂ (Fintype.card (Fin n)) F g)
    (fun σ : Equiv.Perm (Fin n) => (Equiv.Perm.sign σ : ℂ))
    (fun σ i m => g * (Cm n * (![zLow j, zMid j, zTop j] m) ((Fintype.equivFin (Fin n)).symm i)
      (σ ((Fintype.equivFin (Fin n)).symm i)) * CmI n)) ?_
  · simpa using hv
  intro θ
  have h1 : ∀ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℂ) *
      iteratedFDeriv ℂ (Fintype.card (Fin n)) F g (fun i =>
        g * (Cm n * zLow j ((Fintype.equivFin (Fin n)).symm i) (σ ((Fintype.equivFin (Fin n)).symm i)) * CmI n)
        + Complex.exp (2 * ↑θ * Complex.I) • (g * (Cm n * zMid j ((Fintype.equivFin (Fin n)).symm i)
          (σ ((Fintype.equivFin (Fin n)).symm i)) * CmI n))
        + Complex.exp (2 * ↑θ * Complex.I) ^ 2 • (g * (Cm n * zTop j ((Fintype.equivFin (Fin n)).symm i)
          (σ ((Fintype.equivFin (Fin n)).symm i)) * CmI n)))
      = Complex.exp (2 * ↑θ * Complex.I) ^ Fintype.card (Fin n) * ((Equiv.Perm.sign σ : ℂ) *
        iteratedFDeriv ℂ (Fintype.card (Fin n)) F g (fun i => rotL g j θ
          (single ((Fintype.equivFin (Fin n)).symm i) (σ ((Fintype.equivFin (Fin n)).symm i)) 1))) := by
    intro σ
    simp_rw [← rotL_single]
    rw [ContinuousMultilinearMap.map_smul_univ, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul]
    ring
  refine (Finset.sum_congr rfl fun σ _ => h1 σ).trans ?_
  rw [← Finset.mul_sum, key θ, mul_zero]

theorem block_part_embedding_first (j : ℕ) (T : Matrix (blkA (n := n) j) (blkA j) ℂ) (S : Matrix (blkB (n := n) j) (blkB j) ℂ) :
    matrixBlockRestriction (blkA j) (blkA j) (embOn (blkA j) T + embOn (blkB j) S) = embOn (blkA j) T := by
  ext a b
  by_cases ha : a ∈ blkA j <;> by_cases hb : b ∈ blkA j <;>
    simp [matrixBlockRestriction, embOn, blkB, ha, hb]

theorem block_part_embedding_second (j : ℕ) (T : Matrix (blkA (n := n) j) (blkA j) ℂ) (S : Matrix (blkB (n := n) j) (blkB j) ℂ) :
    matrixBlockRestriction (blkB j) (blkB j) (embOn (blkA j) T + embOn (blkB j) S) = embOn (blkB j) S := by
  ext a b
  by_cases ha : a ∈ blkA j <;> by_cases hb : b ∈ blkA j <;>
    simp [matrixBlockRestriction, embOn, blkB, ha, hb]

theorem block_part_diagonal_first (j : ℕ) (c c' : ℂ) (t : Matrix (Fin n) (Fin n) ℂ) :
    matrixBlockRestriction (blkA j) (blkA j) (bdiag j c c' t) = c • matrixBlockRestriction (blkA j) (blkA j) t := by
  ext a b
  by_cases ha : a ∈ blkA j <;> by_cases hb : b ∈ blkA j <;>
    simp [matrixBlockRestriction, bdiag, blkB, ha, hb]

theorem block_part_diagonal_second (j : ℕ) (c c' : ℂ) (t : Matrix (Fin n) (Fin n) ℂ) :
    matrixBlockRestriction (blkB j) (blkB j) (bdiag j c c' t) = c' • matrixBlockRestriction (blkB j) (blkB j) t := by
  ext a b
  by_cases ha : a ∈ blkA j <;> by_cases hb : b ∈ blkA j <;>
    simp [matrixBlockRestriction, bdiag, blkB, ha, hb]

theorem g_mX (g : M2 n) (P Q R S : Matrix (Fin n) (Fin n) ℂ) :
    g * mX (1 + P) Q R (1 + S) = g + g * (Cm n * fromBlocks P Q R S * CmI n) := by
  have h : fromBlocks (1 + P) Q R (1 + S) = (1 : M2 n) + fromBlocks P Q R S := by
    rw [← fromBlocks_one, fromBlocks_add]
    simp
  simp only [mX, cm_inv, h, mul_add, add_mul, mul_one, cm_mul_cmI]

theorem supp_smul {s t : Finset (Fin n)} (c : ℂ) (x : Matrix (Fin n) (Fin n) ℂ) :
    ∀ a b, (c • matrixBlockRestriction s t x) a b ≠ 0 → a ∈ s ∧ b ∈ t := by
  intro a b h
  by_contra hn
  apply h
  simp only [Matrix.smul_apply, matrixBlockRestriction, if_neg hn, smul_zero]

private theorem eq_mul_mX_mul_mX_blockEntries (g : M2 n) (j : ℕ) (t : Matrix (Fin n) (Fin n) ℂ) :
    g + topL g j t = g * mX 1 ((2 * Complex.I)⁻¹ • matrixBlockRestriction (blkA j) (blkA j) t)
      ((-(2 * Complex.I)⁻¹) • matrixBlockRestriction (blkB j) (blkB j) t) 1 *
      mX (1 + (2 * Complex.I)⁻¹ • matrixBlockRestriction (blkA j) (blkB j) t) 0 0
        (1 + (-(2 * Complex.I)⁻¹) • matrixBlockRestriction (blkB j) (blkA j) t) := by
  rw [mul_assoc, ← mX_factor j _ _ _ _ (supp_smul _ _) (supp_smul _ _) (supp_smul _ _) (supp_smul _ _), g_mX]
  simp only [topL, conjL_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.neg_apply, block_part_linear_apply,
    neg_smul]

private theorem conjL_bdiag_eq_mul_mX_blockEntries (g : M2 n) (j : ℕ) (t : Matrix (Fin n) (Fin n) ℂ) :
    g + conjL g 0 (matrixBlockRestrictionLinear (blkA j) (blkA j)) (matrixBlockRestrictionLinear (blkB j) (blkB j)) 0
      (bdiag j (2 * Complex.I)⁻¹ (-(2 * Complex.I)⁻¹) t) =
    g * mX 1 ((2 * Complex.I)⁻¹ • matrixBlockRestriction (blkA j) (blkA j) t)
      ((-(2 * Complex.I)⁻¹) • matrixBlockRestriction (blkB j) (blkB j) t) 1 := by
  have h := g_mX g 0 ((2 * Complex.I)⁻¹ • matrixBlockRestriction (blkA j) (blkA j) t)
    ((-(2 * Complex.I)⁻¹) • matrixBlockRestriction (blkB j) (blkB j) t) 0
  simp only [add_zero] at h
  rw [h, conjL_apply]
  simp only [ContinuousLinearMap.zero_apply, block_part_linear_apply, block_part_diagonal_first, block_part_diagonal_second]

private theorem comp_blockEntries_eq (g : M2 n) (j : ℕ) (T : Matrix (blkA (n := n) j) (blkA j) ℂ)
    (S : Matrix (blkB (n := n) j) (blkB j) ℂ) :
    g * mX 1 (embOn (blkA j) T) (embOn (blkB j) S) 1 =
      g + conjL g 0 (matrixBlockRestrictionLinear (blkA j) (blkA j)) (matrixBlockRestrictionLinear (blkB j) (blkB j)) 0
        (embOn (blkA j) T + embOn (blkB j) S) := by
  have h := g_mX g 0 (embOn (blkA j) T) (embOn (blkB j) S) 0
  simp only [add_zero] at h
  rw [h, conjL_apply]
  simp only [ContinuousLinearMap.zero_apply, block_part_linear_apply, block_part_embedding_first, block_part_embedding_second]

set_option maxHeartbeats 800000 in
theorem topComp_of (hA : IterAffine) (hB : DetDBlock) : TopComp := by
  intro n j F Ω hΩ hG hF hinv hhyp g hg
  have hgΩ : g ∈ Ω := hG hg
  have hc : (2 * Complex.I)⁻¹ ≠ 0 := by simp [Complex.I_ne_zero]
  have hLc : Continuous fun t : Matrix (Fin n) (Fin n) ℂ =>
      g + conjL g 0 (matrixBlockRestrictionLinear (blkA j) (blkA j)) (matrixBlockRestrictionLinear (blkB j) (blkB j)) 0 t :=
    continuous_const.add (ContinuousLinearMap.continuous _)
  have hΩ' : IsOpen ((fun t : Matrix (Fin n) (Fin n) ℂ =>
      g + conjL g 0 (matrixBlockRestrictionLinear (blkA j) (blkA j)) (matrixBlockRestrictionLinear (blkB j) (blkB j)) 0 t) ⁻¹' Ω) := hΩ.preimage hLc
  have h0 : (0 : Matrix (Fin n) (Fin n) ℂ) ∈ (fun t : Matrix (Fin n) (Fin n) ℂ =>
      g + conjL g 0 (matrixBlockRestrictionLinear (blkA j) (blkA j)) (matrixBlockRestrictionLinear (blkB j) (blkB j)) 0 t) ⁻¹' Ω := by
    simp only [Set.mem_preimage, map_zero, add_zero]
    exact hgΩ
  have hψ : ContDiffOn ℂ ∞ (fun t : Matrix (Fin n) (Fin n) ℂ =>
      F (g + conjL g 0 (matrixBlockRestrictionLinear (blkA j) (blkA j)) (matrixBlockRestrictionLinear (blkB j) (blkB j)) 0 t))
      ((fun t : Matrix (Fin n) (Fin n) ℂ =>
        g + conjL g 0 (matrixBlockRestrictionLinear (blkA j) (blkA j)) (matrixBlockRestrictionLinear (blkB j) (blkB j)) 0 t) ⁻¹' Ω) :=
    hF.comp (contDiff_const.add (ContinuousLinearMap.contDiff _)).contDiffOn (fun t ht => ht)
  have hmain := hB n j (2 * Complex.I)⁻¹ (-(2 * Complex.I)⁻¹) _ _ hΩ' h0 hψ
  have hzero : (detD fun t : Matrix (Fin n) (Fin n) ℂ =>
      F (g + conjL g 0 (matrixBlockRestrictionLinear (blkA j) (blkA j)) (matrixBlockRestrictionLinear (blkB j) (blkB j)) 0
        (bdiag j (2 * Complex.I)⁻¹ (-(2 * Complex.I)⁻¹) t))) = 0 := by
    refine Eq.trans ?_ (top_zero (j := j) hA hΩ hG hF hhyp hg)
    have hev : (fun t : Matrix (Fin n) (Fin n) ℂ =>
        F (g + conjL g 0 (matrixBlockRestrictionLinear (blkA j) (blkA j)) (matrixBlockRestrictionLinear (blkB j) (blkB j)) 0
          (bdiag j (2 * Complex.I)⁻¹ (-(2 * Complex.I)⁻¹) t))) =ᶠ[𝓝 0]
        fun t => F (g + topL g j t) := by
      have e1 : ∀ᶠ t in 𝓝 (0 : Matrix (Fin n) (Fin n) ℂ), g + topL g j t ∈ Ω :=
        (continuous_const.add (topL g j).continuous).continuousAt.preimage_mem_nhds
          (by simpa using hΩ.mem_nhds hgΩ)
      have hc2 : Continuous fun t : Matrix (Fin n) (Fin n) ℂ => g + conjL g 0 (matrixBlockRestrictionLinear (blkA j) (blkA j))
          (matrixBlockRestrictionLinear (blkB j) (blkB j)) 0 (bdL j (2 * Complex.I)⁻¹ (-(2 * Complex.I)⁻¹) t) :=
        continuous_const.add ((ContinuousLinearMap.continuous _).comp (ContinuousLinearMap.continuous _))
      have e2 : ∀ᶠ t in 𝓝 (0 : Matrix (Fin n) (Fin n) ℂ), g + conjL g 0 (matrixBlockRestrictionLinear (blkA j) (blkA j))
          (matrixBlockRestrictionLinear (blkB j) (blkB j)) 0 (bdL j (2 * Complex.I)⁻¹ (-(2 * Complex.I)⁻¹) t) ∈ Ω := by
        have hm : Ω ∈ 𝓝 (g + conjL g 0 (matrixBlockRestrictionLinear (blkA j) (blkA j))
            (matrixBlockRestrictionLinear (blkB j) (blkB j)) 0 (bdL j (2 * Complex.I)⁻¹ (-(2 * Complex.I)⁻¹) 0)) := by
          rw [map_zero, map_zero, add_zero]
          exact hΩ.mem_nhds hgΩ
        exact hc2.continuousAt.preimage_mem_nhds hm
      filter_upwards [e1, e2] with t ht1 ht2
      rw [bdL_apply, conjL_bdiag_eq_mul_mX_blockEntries] at ht2
      rw [eq_mul_mX_mul_mX_blockEntries] at ht1
      rw [conjL_bdiag_eq_mul_mX_blockEntries, eq_mul_mX_mul_mX_blockEntries]
      exact (hinv _ _ _ ht1 ht2 (supp_smul _ _) (supp_smul _ _)).symm
    have hI := (hev.iteratedFDeriv ℂ (Fintype.card (Fin n))).eq_of_nhds
    unfold detD
    rw [hI]
  rw [hzero] at hmain
  have hX := (mul_eq_zero.mp hmain.symm).resolve_left
    (mul_ne_zero (pow_ne_zero _ hc) (pow_ne_zero _ (neg_ne_zero.mpr hc)))
  simpa only [comp_blockEntries_eq] using hX

theorem topComp : TopComp := topComp_of iterAffine (detDBlock_of iterAffine iterSymm iterNested)

end PositivityTheory.Rg.Sw.LVs.TC

namespace PositivityTheory.Rg.Sw.LVs

theorem topComp : TopComp := TC.topComp

end PositivityTheory.Rg.Sw.LVs
